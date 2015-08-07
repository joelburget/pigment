// TODO:
// * less ad-hoc binding
// * revolutionize type inference
// * sigma types
// * user-defined types
// * organize
// * source positions? how does this relate to names?
import Immutable from 'immutable';
const { Record, Map, List } = Immutable;
import keyMirror from 'keyMirror'


// TODO consider adding positions to Expression
export class Value {}

export class Pi extends Value {
  abs: Abstraction;

  constructor(abs: Abstraction) {
    super(arguments);
    this.abs = abs;
  }
}

export class Type extends Value {}
Type.singleton = new Type();

export class Lambda extends Value {
  abs: Abstraction;

  constructor(abs: Abstraction) {
    super(arguments);
    this.abs = abs;
  }
}

// XXX Neutral is also a Value

export class Neutral {}

export class Var extends Neutral {
  name: Variable;

  constructor(name: Variable) {
    super(arguments);
    this.name = name;
  }
}

export class App extends Neutral {
  e1: Neutral;
  e2: Value;

  constructor(e1: Neutral, e2: Value) {
    super(arguments);
    this.e1 = e1;
    this.e2 = e2;
  }
}

export class Abstraction {
  variable: Variable;
  type: Value;
  expr: Expression; // XXX

  constructor(variable: Variable, type: Expression, expr: Expression) {
    this.variable = variable;
    this.type = type;
    this.expr = expr;
  }
}


export const Variable = Record({
  str: null,
  num: null,
});

export function varString(str: string) {
  return new Variable({ str });
}

export function gensym(str: string, num: number) {
  return new Variable({ str, num });
}

export function dummy() {
  return new Variable({ str: '_' });
}

// generate a fresh variable name
// TODO I'm sure this doesn't yet match the original intent but it's getting
// closer!
export function refresh(x: Variable): Variable {
  let k = 0;

  // XXX
  function gensym_(name: string) {
    k += 1;

    return gensym(name, k)
  };

  return gensym_(x.str);
}


type Context = Map<Variable, [Expression, ?Expression]>;


// substitute expressions for variables (from s) in v
export function subst(s: Context, v: Expression): Expression {

  if (v instanceof Var) {
    return s.has(v.name) ? s.get(v.name) : v;

  } else if (v instanceof Type) {
    return v;

  } else if (v instanceof Pi) {
    return new Pi(substAbstraction(s, v.abs));

  } else if (v instanceof Lambda) {
    return new Lambda(substAbstraction(s, v.abs));

  } else { // if (v instanceof App) {
    return new App(subst(s, v.e1), subst(s, v.e2));
  }

}

// XXX this mapping is wrong. should map variable to its type and possibly value
export function substAbstraction(s: Context, abstr: Abstraction): Abstraction {
  const x_ = refresh(abstr.variable);
  const s_ = s.push([x, new Expression({type: expressionType.VAR, value: x_})]);

  return new Abstraction(
    x_, // variable
    subst(s, abstr.type), // type
    subst(s_, abstr.expr) // expr
  );
}

// find the type of x in ctx
// TODO not found error
export function lookupTy(x: Variable, ctx: Context): Expression {
  return ctx.get(x)[0];
}


export function lookupValue(x: Variable, ctx: Context): ?Expression {
  return ctx.get(x)[1];
}


export function extend(x: Variable,
                       t: Expression,
                       value: ?Expression,
                       ctx: Context): Context {
  return ctx.set(x, [t, value]);
}


export function inferType(ctx: Context, expr: Expression): Expression {
  if (expr instanceof Var) {
    return lookupTy(expr.name, ctx);

  } else if (expr instanceof Pi) {
    // man, this is easier than inferring a universe
    return Type.singleton;

  } else if (expr instanceof Type) {
    return Type.singleton;

  } else if (expr instanceof Lambda) {
    const { variable: x, type: t, expr: e } = expr.abs
    const te = inferType(extend(x, t, null, ctx), e);

    return new Pi(new Abstraction(x, t, te));

  } else { // (expr instanceof App) {
    const { e1, e2 } = expr;
    const { variable: x, type: s, expr: t } = inferPi(ctx, e1).abs;
    const te = inferType(ctx, e2);
    if (!checkEqual(ctx, s, te)) {
      throw new Error(s, te, "not equal");
    }

    return subst(List.of([[x, e2]]), t);
  }
}


// infer the type of e in ctx and verify it's a pi
export function inferPi(ctx: Context, e: Expression): Pi {
  const t = inferType(ctx, e);
  const normalized = normalize(ctx, t);

  if (normalized instanceof Pi) {
    return normalized;
  } else {
    throw new Error("type expected");
  }
}


// normalize the given expression in context
// - beta-reduction
// - definition unfolding
export function normalize(ctx: Context, e: Expression) {
  if (e instanceof Var) {
    const val = lookupValue(e.name, ctx);
    if (val) {
      return normalize(ctx, val);
    } else {
      return e;
    }

  } else if (e instanceof Pi) {
    return new Pi(normalizeAbstraction(ctx, e.abs));

  } else if (e instanceof Type) {
    return e;

  } else if (e instanceof Lambda) {
    return new Lambda(normalizeAbstraction(ctx, e.abs));

  } else if (e instanceof App) {
    const { e1, e2 } = e;
    const e1_ = normalize(ctx, e1);
    const e2_ = normalize(ctx, e2);

    if (e1_ instanceof Lambda) {
      const { variable: x, type: t, expr: e1__ } = e1_.abs;
      const ctx_ = List.of([[x, e2_]]);
      return normalize(ctx, subst(ctx_, e1__));
    } else {
      return new App(e1, e2);
    }
  }

}


export function normalizeAbstraction(ctx: Context,
                                     abs: Abstraction): Abstraction {
  let { variable, type, expr } = abs;
  type = normalize(ctx, type);

  return new Abstraction(
    variable,
    type,
    normalize(extend(variable, type, null, ctx), expr)
  );
}


export function equal(ctx: Context, e1_: Expression, e2_: Expression) {
  const e1 = normalize(ctx, e1_);
  const e2 = normalize(ctx, e2_);

  if (e1 instanceof Var && e2 instanceof Var) {
    return Immutable.is(e1.name, e2.name);

  } else if (e1 instanceof Pi && e2 instanceof Pi) {
    return equalAbstraction(ctx, e1.abs, e2.abs);

  } else if (e1 instanceof Type && e2 instanceof Type) {
    return true;

  } else if (e1 instanceof Lambda && e2 instanceof Lambda) {
    return equalAbstraction(ctx, e1.abs, e2.abs);

  } else if (e1 instanceof App && e2 instanceof App) {
    const { e1: e11, e2: e12 } = e1;
    const { e1: e21, e2: e22 } = e2;

    return equal(ctx, e11, e21) && equal(ctx, e12, e22);

  } else {
    return false;
  }
}

export function equalAbstraction(ctx: Context,
                                 abs1: Abstraction,
                                 abs2: Abstraction): boolean {
  const { variable: x, type: t1, expr: e1 } = abs1;
  const { variable: y, type: t2, expr: e2 } = abs2;

  // Make both bound variables the same in the comparison of abstractions
  const ctx_ = List.of([[y, x]]);

  return equal(ctx, t1, t2) &&
         equal(ctx, e1, subst(ctx_, e2));
}
