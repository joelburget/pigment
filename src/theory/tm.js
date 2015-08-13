// TODO:
// * user-defined types
// * source positions? how does this relate to names?
import { Var, Abs, Tm, Abt } from './abt';


type EvaluationResult<A>
  = { type: 'success', value: A }
  | { type: 'stuck', value: A }


export function mkSuccess(e: A): EvaluationResult<A> {
  return {
    type: 'success',
    value: e,
  };
}


export function mkStuck(e: A): EvaluationResult<A> {
  return {
    type: 'stuck',
    value: e,
  };
}


export class Expression {
  arity: [number];
  children: [ Abt<Expression> ];
  // map: (Abt<Expression> => Abt<Expression>) => Expression;
  // evaluate: Context => EvaluationResult<Expression>;
  // getType: Context => Expression

  constructor(children: [ Abt<Expression> ]): void {
    this.children = children;
  }
}


export class EVar extends Expression {
  static arity = [];

  constructor(name: string, type: Expression): void {
    super([ new Var(name) ]);
    this.type = type;
  }

  map(f): Expression {
    let v = new EVar(this.children[0].name);
    v.children = v.children.map(f);
    return v;
  }

  evaluate(ctx: Context): EvaluationResult<Expression> {
    return lookupValue(ctx, this.children[0].name).evaluate();
  }

  getType(ctx: Context) {
    return this.type;
  }
}


export class Type extends Expression {
  static arity = [];
  static singleton = new Type();

  constructor(): void {
    super([]);
  }

  map(f): Type {
    return this;
  }

  evaluate(ctx: Context): EvaluationResult<Expression> {
    return mkSuccess(this);
  }

  getType(ctx: Context) {
    return Type.singleton;
  }
}


export class Hole extends Expression {
  static arity = [];
  name: ?string;

  constructor(name: ?string, type: Expression): void {
    super([]);
    this.name = name;
    this.type = type;
  }

  map(f): Expression {
    return this;
  }

  evaluate(ctx: Context): EvaluationResult<Expression> {
    return mkStuck(this);
  }

  getType(ctx: Context) {
    return this.type;
  }
}
