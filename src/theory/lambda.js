// @flow
import { Expression, Type } from './tm';
import { mkStuck, mkSuccess, bind } from './evaluation';
import type { EvaluationResult } from './evaluation';
import { Var, Abs, Tm, AbtBase } from './abt';
import { lookup, add } from './context';
import type { Context } from './context';


export class Lam extends Expression {
  // $flowstatic
  static arity = [1];
  // $flowstatic
  static renderName = "lam";

  constructor(abt: AbtBase, type: Expression): void {
    // we can analyze the abt:
    // * Abs - indicates the lambda is binding
    // * Var, Tm - the lambda is constant
    super([ abt ], type);
  }

  map1(f: (x: AbtBase) => AbtBase): Lam {
    // XXX we don't know the type here!
    return new Lam(f(this.children[0]), this.type);
  }

  evaluate(ctx: Context, x: Expression): EvaluationResult<Expression> {
    var [ child ] = this.children;

    if (child instanceof Var) {
      return mkSuccess(lookup(ctx, child.name));

    } else if (child instanceof Abs) {
      return child
        .subst(new Tm(x), child.name)
        .body
        .evaluate(ctx);

    } else if (child instanceof Tm) {
      return child.value.evaluate(ctx);
    }
  }
}


export class Arr extends Expression {
  // $flowstatic
  static arity = [0, 0];
  // $flowstatic
  static renderName = "arr";

  constructor(domain: Expression, codomain: Expression): void {
    super([ new Tm(domain), new Tm(codomain) ], Type.singleton);
  }

  domain(): Expression {
    var domain = this.children[0];
    if (domain instanceof Tm) {
      return domain.value;
    } else {
      throw new Error('TODO - non-Tm domain');
    }
  }

  codomain(): Expression {
    var codomain = this.children[1];
    if (codomain instanceof Tm) {
      return codomain.value;
    } else {
      throw new Error('TODO - non-Tm codomain');
    }
  }

  map(f: (x: AbtBase) => AbtBase): Arr {
    return new Arr(f(this.domain()), f(this.codomain()));
  }

  evaluate(ctx: Context): EvaluationResult<Expression> {
    throw new Error("TODO - Arr.evaluate");
  }
}


export class App extends Expression {
  // $flowstatic
  static arity = [0, 0];
  // $flowstatic
  static renderName = "app";

  constructor(f: Expression, x: Expression): void {
    var fType = f.type;
    if (fType instanceof Arr) {
      var codomain = fType.codomain();
      super([ new Tm(f), new Tm(x) ], codomain);
    } else {
      throw new Error('runtime error in App constructor');
    }
  }

  func(): Expression {
    return this.children[0];
  }

  arg(): Expression {
    return this.children[1];
  }

  map(f: (x: AbtBase) => AbtBase): App {
    return new App(f(this.func()), f(this.arg()));
  }

  evaluate(ctx: Context): EvaluationResult<Expression> {
    return bind(
      this.arg().evaluate(ctx),
      arg => this.func().evaluate(ctx, arg)
    );
  }
}
