import { Expression, Type } from './tm';
import { mkStuck, mkSuccess, bind } from './evaluation';
import { Var, Abs, Tm } from './abt';
import { lookup, lookupType, add } from './context';


export class Lam extends Expression {
  static arity = [1];
  static renderName = "lam";

  constructor(abt: Abt, type: Expression): void {
    // we can analyze the abt:
    // * Abs - indicates the lambda is binding
    // * Var, Tm - the lambda is constant
    super([ abt ], type);
  }

  map(f): Expression {
    return new Lam(f(this.children[0]));
  }

  evaluate(ctx, x: Expression): EvaluationResult<Expression> {
    const [ child ] = this.children;

    if (child instanceof Var) {
      return mkSuccess(lookup(ctx, child.name));

    } else if (child instanceof Abs) {
      return child
        .subst(new Tm(x), child.name)
        .evaluate(ctx);

    } else { // child instanceof Tm
      return child.value.evaluate(ctx);
    }
  }
}


export class Arr extends Expression {
  static arity = [0, 0];
  static renderName = "arr";

  constructor(domain: Expression, codomain: Expression): void {
    super([ new Tm(domain), new Tm(codomain) ], Type.singleton);
  }

  domain(): Expression {
    return this.children[0].value;
  }

  codomain(): Expression {
    return this.children[1].value;
  }

  map(f): Expression {
    return new Arr(f(this.domain()), f(this.codomain()));
  }

  evaluate(ctx: Context): EvaluationResult<Expression> {
    throw new Error("TODO - Arr.evaluate");
  }
}


export class App extends Expression {
  static arity = [0, 0];
  static renderName = "app";

  constructor(f: Lam, x: Expression): void {
    const codomain = f.type.codomain();
    super([ new Tm(f), new Tm(x) ], codomain);
  }

  func(): Lam {
    return this.children[0];
  }

  arg(): Expression {
    return this.children[1];
  }

  map(f): Expression {
    return new App(f(this.func()), f(this.arg()));
  }

  evaluate(ctx: Context): EvaluationResult<Expression> {
    return bind(
      this.arg().value.evaluate(ctx),
      arg => this.func().value.evaluate(ctx, arg)
    );
  }
}
