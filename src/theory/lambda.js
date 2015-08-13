import { mkStuck, mkSuccess, Expression, Type } from './tm';
import { Abs, Tm } from './abt';
import { lookup, lookupType } from './context';


export class Lam extends Expression {
  static arity = [1];
  static renderName = "lam";

  constructor(name: string, body: Expression): void {
    super([ new Abs(name, new Tm(body)) ]);
  }

  map(f): Expression {
    const name = this.children[0].name;
    const body = this.children[1].value;
    let v = new Lam(name, body);
    v.children = v.children.map(f);
    return v;
  }

  evaluate(): EvaluationResult<Expression> {
    return mkStuck(this);
  }

  getType(ctx: Context) {
    const [ abs ] = this.children;
    const newCtx = add(ctx, abs.name, lookup(ctx, abs.name));
    const codomainTy = abs.body.getType(newCtx);

    return new Pi(lookupType(ctx, abs.name), codomainTy);
  }
}


export class Pi extends Expression {
  static arity = [0, 1];
  static renderName = "pi";

  constructor(domain: Expression, codomain: Expression): void {
    super([ new Tm(domain), new Tm(codomain) ]);
  }

  map(f): Expression {
    const domain = this.children[0].value;
    const codomain = this.children[1].value;
    let v = new Lam(domain, codomain);
    v.children = v.children.map(f);
    return v;
  }

  evaluate(ctx: Context): EvaluationResult<Expression> {
    throw new Error("TODO - Pi.evaluate");
  }

  getType(ctx: Context) {
    return Type.singleton;
  }
}


export class App extends Expression {
  static arity = [0, 0];
  static renderName = "app";

  constructor(f: Expression, x: Expression): void {
    super([ new Tm(f), new Tm(x) ]);
  }

  map(f): Expression {
    const e1 = this.children[0].value;
    const e2 = this.children[1].value;
    let v = new Lam(e1, e2);
    v.children = v.children.map(f);
    return v;
  }

  evaluate(ctx: Context): EvaluationResult<Expression> {
    const [ e1, e2 ] = this.children;
    const val = e2.value.evaluate(ctx);
    if (val.type === 'success') {
      // TODO subst
      // XXX why does subst not always use .name?
      const body = e2.subst(val, e2.name);
      return body.evaluate(ctx);
    } else { // stuck
      // TODO
    }
  }

  getType(ctx: Context) {
    const [ f, x ] = this.children;
    const fTy = f.getType(ctx); // Pi(X; \x -> ?)
    const xTy = x.getType(ctx);

    // TODO no way this is right...
    const app = new App(new App(fTy, xTy), x);
    return app.getType(ctx);
  }
}
