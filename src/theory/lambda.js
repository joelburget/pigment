import { mkStuck, mkSuccess, Expression } from './tm';
import { Var, Abs, Tm } from './abt';


export class Lam extends Expression {
  static arity = [1];

  constructor(name: string, body: Expression): void {
    super(arguments);
    this.children = [ new Abs(name, new Tm(body)) ];
  }

  map(f) {
    const name = this.children[0].name;
    const body = this.children[1].value;
    let v = new Lam(name, body);
    v.children = v.children.map(f);
    return v;
  }

  evaluate() {
    return mkStuck(this);
  }
}


export class Pi extends Expression {
  static arity = [0, 1];

  constructor(domain: Expression, codomain: Expression): void {
    super(arguments);
    this.children = [ new Tm(domain), new Tm(codomain) ];
  }

  map(f) {
    const domain = this.children[0].value;
    const codomain = this.children[1].value;
    let v = new Lam(domain, codomain);
    v.children = v.children.map(f);
    return v;
  }

  evaluate(ctx: Context) {
    throw new Error("TODO - Pi.evaluate");
  }
}


export class App extends Expression {
  static arity = [0, 0];

  constructor(f: Expression, x: Expression): void {
    super(arguments);
    this.children = [ new Tm(f), new Tm(x) ];
  }

  map(f) {
    const e1 = this.children[0].value;
    const e2 = this.children[1].value;
    let v = new Lam(e1, e2);
    v.children = v.children.map(f);
    return v;
  }

  evaluate(ctx: Context) {
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
}
