import { mkStuck, mkSuccess, Expression } from './tm';
import { Var, Abs, Tm, Abt } from './abt';


export class Sigma extends Expression {
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
}


export class Tuple extends Expression {
  static arity = [0, 1];

  constructor(inl: Expression, inr: Expression): void {
    super(arguments);
    this.children = [ new Tm(inl), new Tm(inr) ];
  }

  map(f) {
    const inl = this.children[0].value;
    const inr = this.children[1].value;
    let v = new Lam(inl, inr);
    v.children = v.children.map(f);
    return v;
  }

  evaluate(ctx: Context) {
    const [ inl, inr ] = this.children;
    const lval = inl.evaluate(ctx);
    if (lval.type === 'success') {
      const rbody = inr.subst(lval.value, inr.name);
      const rval = rbody.evaluate(ctx);

      if (rval.type === 'success') {
        return mkSuccess(new Tuple(lval.value, rval.value));
      } else {
        // XXX
      }
    } else {
      // XXX
    }
  }
}

// TODO eliminators: outl, outr
