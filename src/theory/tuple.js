import { mkStuck, mkSuccess, Expression, Type } from './tm';
import { add } from './context';


export class Sigma extends Expression {
  static arity = [0, 1];
  static renderName = "sigma";

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
    throw new Error('TODO - Sigma.evaluate');
  }

  getType() {
    return Type.singleton;
  }
}


export class Tuple extends Expression {
  static arity = [0, 1];
  static renderName = "tuple";

  constructor(inl: Expression, inr: Expression): void {
    super([ new Tm(inl), new Tm(inr) ]);
  }

  map(f): Expression {
    const inl = this.children[0].value;
    const inr = this.children[1].value;
    let v = new Lam(inl, inr);
    v.children = v.children.map(f);
    return v;
  }

  evaluate(ctx: Context): EvaluationResult<Expression> {
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

  getType(ctx: Context) {
    const [ inl, inr ] = this.children;
    const lty = inl.getType(ctx);
    const newCtx = add(ctx, inr.name, [inl, lty]);
    const rty = inr.body.getType(newCtx);

    return new Sigma(lty, rty);
  }
}

// TODO eliminators: outl, outr
