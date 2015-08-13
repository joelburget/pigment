import { Map } from 'immutable';
import type { Context } from './context'
import { lookupValue } from './context'


type EvalutationResult<A>
  = { type: 'success', value: A }
  | { type: 'stuck', value: A }

export function mkSuccess(e) {
  return {
    type: 'success',
    value: e,
  };
}

export function mkStuck(e) {
  return {
    type: 'stuck',
    value: e,
  };
}

// also normalization by evaluation
export function evaluate(ctx: Context, e: Expression): EvalutationResult<Expression> {
  switch (e.type) {
    case "var":
      // TODO is this right? what should the context be?
      // or maybe we should never end up here?
      return evaluate(ctx, lookupValue(ctx, e.name));

    case "type":
      return mkSuccess(e);

    case "hole":
    case "lam":
      return mkStuck(e);

    case "app":
      const [ e1, e2 ] = e.children;
      const val = evaluate(ctx, e2);
      // TODO subst
      // XXX why does subst not always use .name?
      const body = e2.subst(val, e2.name);
      console.log('e1', e1);
      console.log('e2', e2);
      console.log('val', val);
      console.log('body', body);
      return evaluate(ctx, body);

    case "pi":
    case "sigma":
    case "tuple":
  }
}
