import type Context from './context';

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


export function bind(e: EvaluationResult<A>,
                     f: Function): EvaluationResult<A> {
  return e.type === 'success' ? f(e.value) : e;
}


export function evalLookup(ctx: Context, name: string) {
  return ctx.get(name).evaluate(ctx);
}
