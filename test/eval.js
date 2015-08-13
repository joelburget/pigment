import expect from 'expect';
import { Var, Abs, Tm } from '../src/theory/abt';
import { Type, EVar, Hole } from '../src/theory/tm';
import { Lam, Pi, App } from '../src/theory/lambda';
import { Sigma, Tuple } from '../src/theory/tuple';
import { Map } from 'immutable';
import { empty as emptyCtx } from '../src/theory/context';
import { evaluate, mkSuccess, mkStuck } from '../src/theory/eval';

describe('eval', () => {
  it('evaluates the basics', () => {
    // start with an empty context;
    expect(Type.singleton.evaluate(emptyCtx))
      .toEqual(mkSuccess(Type.singleton));

    const hole = new Hole('hole');
    expect(hole.evaluate(emptyCtx))
      .toEqual(mkStuck(hole));
  });

  it('evaluates functions', () => {
    const lam = new Lam('x', new EVar('x'));
    expect(lam.evaluate(emptyCtx))
      .toEqual(mkStuck(lam));

    expect(new App(lam, Type.singleton).evaluate(emptyCtx))
      .toEqual(mkSuccess(Type.singleton));
  });

  it('evaluates tuples', () => {
    // TODO
  });
});
