import expect from 'expect';
import { Var, Abs, Tm } from '../src/theory/abt';
import { mkType, mkVar, mkLam, mkPi, mkSigma, mkPair, mkHole, mkApp } from '../src/theory/tm';
import { Map } from 'immutable';
import { empty as emptyCtx } from '../src/theory/context';
import { evaluate, mkSuccess, mkStuck } from '../src/theory/eval';

describe('eval', () => {
  it('knows these', () => {
    // start with an empty context;
    expect(evaluate(emptyCtx, mkType))
      .toEqual(mkSuccess(mkType));

    const hole = mkHole('hole');
    expect(evaluate(emptyCtx, hole))
      .toEqual(mkStuck(hole));

    const lam = mkLam('x', mkVar('x'));
    expect(evaluate(emptyCtx, lam))
      .toEqual(mkStuck(lam));

    expect(evaluate(emptyCtx, mkApp(lam, mkType)))
      .toBe(mkType);
  });
});
