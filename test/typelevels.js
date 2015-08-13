import expect from 'expect';
import { Var, Abs, Tm } from '../src/theory/abt';
import { mkType, mkVar, mkLam, mkPi, mkSigma, mkPair } from '../src/theory/tm';
import { getType } from '../src/theory/typelevels';
import { Map } from 'immutable';
import { empty as emptyCtx } from '../src/theory/context';

describe('typelevels', () => {
  it('knows these', () => {
    // start with an empty context;
    expect(getType(emptyCtx, mkType))
      .toBe(mkType);

    expect(getType(emptyCtx.set('x', [mkType, mkType]), mkVar('x')))
      .toBe(mkType);

    expect(getType(emptyCtx, mkPi(mkType, mkLam('_', mkType))))
      .toBe(mkType);

    // XXX what should the second part of a sigma be? is it a lambda?
    expect(getType(emptyCtx, mkSigma(mkType, mkLam('_', mkType))))
      .toBe(mkType);
  });
});
