import expect from 'expect';
import { Map } from 'immutable';

import { Type, Hole } from '../tm';
import { mkSuccess, mkStuck } from '../evaluation';
import { mkFree } from '../ref';

import { mkFunction, mkApplication } from '../../aspects/function/data';


const emptyCtx = Map();

describe('eval', () => {
  const type = Type.singleton;

  it('steps type', () => {
    // start with an empty context;
    expect(type.step(emptyCtx.bind(mkFree())))
      .toEqual(mkSuccess(type));
  });

  it('gets stuck on holes', () => {
    const hole = new Hole({ name: 'hole', type });
    expect(hole.step(emptyCtx.bind(mkFree())))
      .toEqual(mkStuck(hole));

    const returningHole = mkApplication({
      func: mkFunction(
        null,
        type,
        hole,
        type
      ),
      arg: type,
      type,
    });
    expect(returningHole.step(emptyCtx.bind(mkFree())))
      .toEqual(mkStuck(hole));
  });

  describe('function', () => {
    // TODO would be awesome for this to be parametric
    const ctx = Map({'x': type});

    it('works with var', () => {
      const tm = mkApplication({
        func: mkFunction(
          'x',
          type,
          type,
          type,
        ),
        arg: type,
        type,
      });

      expect(tm.step(mkFree(), ctx))
        .toEqual(mkSuccess(type));
    });

    it('works with wildcards', () => {
      const tm = mkApplication({
        func: mkFunction(
          null,
          type,
          type,
          type
        ),
        arg: type,
        type,
      });

      expect(tm.step(mkFree(), ctx))
        .toEqual(mkSuccess(type));
    });
  });
});
