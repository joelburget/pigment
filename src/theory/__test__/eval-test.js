import expect from 'expect';
import { Map, List } from 'immutable';

import { Type, Hole, Var } from '../tm';
import { mkSuccess, mkStuck } from '../evaluation';
import { mkAbs, mkRel } from '../ref';

import Lam from '../../aspects/lambda/data';
import App from '../../aspects/application/data';

describe('eval', () => {
  const type = Type.singleton;

  it('evaluates type', () => {
    // start with an empty context;
    expect(type.evaluate([mkAbs()]))
      .toEqual(mkSuccess(type));
  });

  it('gets stuck on holes', () => {
    const hole = new Hole('hole', type);
    expect(hole.evaluate([mkAbs()]))
      .toEqual(mkStuck(hole));

    const returningHole = new App(
      new Lam(
        null,
        type,
        hole,
        type
      ),
      type
    );
    expect(returningHole.evaluate([mkAbs()]))
      .toEqual(mkStuck(hole));
  });

  describe('lam', () => {
    // TODO would be awesome for this to be parametric
    const ctx = Map({'x': type});

    it('works with var', () => {
      const tm = new App(
        new Lam(
          'x',
          type,
          type,
          type,
        ),
        type
      );

      expect(tm.evaluate(mkAbs(), ctx))
        .toEqual(mkSuccess(type))
    });

    it('works with wildcards', () => {
      const tm = new App(
        new Lam(
          null,
          type,
          type,
          type
        ),
        type
      );

      expect(tm.evaluate(mkAbs(), ctx))
        .toEqual(mkSuccess(type))
    });
  });
});
