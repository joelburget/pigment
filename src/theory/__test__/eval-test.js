import expect from 'expect';
import { Map, List } from 'immutable';

import { Type, Hole, Var } from '../tm';
import { mkSuccess, mkStuck } from '../evaluation';
import { Lam, Arr, App, Binder } from '../lambda';
import { empty as emptyCtx } from '../context';
import { mkAbs, mkRel } from '../ref';

describe('eval', () => {
  const type = Type.singleton;

  it('evaluates type', () => {
    // start with an empty context;
    expect(type.evaluate(mkAbs(), emptyCtx))
      .toEqual(mkSuccess(type));
  });

  it('gets stuck on holes', () => {
    const hole = new Hole('hole', type);
    expect(hole.evaluate(mkAbs(), emptyCtx))
      .toEqual(mkStuck(hole));

    const returningHole = new App(
      new Lam(new Binder({ name: null, type }),
              hole
             ),
      type
    );
    expect(returningHole.evaluate(mkAbs(), emptyCtx))
      .toEqual(mkStuck(hole));
  });

  describe('lam', () => {
    // TODO would be awesome for this to be parametric
    const ctx = Map({'x': type});

    it('works with var', () => {
      const tm = new App(
        new Lam(new Binder({ name: 'x', type }),
                new Var(mkRel('..', 'binder'))
               ),
        type
      );

      expect(tm.evaluate(mkAbs(), ctx))
        .toEqual(mkSuccess(type))
    });

    it('works with wildcards', () => {
      const tm = new App(
        new Lam(
          new Binder({ type }),
          type,
        ),
        type
      );

      expect(tm.evaluate(mkAbs(), ctx))
        .toEqual(mkSuccess(type))
    });
  });
});
