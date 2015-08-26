import expect from 'expect';
import { Map, List } from 'immutable';

import { Type, Hole, Var } from '../src/theory/tm';
import { mkSuccess, mkStuck } from '../src/theory/evaluation';
import { Lam, Arr, App, Binder } from '../src/theory/lambda';
import { empty as emptyCtx } from '../src/theory/context';
import { mkAbs, mkRel } from '../src/theory/ref';

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
