import expect from 'expect';
import { Map } from 'immutable';

import { Type, Hole } from '../tm';
import { mkSuccess, mkStuck } from '../evaluation';
import { mkAbs } from '../ref';

import Lam from '../../aspects/lambda/data';
import App from '../../aspects/application/data';


const emptyCtx = Map();

describe('eval', () => {
  const type = Type.singleton;

  it('steps type', () => {
    // start with an empty context;
    expect(type.step(emptyCtx.bind(mkAbs())))
      .toEqual(mkSuccess(type));
  });

  it('gets stuck on holes', () => {
    const hole = new Hole({ name: 'hole', type });
    expect(hole.step(emptyCtx.bind(mkAbs())))
      .toEqual(mkStuck(hole));

    const returningHole = new App({
      func: new Lam(
        null,
        type,
        hole,
        type
      ),
      arg: type,
      type,
    });
    expect(returningHole.step(emptyCtx.bind(mkAbs())))
      .toEqual(mkStuck(hole));
  });

  describe('lam', () => {
    // TODO would be awesome for this to be parametric
    const ctx = Map({'x': type});

    it('works with var', () => {
      const tm = new App({
        func: new Lam(
          'x',
          type,
          type,
          type,
        ),
        arg: type,
        type,
      });

      expect(tm.step(mkAbs(), ctx))
        .toEqual(mkSuccess(type));
    });

    it('works with wildcards', () => {
      const tm = new App({
        func: new Lam(
          null,
          type,
          type,
          type
        ),
        arg: type,
        type,
      });

      expect(tm.step(mkAbs(), ctx))
        .toEqual(mkSuccess(type));
    });
  });
});
