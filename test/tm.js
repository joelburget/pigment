import expect from 'expect';
import { Var, Abs, Tm } from '../src/theory/abt';
import { Lam, App, Pi, Sigma, Type } from '../src/theory/tm';
import { inferType, checkType } from '../src/theory/typecheck';
import { Map } from 'immutable';
import Immutable from 'immutable';

describe('evalutation', () => {
  // it('compares expressions', () => {
  //   const emptyContext = Map();

  //   expect(equal(emptyContext, Type.singleton, Type.singleton)).toBe(true);

  //   const smallContext = Map([
  //     [varString("x"), [Type.singleton]],
  //     [gensym("x", 1), [Type.singleton]],
  //   ]);

  //   expect(equal(smallContext,
  //                new Var(varString("x")),
  //                new Var(varString("x")))
  //         ).toBe(true);

  //   expect(equal(smallContext,
  //                new Var(varString("x")),
  //                new Var(gensym("x", 1)))
  //         ).toBe(false);
  // });

  it('infers types', () => {
    const l = {
      ...Lam,
      children: [
        new Abs("x", new Var("x"))
      ]
    };

    const ctx = Map([
      [new Var("x"), [Type]],
      [new Var("y"), [l]]
    ]);

    expect(inferType(ctx, new Var("x"))).toBe(Type);

    const ty = inferType(ctx, new Var("x"));
    expect(equal(ctx, ty, l)).toBe(true);

  });
});
