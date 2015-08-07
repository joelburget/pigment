import expect from 'expect';
import { varString, gensym, dummy, Var, Pi, Type, Lambda, App, Abstraction, inferType, equal } from '../src/theory/tm';
import { Map } from 'immutable';
import Immutable from 'immutable';

describe('evalutation', () => {
  it('compares variables', () => {
    const free = varString("free");
    const free2 = varString("free2");
    const gensym1 = gensym("gensym", 1);
    const gensym2 = gensym("gensym", 2);

    expect(Immutable.is(free, free)).toBe(true);
    expect(Immutable.is(free, free2)).toBe(false);

    expect(Immutable.is(gensym1, gensym1)).toBe(true);
    expect(Immutable.is(gensym1, gensym2)).toBe(false);
    expect(Immutable.is(gensym1, free)).toBe(false);

    // XXX does a dummy equal other stuff?
    expect(Immutable.is(dummy(), dummy())).toBe(true);
  });

  it('compares expressions', () => {
    const emptyContext = Map();

    expect(equal(emptyContext, Type.singleton, Type.singleton)).toBe(true);

    const smallContext = Map([
      [varString("x"), [Type.singleton]],
      [gensym("x", 1), [Type.singleton]],
    ]);

    expect(equal(smallContext,
                 new Var(varString("x")),
                 new Var(varString("x")))
          ).toBe(true);

    expect(equal(smallContext,
                 new Var(varString("x")),
                 new Var(gensym("x", 1)))
          ).toBe(false);
  });

  it('infers types', () => {
    const ctx = Map([
      [varString("x"), [Type.singleton]],
      [gensym("x", 1), [new Lambda(new Abstraction(varString("x"), Type.singleton, new Var(varString("x"))))]]
    ]);

    expect(inferType(ctx, new Var(varString("x")))).toBe(Type.singleton);

    const ty = inferType(ctx, new Var(gensym("x", 1)));
    const expected = new Lambda(
      new Abstraction(varString("x"), Type.singleton, new Var(varString("x")))
    );
    expect(equal(ctx, ty, expected)).toBe(true);

  });
});
