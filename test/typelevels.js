import expect from 'expect';

import { Type, EVar } from '../src/theory/tm';
import { Lam, Arr } from '../src/theory/lambda';
// import { Sigma } from '../src/theory/tuple';
import { empty as emptyCtx } from '../src/theory/context';

describe('typelevels', () => {
  const type = Type.singleton;

  it('knows the types of basics', () => {
    expect(type.getType()).toBe(type);
  });

  it('knows arrs', () => {
    expect(new Arr(type, type).getType()).toBe(type);
  });

  // it('knows sigmas', () => {
  //   // XXX what should the second part of a sigma be? is it a lambda?
  //   expect(new Sigma(type, new Lam('x', type)).getType(emptyCtx))
  //     .toBe(type);
  // });
});
