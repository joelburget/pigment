import expect from 'expect';

import { Type } from '../tm';
import { Lam } from '../../aspects/lambda/data';
// import { Sigma } from '../tuple';

describe('typelevels', () => {
  const type = Type.singleton;

  it('knows the types of basics', () => {
    expect(type.getType()).toBe(type);
  });

  // it('knows sigmas', () => {
  //   // XXX what should the second part of a sigma be? is it a lambda?
  //   expect(new Sigma(type, new Lam('x', type)).getType([]))
  //     .toBe(type);
  // });
});
