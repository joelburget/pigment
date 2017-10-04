import { Type } from '../tm';
import { mkBound, mkFree } from '../ref';
import { mkFunction } from '../../aspects/function/data';

import { id, k } from '../../testutil/examples';
import expectImmutableIs from '../../testutil/expectImmutableIs';


describe('lambda', () => {
  const type = Type.singleton;

  it("doesn't substitute", () => {
    const noVarLam = mkFunction(
      ['x', type],
      type
    );

    expectImmutableIs(
      noVarLam.subst(mkFree(), mkBound('binder'), type),
      noVarLam
    );

    // different variable
    expectImmutableIs(
      id.subst(mkFree(), mkBound(), type),
      id
    );
  });

  it('substitutes', () => {
    expectImmutableIs(
      id.subst(mkFree(), mkBound('binder'), type),
      mkFunction(
        'x',
        type,
        type,
        type
      )
    );

    // k: \x y -> x

    // substituting for y does nothing
    expectImmutableIs(
      k.subst(mkFree(), mkBound('body', 'binder'), type),
      k
    );

    // substituting for x replaces the inner body!
    expectImmutableIs(
      k.subst(mkFree(), mkBound('binder'), type),
      mkFunction(
        'x',
        type,
        mkFunction(
          'y',
          type,
          type,
          type
        ),
        type
      )
    );

    // we can also use the absolute path (we're starting at root here)!
    expectImmutableIs(
      k.subst(mkFree(), mkFree('binder'), type),
      mkFunction(
        'x',
        type,
        mkFunction(
          'y',
          type,
          type,
          type
        ),
        type,
      )
    );

    // y's absolute path doesn't change anything
    expectImmutableIs(
      k.subst(mkFree(), mkFree('body', 'binder'), type),
      k
    );

    // some random path also doesn't change anything
    expectImmutableIs(
      k.subst(mkFree(), mkFree('a', 'b', 'c'), type),
      k
    );
  });
});
