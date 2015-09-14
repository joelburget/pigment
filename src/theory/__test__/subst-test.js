import expect from 'expect';

import { Type, Var } from '../tm';
import { mkSuccess, mkStuck, bind } from '../evaluation';
import { mkRel, mkAbs } from '../ref';
import Lam from '../../aspects/lambda/data';
import App from '../../aspects/application/data';

import { id, k } from '../../testutil/examples';
import expectImmutableIs from '../../testutil/expectImmutableIs';


describe('lambda', () => {
  const type = Type.singleton;

  it("doesn't substitute", () => {
    var noVarLam = new Lam(
      ['x', type],
      type
    );

    expectImmutableIs(
      noVarLam.subst(mkAbs(), mkRel('binder'), type),
      noVarLam
    );

    // different variable
    expectImmutableIs(
      id.subst(mkAbs(), mkRel(), type),
      id
    );
  });

  it('substitutes', () => {
    expectImmutableIs(
      id.subst(mkAbs(), mkRel('binder'), type),
      new Lam(
        'x',
        type,
        type,
        type
      )
    );

    // k: \x y -> x

    // substituting for y does nothing
    expectImmutableIs(
      k.subst(mkAbs(), mkRel('body', 'binder'), type),
      k
    );

    // substituting for x replaces the inner body!
    expectImmutableIs(
      k.subst(mkAbs(), mkRel('binder'), type),
      new Lam(
        'x',
        type,
        new Lam(
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
      k.subst(mkAbs(), mkAbs('binder'), type),
      new Lam(
        'x',
        type,
        new Lam(
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
      k.subst(mkAbs(), mkAbs('body', 'binder'), type),
      k
    );

    // some random path also doesn't change anything
    expectImmutableIs(
      k.subst(mkAbs(), mkAbs('a', 'b', 'c'), type),
      k
    );
  });
});
