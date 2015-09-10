import expect from 'expect';
import { List } from 'immutable';

import expectImmutableIs from './expectImmutableIs';
import { Type, Hole, Var } from '../src/theory/tm';
import { mkRel } from '../src/theory/ref';


describe('unification', () => {
  const type = Type.singleton;

  it('unifies type', () => {
    expectImmutableIs(type.unify(type), type);
  });

  it('holes unify with everything', () => {
    const hole = new Hole('hole', type);
    expectImmutableIs(hole.unify(type), type);
  });

  it('vars unify with everything', () => {
    const v = new Var(mkRel('..', 'binder'), type);
    expectImmutableIs(v.unify(type), type);
  });
});
