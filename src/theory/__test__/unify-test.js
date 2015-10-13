import { Type, Hole, Var } from '../tm';
import { mkRel } from '../ref';

import expectImmutableIs from '../../testutil/expectImmutableIs';


describe('unification', () => {
  const type = Type.singleton;

  it('unifies type', () => {
    expectImmutableIs(type.unify(type), type);
  });

  it('holes unify with everything', () => {
    const hole = new Hole({ name: 'hole', type });
    expectImmutableIs(hole.unify(type), type);
  });

  it('vars unify with everything', () => {
    const v = new Var(mkRel('..', 'binder'), type); // eslint-disable-line id-length
    expectImmutableIs(v.unify(type), type);
  });
});
