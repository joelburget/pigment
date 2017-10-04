import { Type, Hole, Var } from '../tm';
import { mkBound } from '../ref';

import expectImmutableIs from '../../testutil/expectImmutableIs';


describe('unification', () => {

  it('unifies type', () => {
    expectImmutableIs(Type.unify(Type), Type);
  });

  it('holes unify with everything', () => {
    const hole = new Hole({ name: 'hole', Type });
    expectImmutableIs(hole.unify(Type), Type);
  });

  it('vars unify with everything', () => {
    const v = new Var(mkBound('..', 'binder'), Type); // eslint-disable-line id-length
    expectImmutableIs(v.unify(Type), Type);
  });
});
