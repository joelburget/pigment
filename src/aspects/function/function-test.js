import { Type } from '../../theory/tm';
import { mkSuccess } from '../../theory/evaluation';

import { id, k } from '../../testutil/examples';
import expectImmutableIs from '../../testutil/expectImmutableIs';

import { mkApplication } from './data';


describe('functions', () => {

  it('steps id', () => {
    const app = mkApplication(id, Type);

    expectImmutableIs(
      app.step(),
      mkSuccess(Type)
    );
  });

  it('steps k', () => {
    const app = mkApplication(
      mkApplication(k, Type),
      Type
    );

    expectImmutableIs(
      app.step(),
      mkSuccess(Type)
    );
  });

});
