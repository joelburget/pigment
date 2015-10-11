import { Type } from '../../theory/tm';
import { mkSuccess } from '../../theory/evaluation';
import { mkAbs } from '../../theory/ref';
import App from '../application/data';

import { id, k } from '../../testutil/examples';
import expectImmutableIs from '../../testutil/expectImmutableIs';


describe('lambda', () => {
  const type = Type.singleton;

  it('steps id', () => {
    const app = new App(
      id,
      type
    );

    expectImmutableIs(
      app.step([mkAbs()]),
      mkSuccess(type)
    );
  });

  it('steps k', () => {
    const app = new App(
      new App(
        k,
        type
      ),
      type
    );

    expectImmutableIs(
      app.step([mkAbs()]),
      mkSuccess(type)
    );
  });
});
