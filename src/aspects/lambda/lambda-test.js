import expect from 'expect';
import { List } from 'immutable';

import { Type, Var } from '../../theory/tm';
import { mkSuccess, mkStuck, bind } from '../../theory/evaluation';
import { mkRel, mkAbs } from '../../theory/ref';
import Lam from './data';
import App from '../application/data';

import { id, k } from '../../testutil/examples';
import expectImmutableIs from '../../testutil/expectImmutableIs';


describe('lambda', () => {
  const type = Type.singleton;

  it('steps id', () => {
    var app = new App(
      id,
      type
    );

    expectImmutableIs(
      app.step([mkAbs()]),
      mkSuccess(type)
    );
  });

  it('steps k', () => {
    var app = new App(
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
