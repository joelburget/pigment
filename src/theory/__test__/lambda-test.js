import expect from 'expect';
import { List } from 'immutable';

import { Type, Var } from '../tm';
import { mkSuccess, mkStuck, bind } from '../evaluation';
import { Lam, App } from '../lambda';
import { empty as emptyCtx } from '../context';
import { mkRel, mkAbs } from '../ref';

import { id, k } from '../../../test/examples';
import expectImmutableIs from '../../../test/expectImmutableIs';


describe('lambda', () => {
  const type = Type.singleton;

  it('evaluates id', () => {
    var app = new App(
      id,
      type
    );

    expectImmutableIs(
      app.evaluate(mkAbs(), emptyCtx),
      mkSuccess(type)
    );
  });

  it('evaluates k', () => {
    var app = new App(
      new App(
        k,
        type
      ),
      type
    );

    expectImmutableIs(
      app.evaluate(mkAbs(), emptyCtx),
      mkSuccess(type)
    );
  });
});
