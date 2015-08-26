import expect from 'expect';
import { List } from 'immutable';

import { Type, Var } from '../src/theory/tm';
import { mkSuccess, mkStuck, bind } from '../src/theory/evaluation';
import { Lam, App } from '../src/theory/lambda';
import { empty as emptyCtx } from '../src/theory/context';
import { mkRel, mkAbs } from '../src/theory/ref';

import { id, k } from './examples';
import expectImmutableIs from './expectImmutableIs';


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
