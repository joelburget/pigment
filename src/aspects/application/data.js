// @flow

import { Record, Set } from 'immutable';

import { ELIM, Hole, Type } from '../../theory/tm';
import { register } from '../../theory/registry';
import { bind } from '../../theory/evaluation';
import { mkRel } from '../../theory/ref';
import Relation, { IS_TYPE, MATCHES } from '../../theory/relation';

import type { Map } from 'immutable';
import type { EvaluationResult } from '../../theory/evaluation';
import type { Tm } from '../../theory/tm';
import type { AbsRef } from '../../theory/ref';


const AppShape = Record({
  func: null,
  arg: null,
  type: null,
}, 'app');


export default class App extends AppShape {

  step(root: AbsRef, ctx: Map<string, Tm>): EvaluationResult {
    return bind(
      this.arg.step(root.extend(mkRel('arg')), ctx),
      arg => this.func.step(root.extend(mkRel('func')), ctx, arg)
    );
  }

  // hm... this hardly seems to make sense for app...
  subst(): Tm {
    throw new Error('unimplemented - App.subst');
  }

    // how to quantify this variable so it's the same in both places?
    // future plan: instantiate here with a quantifier, its context menu allows
    // you to instantiate it and remove the quantifier.
    const type = Type.singleton;

  let internalMatch = new Relation({
    type: MATCHES,
    subject: this.path.push('arg', 'type'),
    object: this.path.push('func', 'type', 'domain')
  });

  let externalMatch = new Relation({
    type: MATCHES,
    subject: this.path.push('func', 'type', 'codomain'),
    object: this.path.push('type'),
  });

  static fillHole = [
    Set([
      // TODO - could either match be expressed better as an IS_TYPE?
      internalMatch,
      externalMatch,
    ]),
    new App(
      new Hole('f', XXX /* this needs to be an arrow... */),
      new Hole('x', type),
      type
    ),
  ];

  static form = ELIM;
}

register('app', App);
