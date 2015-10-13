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


// how to quantify this variable so it's the same in both places?
// future plan: instantiate here with a quantifier, its context menu allows
// you to instantiate it and remove the quantifier.
const type = Type.singleton;

const internalMatch = new Relation({
  type: MATCHES,
  subject: mkRel('arg', 'type'),
  object: mkRel('func', 'type', 'domain')
});

const externalMatch = new Relation({
  type: MATCHES,
  subject: mkRel('func', 'type', 'codomain'),
  object: mkRel('type'),
});

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

  generateConstraints(): Set<Relation> {
    return Set([
      // TODO - could either match be expressed better as an IS_TYPE?
      new Relation({
        type: MATCHES,
        subject: mkRel('func', 'type', 'domain'),
        object: mkRel('arg', 'type'),
      }),
      externalMatch,
      new Relation({
        type: IS_TYPE,
        subject: mkRel(),
        // object: mkRel('type'),
        // XXX bleh
        type: new Arrow(XXX)
      }),
    ]);
  }

  static form = ELIM;
}

register('app', App);
