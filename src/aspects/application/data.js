// @flow

import { Record } from 'immutable';

import { ELIM, Hole } from '../../theory/tm';
import { register } from '../../theory/registry';
import { bind } from '../../theory/evaluation';
import { mkRel } from '../../theory/ref';

import type { Map } from 'immutable';
import type { EvaluationResult } from '../../theory/evaluation';
import type { Tm } from '../../theory/tm';
import type { AbsRef } from '../../theory/ref';


const appShape = Record({
  func: null,
  arg: null,
  type: null,
}, 'app');

export default class App extends appShape {

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

  static fillHole(type: Tm): App {
    // how to quantify this variable so it's the same in both places?
    // future plan: instantiate here with a quantifier, its context menu allows
    // you to instantiate it and remove the quantifier.
    const x = Type.singleton;

    return new App(
      new Hole('f', XXX /* this needs to be an arrow... */),
      new Hole('x', x),
      type
    );
  }

  static form = ELIM;
}

register('app', App);
