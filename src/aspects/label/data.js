// @flow

import invariant from 'invariant';
import { List, Record, Set } from 'immutable';

import { mkSuccess } from '../../theory/evaluation';
import { register } from '../../theory/registry';
import { INTRO, Type } from '../../theory/tm';
import Relation, { IS_TYPE, MATCHES } from '../../theory/relation';

import type { EvaluationResult } from '../../theory/evaluation';
import type { Tm } from '../../theory/tm';
import type Edit, { Action } from '../../theory/edit';


const LabelShape = Record({
  name: null, // string
  type: null, // Tm
}, 'label');

export default class Label extends LabelShape {

  constructor(name: string): void {
    super({ name, type: Type.singleton });
  }

  step(): EvaluationResult {
    return mkSuccess(this);
  }

  actions(): List<Action> {
    return List();
  }

  performEdit(): Edit {
    invariant(
      false,
      "Label.performEdit doesn't know any actions"
    );
  }

  static typeClass = Type;

  static fillHole = [
    Set([
      new Relation({
        type: IS_TYPE,
        subject: this.path,
        object: this.path.type,
      });
    ]),
    new Label('new label'),
  ]

  static form = INTRO;
}

register('label', Label);
