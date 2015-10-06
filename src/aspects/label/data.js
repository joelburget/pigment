// @flow

import invariant from 'invariant';
import { Record } from 'immutable';

import { mkSuccess } from '../../theory/evaluation';
import { register } from '../../theory/registry';
import { INTRO, Type } from '../../theory/tm';

import type { EvaluationResult } from '../../theory/evaluation';
import type { AbsRef } from '../../theory/ref';
import type { Tm } from '../../theory/tm';


var labelShape = Record({
  name: null, // string
  type: null, // Tm
}, 'label');

export default class Label extends labelShape {

  constructor(name: string): void {
    super({ name, type: Type.singleton });
  }

  evaluate(root: AbsRef): EvaluationResult {
    return mkSuccess(this);
  }

  actions(): List<Action> {
    return List();
  }

  performEdit(id: string): List<Edit> {
    invariant(
      false,
      "Label.performEdit doesn't know any actions"
    );
  }

  static typeClass = Type;

  static fillHole(type: Tm): Label {
    invariant(
      type === Type.singleton,
      'Label asked to fill a hole of type other than Type'
    );

    return new Label('new label');
  }

  static form = INTRO;
}

register('label', Label);
