// @flow

import invariant from 'invariant';
import { List, Record } from 'immutable';

import { mkSuccess } from '../../theory/evaluation';
import { register } from '../../theory/registry';
import { INTRO, Type } from '../../theory/tm';

import type Edit, { Action } from '../../theory/edit';
import type { EvaluationResult } from '../../theory/evaluation';
import type { Tm } from '../../theory/tm';


const LabelShape = Record({
  name: null, // string
}, 'label');


export default class Label extends LabelShape {

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

  getIntroUp(): Tm {
    // TODO is this right? Should there be a LabelTy?
    return Type.singlaton;
  }

  getIntroDown(): ?Tm {
    return null;
  }

  static form = INTRO;
}


register('label', Label);
