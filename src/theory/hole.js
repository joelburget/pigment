// @flow
import { List, Record } from 'immutable';

import { mkStuck } from './evaluation';

import type { Action } from './edit';
import type { EvaluationResult } from './evaluation';
import type { Ref, FreeVar } from './ref';
import type { Tm } from './tm';


const HoleShape = Record({
  name: null,
  type: null,
}, 'hole');


export default class Hole extends HoleShape {

  step(): EvaluationResult {
    return mkStuck(this);
  }

  subst(root: FreeVar, ref: Ref, value: Tm): Tm {
    return ref.is(this.ref, root) ? value : this;
  }

  actions(): List<Action> {
    return List();
  }

  // TODO
  // * term
  // * type
  // * getPieces
  // * performEdit

}
