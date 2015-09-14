// @flow

import { Record, OrderedMap } from 'immutable';

import { Type } from '../../theory/tm';
import { mkSuccess } from '../../theory/evaluation';
import { register } from '../../theory/registry';

import type { Tm } from '../../theory/tm';
import type { EvaluationResult } from '../../theory/evaluation';
import type { AbsRef, Ref } from '../../theory/ref';


// record primitive operations
// * select : { l : a | r } -> a
//   r.l
//   distance p = sqrt (p.x * p.x + p.y * p.y)
// * restrict : { l : a | r } -> { r }
//   r - l
//   update:
//     { l := x | r } = { l = x | r - l }
//   rename:
//     { l <- m | r } = { l = r.m | r - m }
// * extend : a -> { r } -> { l : a | r }
//   { l = e | r }
//   origin = { x = 0 | { y = 0 | {} } }
//   origin = { x = 0, y = 0 }


var recordShape = Record({
  values: null,
  type: null,
}, 'rec');

export default class Rec extends recordShape {

  constructor(values: OrderedMap<string, Tm>, type: Row) {
    super({ values, type });
  }

  getType(): Tm {
    return this.type;
  }

  evaluate(root: AbsRef, args: [Tm]): EvaluationResult {
    // TODO evaluate all children?
    return mkSuccess(this);
  }
}

register('rec', Rec);
