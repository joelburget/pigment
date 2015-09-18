// @flow

import invariant from 'invariant';
import { Record, Map } from 'immutable';

import { INTRO, Type } from '../../theory/tm';
import { register } from '../../theory/registry';

import type { Tm } from '../../theory/tm';


var rowShape = Record({
  entries: null, // Map<string, Tm>
}, 'row');

export default class Row extends rowShape {

  // TODO maybe this should be an OrderedMap?
  constructor(entries: Map<string, Tm>): void {
    super({ entries });
  }

  getType(): Tm {
    return Type.singleton;
  }

  evaluate(root: AbsRef, ctx: Context): EvaluationResult {
    return mkSuccess(this);
  }

  static typeClass = Type;

  static fillHole(type: Tm): Row {
    invariant(
      type === Type.singleton,
      'Row asked to fill a hole of type other than *'
    );

    return new Row(Map({}));
  }

  static form = INTRO;
}

register('row', Row);
