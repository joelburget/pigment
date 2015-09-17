// @flow

import invariant from 'invariant';
import { Record, Map } from 'immutable';

import { INTRO, Type } from '../../theory/tm';
import { register } from '../../theory/registry';

import type { Tm } from '../../theory/tm';


var rowShape = Record({
  entries: null, // Map<string, Tm>
}, 'row');

export class Row extends rowShape {

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

  static typeClass = Type.singleton;

  static fillHole(type: Tm): Row {
    // XXX hold up what's happening here?
    invariant(
      type === Type.singleton
      'Type asked to fill a hole of type other than RowTy'
    );

    return RowTy.singleton;
  }

  static form = INTRO;
}

register('row', Row);
