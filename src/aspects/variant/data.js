// @flow
//
// Variants! I suppose records and variants together are the way to go!

import { List, Record } from 'immutable';
import invariant from 'invariant';

import { INTRO, Hole } from '../../theory/tm';
import { register } from '../../theory/registry';

import Row from '../row/data';

import type { EvaluationResult } from '../../theory/evaluation';
import type { Tm } from '../../theory/tm';
import type Edit, { Action } from '../../theory/edit';


const VariantTyShape = Record({
  row: null, // Row
  type: null, // Type
});


export class VariantTy extends VariantTyShape {
}


const VariantShape = Record({
  label: null, // Label
  type: null,  // Type
});


export default class Variant extends VariantShape {

  step(): EvaluationResult {
    // TODO step all children?
    throw new Error('unimplemented - Variant.step');
  }

  subst(): Tm {
    throw new Error('unimplemented - Variant.subst');
  }

  actions(): List<Action> {
    return List([]);
  }

  performEdit(): Edit {
    invariant(
      false,
      'Variant.performEdit knows nothing!'
    );
  }

  static typeClass = Row;

  static fillHole(type: Row): Variant {
    invariant(
      type.constructor === Row,
      'Variant asked to fill a hole of type other than Row'
    );

    const values = type.entries.map(
      (colTy, name) => new Hole(name + ' hole', colTy)
    );

    return new Variant({ values, type });
  }

  static form = INTRO;

}

register('variant', Variant);
