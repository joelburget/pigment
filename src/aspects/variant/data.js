// @flow
//
// Variants! I suppose records and variants together are the way to go!

import { List, Record } from 'immutable';
import invariant from 'invariant';

import { INTRO } from '../../theory/tm';
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


// Interesting special cases:
// * enumerations
// * single-field variants (newtype, essentially)
//
// Both would be useful to visually distinguish.
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

  getIntroUp(): Tm {
    const entries = Map([this.label.name, XXX]);

    return new Row({ entries });
  }

  getIntroDown(): ?Tm {
    return null;
  }

  static form = INTRO;

}

register('variant', Variant);
