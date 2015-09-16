// @flow
//
// Variants! I suppose records and variants together are the way to go!
//
// primitives:
// *

import { Record } from 'immutable';
import type { Iterable } from 'immutable';

import { register } from '../../theory/registry';

import type { Label } from '../record';


var variantShape = Record({
});

export class Variant extends variantShape {
  getType(): Tm {
    throw new Error('unimplemented - Variant.getType');
  }

  evaluate(root: AbsRef, args: [Tm]): EvaluationResult {
    // TODO evaluate all children?
    throw new Error('unimplemented - Variant.evaluate');
  }

  subst(root: AbsRef, ref: Ref, value: Tm): Tm {
    throw new Error('unimplemented - Variant.subst');
  }

  slots(): Iterable<K, V> {
    throw new Error('unimplemented - Variant.slots');
  }

  static form = INTRO;
}

register('variant', Variant);
