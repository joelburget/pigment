// @flow
//
// Variants! I suppose records and variants together are the way to go!
//
// primitives:
// *

import { List, Record } from 'immutable';
import type { Iterable } from 'immutable';
import invariant from 'invariant';

import { INTRO, Hole, Type } from '../../theory/tm';
import { register } from '../../theory/registry';

import Label from '../label/data';
import Row from '../row/data';


var VariantShape = Record({
  values: null,
  row: null,
});

export class Variant extends VariantShape {
  getType(): Tm {
    return this.row;
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

  actions(): List<Action> {
    return List();
  }

  performEdit(id: string): List<Edit> {
    invariant(
      false,
      "Variant.performEdit doesn't know any edits"
    );
  }

  static typeClass = Row;

  static fillHole(row: Row): Variant {
    invariant(
      row.constructor === Row,
      'Variant asked to fill a hole of type other than Row'
    );

    const values = row.entries.map(
      (type, name) => new Hole(name + ' hole', type)
    );

    return new Variant({ values, row });
  }

  static form = INTRO;
}

register('variant', Variant);
