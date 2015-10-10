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
import { openNewEdit } from '../../theory/edit';
import { ADD_ENTRY, addEntry, makeLabel } from '../../commands/addEntry';

import Label from '../label/data';
import Row from '../row/data';

import type { Tm } from '../../theory/tm';
import type { AbsRef } from '../../theory/ref';


const VariantTyShape = Record({
  row: null, // Row
  type: null, // Type
});


export class VariantTy extends VariantTyShape {
}


const VariantShape = Record({
  label: null,
  type: null,
});


export default class Variant extends VariantShape {

  step(root: AbsRef, ctx: Context): EvaluationResult {
    // TODO step all children?
    throw new Error('unimplemented - Variant.step');
  }

  subst(root: AbsRef, ref: Ref, value: Tm): Tm {
    throw new Error('unimplemented - Variant.subst');
  }

  actions(): List<Action> {
    return List([addEntry]);
  }

  performEdit(id: string): Edit {
    invariant(
      id === ADD_ENTRY,
      "Variant.performEdit only knows of ADD_ENTRY"
    );

    const { row, type } = this;

    const label = makeLabel(row.values);
    const ty = new Hole(null, Type.singleton);
    const val = new Hole(null, ty);

    const newTm = new Variant({
      values: values.set(label, val),
      type: new Row(type.entries.set(label, ty))
    });

    return openNewEdit(id, this, newTm, new List());
  }

  static typeClass = Row;

  static fillHole(type: Row): Variant {
    invariant(
      type.constructor === Row,
      'Variant asked to fill a hole of type other than Row'
    );

    const values = type.entries.map(
      (type, name) => new Hole(name + ' hole', type)
    );

    return new Variant({ values, type });
  }

  static form = INTRO;

}

register('variant', Variant);
