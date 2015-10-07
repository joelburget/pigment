// @flow

import { List, Record, Map } from 'immutable';
import type { Iterable } from 'immutable';
import invariant from 'invariant';

import { INTRO, Hole, Type } from '../../theory/tm';
import { mkSuccess } from '../../theory/evaluation';
import { register } from '../../theory/registry';
import { openNewEdit } from '../../theory/edit';
import { ADD_ENTRY, addEntry, makeLabel } from '../../commands/addEntry';

import Label from '../label/data';
import Row from '../row/data';

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


const RecordTyShape = Record({
  row: null, // Row
  type: null, // Type
});


export class RecordTy extends RecordTyShape {
}


const RecordShape = Record({
  values: null,
  type: null,
}, 'rec');

export default class Rec extends RecordShape {

  constructor(values: Map<string, Tm>, type: Row) {
    super({ values, type });
  }

  evaluate(root: AbsRef, args: [Tm]): EvaluationResult {
    // TODO evaluate all children?
    return mkSuccess(this);
  }

  subst(root: AbsRef, ref: Ref, value: Tm): Tm {
    throw new Error('unimplemented - Record.subst');
  }

  actions(): List<Action> {
    return List([addEntry]);
  }

  // TODO should this use Row.performEdit instead of building its own row?
  performEdit(id: string): Edit {
    invariant(
      id === ADD_ENTRY,
      'Row.performEdit only knows of ADD_ENTRY'
    );

    const { values, type } = this;
    const label = makeLabel(values);

    const ty = new Hole(null, Type.singleton);
    const val = new Hole(null, ty);

    const newTm = new Rec(
      values.set(label, val),
      new Row(type.entries.set(label, ty))
    );

    return openNewEdit(id, this, newTm, new List());
  }

  static typeClass = Row;

  static fillHole(type: Row): Rec {
    invariant(
      type.constructor === Row,
      'Rec asked to fill a hole of type other than Row'
    );

    const values = type.entries.map(
      (holeTy, name) => new Hole(name + ' hole', holeTy)
    );

    return new Rec(values, type);
  }

  static form = INTRO;
}

register('rec', Rec);
