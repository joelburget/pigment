// @flow

import { List, Record, Map } from 'immutable';
import invariant from 'invariant';

import { INTRO, Hole, Type } from '../../theory/tm';
import { mkSuccess } from '../../theory/evaluation';
import { register } from '../../theory/registry';
import { openNewEdit } from '../../theory/edit';

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


const ADD_ENTRY = 'ADD_ENTRY';


const recordShape = Record({
  values: null,
  row: null,
}, 'rec');

export default class Rec extends recordShape {

  constructor(values: Map<string, Tm>, row: Row) {
    super({ values, row });
  }

  getType(): Tm {
    return this.row;
  }

  evaluate(root: AbsRef, args: [Tm]): EvaluationResult {
    // TODO evaluate all children?
    return mkSuccess(this);
  }

  subst(root: AbsRef, ref: Ref, value: Tm): Tm {
    throw new Error('unimplemented - Record.subst');
  }

  slots(): Iterable<K, V> {
    throw new Error('unimplemented - Record.slots');
  }

  actions(): List<Action> {
    return List([
      {
        id: ADD_ENTRY,
        title: 'add entry',
        // value: new Rec(
        //   this.values.set(
        //     'new entry',
        //     new Hole('new entry', Type.singleton)
        //   ),
        //   this.row
        // )
      },
    ]);
  }

  performEdit(id: string): List<Edit> {
    invariant(
      id === ADD_ENTRY,
      'Type.edit only knows of POKE_HOLE'
    );

    const { values, row } = this;

    const label = 'new entry';
    const val = new Hole(null, Type.singleton);

    const newTm = new Rec(
      values.set(label, val),
      new Row(row.entries.set(label, Type.singleton))
    );

    return openNewEdit(id, this, newTm, new List());
  }

  static typeClass = Row;

  static fillHole(row: Row): Rec {
    invariant(
      row.constructor === Row,
      'Rec asked to fill a hole of type other than Row'
    );

    const values = row.entries.map(
      (type, name) => new Hole(name + ' hole', type)
    );

    return new Rec(values, row);
  }

  static form = INTRO;
}

register('rec', Rec);
