// @flow

import { List, Record, Map } from 'immutable';
import invariant from 'invariant';

import { INTRO, Hole, Type } from '../../theory/tm';
import { mkSuccess } from '../../theory/evaluation';
import { register } from '../../theory/registry';
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


var recordShape = Record({
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
        name: 'add entry',
        action: () => {
          const newRec = new Rec(
            this.values.set(
              'new entry',
              new Hole('new entry', Type.singleton)
            ),
            this.row
          );
          console.log('rec: add entry', newRec);
          return newRec;
        }
      },
    ]);
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
