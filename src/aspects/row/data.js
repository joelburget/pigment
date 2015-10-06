// @flow

import invariant from 'invariant';
import { Record, Map, List } from 'immutable';

import { INTRO, Hole, Type } from '../../theory/tm';
import { mkSuccess } from '../../theory/evaluation';
import { register } from '../../theory/registry';
import { openNewEdit } from '../../theory/edit';

import type { Tm } from '../../theory/tm';


// TODO does it smell that the same code is defined in both Row and Record?
const ADD_ENTRY = 'ADD_ENTRY';


var rowShape = Record({
  entries: null, // Map<string, Tm>
  type: null, // Tm
}, 'row');

export default class Row extends rowShape {

  // TODO maybe this should be an OrderedMap?
  constructor(entries: Map<string, Tm>): void {
    super({ entries, type: Type.singleton });
  }

  evaluate(root: AbsRef, ctx: Context): EvaluationResult {
    return mkSuccess(this);
  }

  actions(): List<Action> {
    return List([
      {
        id: ADD_ENTRY,
        title: 'add entry',
      },
    ]);
  }

  performEdit(id: string): List<Edit> {
    invariant(
      id === ADD_ENTRY,
      'Row.performEdit only knows of ADD_ENTRY'
    );

    const { values, row } = this;

    const label = 'new entry';
    const newRow = new Row(this.entries.set(label, Type.singleton))

    return openNewEdit(id, this, newRow, new List());
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
