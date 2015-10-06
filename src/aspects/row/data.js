// @flow

import invariant from 'invariant';
import { Record, Map, List } from 'immutable';

import { INTRO, Hole, Type } from '../../theory/tm';
import { mkSuccess } from '../../theory/evaluation';
import { register } from '../../theory/registry';
import { openNewEdit } from '../../theory/edit';
import { ADD_ENTRY, addEntry } from '../../commands/addEntry';
import { POKE_HOLE, pokeHole, doPokeHole } from '../../commands/pokeHole';

import type { Tm } from '../../theory/tm';


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
    return List([addEntry, pokeHole]);
  }

  performEdit(id: string): List<Edit> {
    invariant(
      id === ADD_ENTRY || id === POKE_HOLE,
      'Row.performEdit only knows of ADD_ENTRY and POKE_HOLE'
    );

    if (id === ADD_ENTRY) {
      const { values, row } = this;

      const label = 'new entry';
      const newRow = new Row(this.entries.set(label, Type.singleton))

      return openNewEdit(id, this, newRow, new List());
    } else {
      return doPokeHole(this);
    }
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
