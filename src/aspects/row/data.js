// @flow

import invariant from 'invariant';
import { Record, List } from 'immutable';

import { INTRO, Hole, Type } from '../../theory/tm';
import { mkSuccess } from '../../theory/evaluation';
import { register } from '../../theory/registry';
import { openNewEdit } from '../../theory/edit';
import { ADD_ENTRY, addEntry, makeLabel } from '../../commands/addEntry';
import { POKE_HOLE, pokeHole, doPokeHole } from '../../commands/pokeHole';

import type { EvaluationResult } from '../../theory/evaluation';
import type { Tm } from '../../theory/tm';
import type Edit, { Action } from '../../theory/edit';


const rowShape = Record({
  entries: null, // Map<string, Tm>
}, 'row');


export default class Row extends rowShape {

  step(): EvaluationResult {
    return mkSuccess(this);
  }

  actions(): List<Action> {
    return List([addEntry, pokeHole]);
  }

  performEdit(id: string): Edit {
    invariant(
      id === ADD_ENTRY || id === POKE_HOLE,
      'Row.performEdit only knows of ADD_ENTRY and POKE_HOLE'
    );

    if (id === ADD_ENTRY) {
      const entries = this.entries;

      const label = makeLabel(entries);
      const val = new Hole(null, Type.singleton);
      const newRow = new Row(entries.set(label, val));

      return openNewEdit(id, this, newRow, new List());
    } else { // id === POKE_HOLE
      return doPokeHole(this);
    }
  }

  getIntroUp(): Tm {
    return Type.singleton;
  }

  getIntroDown(): ?Tm {
    return new Hole({ type: this });
  }

  static form = INTRO;
}


register('row', Row);
