// @flow

import invariant from 'invariant';
import { Record, List } from 'immutable';

import { Hole, Type } from '../../theory/tm';
import { register } from '../../theory/registry';
import { openNewEdit } from '../../theory/edit';
import { ADD_ENTRY, addEntry, makeLabel } from '../../commands/addEntry';
import { POKE_HOLE, pokeHole, doPokeHole } from '../../commands/pokeHole';

import type { EvaluationResult } from '../../theory/evaluation';
import type { Tm } from '../../theory/tm';
import type Edit, { Action } from '../../theory/edit';


// formation

const Row = Record({
  entries: null, // Map<string, Tm>
}, 'row');


export const mkRow = entries => new Tm(
  ['Row', 'formation'], new Row({ entries })
);


const formation = {
  term: mkRow(XXX),
  type: Type,

  actions: () => List([addEntry, pokeHole]),

  performEdit: (id: string) => {
    invariant(
      id === ADD_ENTRY || id === POKE_HOLE,
      'Row.performEdit only knows of ADD_ENTRY and POKE_HOLE'
    );

    if (id === ADD_ENTRY) {
      const entries = this.entries;

      const label = makeLabel(entries);
      const val = new Hole({ type: Type.singleton });
      const newRow = new Row(entries.set(label, val));

      return openNewEdit(id, this, newRow, new List());
    } else { // id === POKE_HOLE
      return doPokeHole(this);
    }
  }
};


const signature = {
  formation,

  // no introduction / elimination! (for now?)
  intros: [],
  elims: [],

  searchAliases: ['row'],
};


export default signature;


register('row', signature);
