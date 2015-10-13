// @flow

import { List } from 'immutable';

import { openNewEdit } from '../theory/edit';
import { Hole } from '../theory/tm'; // XXX this loops

import type Edit from '../theory/edit';
import type { Tm } from '../theory/tm';

export const POKE_HOLE = 'POKE_HOLE';

export const pokeHole = {
  id: POKE_HOLE,
  title: 'poke hole',
};

export function doPokeHole(here: Tm): Edit {
  return openNewEdit(
    POKE_HOLE,
    here,
    new Hole({ type: here.type }),
    List()
  );
}
