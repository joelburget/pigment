// @flow

import { List } from 'immutable';

import { openNewEdit } from '../theory/edit';
import { Hole } from '../theory/tm'; // XXX this loops

export const POKE_HOLE = 'POKE_HOLE';

export const pokeHole = {
  id: POKE_HOLE,
  title: 'poke hole',
};

export function doPokeHole(here) {
  return openNewEdit(
    POKE_HOLE,
    here,
    new Hole(null, here.type),
    List()
  );
}
