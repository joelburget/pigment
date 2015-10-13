import { Set } from 'immutable';

import type Relation from '../theory/relation';


const initialState = Set();


const INSERT_RELATION = 'pigment/relation/INSERT_RELATION';


export default function reducer(state = initialState, action = {}) {
  switch (action.type) {
    case INSERT_RELATION:
      return state.add(action.relation);

    default:
      return state;
  }
}


// query the relation store for all relations with either endpoint at this
// location
export function query(state, path) {
  return state.filter(({ subject, object }) => {
    return subject === path || object === path;
  });
}


export function insertRelation(relation: Relation) {
  return {
    type: INSERT_RELATION,
    relation,
  };
}
