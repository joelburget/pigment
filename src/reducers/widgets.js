import { List } from 'immutable';

import {
  WIDGET_LOAD,
  WIDGET_LOAD_SUCCESS,
  WIDGET_LOAD_FAIL,
  DEFINITION_RENAME,
} from '../actions/actionTypes';

import { EVar, Hole } from '../theory/tm';
import { Lam, Pi, } from '../theory/lambda';
import { Tuple, Sigma } from '../theory/tuple';

const goal = new Pi(
  new EVar('A'),
  new Pi(new EVar('B'),
       new Sigma(new EVar('A'),
               new EVar('B'))));

const definitions = [
  {
    name: "pairer",
    defn: new Lam('x',
                  new Lam('y',
                          new Tuple(new EVar('x'),
                                    new EVar('y')))),
    type: "definition",
  },
  {
    name: "about pairer",
    defn: "text of the note",
    type: "note",
  },
  {
    name: "pairer example",
    defn: new Tuple(new EVar('x'), new EVar('y')),
    type: "example",
  },
  {
    name: "pairer property",
    defn: new EVar('TODO'),
    type: "property",
  },
  {
    name: "has hole",
    defn: new Lam('x', new Hole('hole')),
    type: "definition",
  },
];

const initialState = {
  goal,
  definitions,
};


export default function widgets(state = initialState, action = {}) {
  switch (action.type) {
    case DEFINITION_RENAME:
      console.log("reducer", action);
      const { index, newName } = action;

      const newArr = state.definitions.slice();
      newArr[index] = {
        name: newName,
        defn: newArr[index].defn,
      };

      return {
        ...state,
        definitions: newArr,
      };
    default:
      return state;
  }
}

export function isLoaded(globalState) {
  return globalState.widgets && globalState.widgets.loaded;
}
