import { List } from 'immutable';

import {
  WIDGET_LOAD,
  WIDGET_LOAD_SUCCESS,
  WIDGET_LOAD_FAIL,
  DEFINITION_RENAME,
} from '../actions/actionTypes';

import { mkLam, mkTuple, mkVar, mkPi, mkSigma, mkHole } from '../theory/tm';

const goal = mkPi(mkVar('A'), mkPi(mkVar('B'), mkSigma(mkVar('A'), mkVar('B'))));

const definitions = [
  {
    name: "pairer",
    defn: mkLam('x', mkLam('y', mkTuple(mkVar('x'), mkVar('y')))),
    type: "definition",
  },
  {
    name: "about pairer",
    defn: "text of the note",
    type: "note",
  },
  {
    name: "pairer example",
    defn: mkTuple(mkVar('x'), mkVar('y')),
    type: "example",
  },
  {
    name: "pairer property",
    defn: mkVar('TODO'),
    type: "property",
  },
  {
    name: "has hole",
    defn: mkLam('x', mkHole('hole')),
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
