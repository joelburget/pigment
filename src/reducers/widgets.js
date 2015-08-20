import { List, Set } from 'immutable';

import {
  DEFINITION_RENAME,

  MOUSE_UP,
  EXPRESSION_MOUSE_DEPRESS,
  EXPRESSION_MOUSE_ENTER,
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

  // These two require some more explanation:
  // * they're only active when you depressed the mouse on an expression and
  //   have not yet released it.
  // * mouseDownStart points to the element you depressed the mouse on
  // * mouseDownEnd points to the element you're currently hovering
  //   - it could be nothing if you've escaped the root of this expression. at
  //     that point the highlight goes away.
  //   - it could be the same element as mouseDownStart
  mouseDownStart: null,
  mouseDownEnd: null,

  mouseDownWithin: Set(),
};


export default function widgets(state = initialState, action = {}) {
  switch (action.type) {
    case DEFINITION_RENAME:
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

    case EXPRESSION_MOUSE_DEPRESS:
      const mouseDownStart = action.element;
      const mouseDownWithin = state.mouseDownWithin.add(action.element);
      return { ...state, mouseDownStart, mouseDownWithin };

    case EXPRESSION_MOUSE_ENTER:
      const mouseDownEnd = action.element;
      return { ...state, mouseDownEnd };

    case MOUSE_UP:
      return { ...state, mouseDownWithin: Set() };

    default:
      return state;
  }
}

export function isLoaded(globalState) {
  return globalState.widgets && globalState.widgets.loaded;
}
