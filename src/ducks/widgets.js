import { List, Set } from 'immutable';
import Immutable from 'immutable';

import { Var, Hole, Type } from '../theory/tm';
import type { Tm } from '../theory/tm';
import { Lam, Arr, Binder } from '../theory/lambda';
import { Rec, Row } from '../theory/record';
import { mkRel, mkAbs } from '../theory/ref';
import type { Ref } from '../theory/ref';

const DEFINITION_RENAME = 'redux-example/widgets/DEFINITION_RENAME';
const MOUSE_UP = 'redux-example/widgets/MOUSE_UP';
const EXPRESSION_MOUSE_DEPRESS = 'redux-example/widgets/EXPRESSION_MOUSE_DEPRESS';
const EXPRESSION_MOUSE_ENTER = 'redux-example/widgets/EXPRESSION_MOUSE_ENTER';

const type = Type.singleton;

const goal = new Arr(
  new Var(mkAbs('A'), type),
  new Arr(
    new Var(mkAbs('B', type)),
    new Row(
      new Var(mkAbs('A', type)),
      new Var(mkAbs('B', type))
    )
  )
);

const definitions = [
  {
    name: "pairer",
    defn: new Lam(
      new Binder({ name: 'x', type }),
      new Lam(
        new Binder({ name: 'y', type }),
        new Row(
          new Var(mkRel('..', '..', 'binder'), type),
          new Var(mkRel('..', 'binder'), type)
        )
      )
    ),
    type: "definition",
  },
  {
    name: "about pairer",
    defn: "text of the note",
    type: "note",
  },
  // {
  //   name: "pairer example",
  //   defn: new Tuple(new Var('x'), new Var('y')),
  //   type: "example",
  // },
  {
    name: "pairer property",
    defn: new Var(mkAbs('TODO'), type),
    type: "property",
  },
  {
    name: 'uses var',
    defn: new Lam(
      new Binder({ name: 'x', type }),
      new Var(mkRel('..', 'binder'), type)
    ),
    type: 'definition',
  },
  {
    name: "has hole",
    defn: new Lam(
      new Binder({ name: 'x', type }),
      new Hole('hole', type)
    ),
    type: "definition",
  },
];

type Note = {
  name: string;
  defn: string;
  type: 'note';
};

type Definition = {
  name: string;
  defn: Tm;
  type: 'definition';
};

type Property = {
  name: string;
  defn: Tm;
  type: 'property';
};

type Example = {
  name: string;
  defn: Tm;
  type: 'note';
};

type Info = Note | Definition | Property | Example;

type State = {
  goal: Tm;
  definitions: Array<Info>;
  mouseDownStart: ?Element;
  mouseDownEnd: ?Element;
  mouseDownWithin: Set<Element>;
};

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

export default function reducer(state, action) {
  console.log('action', action);
  console.log('before', state);
  var x = reducerHelper(state, action);
  console.log('after', x);
  return x;
}

// export default function reducer(state = initialState, action = {}) {
function reducerHelper(state = initialState, action = {}) {
  switch (action.type) {
    case '@@INIT': // XXX this is really bad

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
      console.log('depress', action.element);
      const mouseDownWithin = state.mouseDownWithin.add(action.element);
      return { ...state, mouseDownStart, mouseDownWithin };

    case EXPRESSION_MOUSE_ENTER:
      const mouseDownEnd = action.element;
      console.log('enter', action.element);
      return { ...state, mouseDownEnd };

    case MOUSE_UP:
      return { ...state, mouseDownWithin: Set() };

    default:
      return state;
  }
}


// TODO(joel) - I'm planning to develop this in a dangerous way at first --
// just look up a ref when you want to know about it. The dangerous part is
// that the ref could have updated without updating things that rely on it.
// Right?
export function lookupRef(definitions: Array<Info>, ref: AbsRef): Tm {
  var path: List<string> = ref.path;
  var entry: string = path.first();
  var tail: List<string> = path.shift();

  // TODO - make Ref into two parts: development (module) and path
  var location: Info = definitions.find(defn => defn.name === entry);

  // this is slick. thank you records!
  // TODO how to tell type system that we can't have a note here?
  return location.defn.getIn(tail);
}

export function isLoaded(globalState) {
  return globalState.widgets && globalState.widgets.loaded;
}
