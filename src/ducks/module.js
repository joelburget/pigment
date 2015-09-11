import { List, Record } from 'immutable';
import Immutable from 'immutable';
import transit from 'transit-js';

import { Var, Hole, Type } from '../theory/tm';
import { Lam, Arr, Binder } from '../theory/lambda';
import { Rec, Row } from '../theory/record';
import { mkRel, mkAbs } from '../theory/ref';
import {
  Module, Note, Definition, Property, Example,
  MODULE_PUBLIC, MODULE_PRIVATE
  } from '../theory/module';

import type { Ref } from '../theory/ref';
import type { Tm } from '../theory/tm';

const DEFINITION_RENAME = 'pigment/module/DEFINITION_RENAME';
const EXPRESSION_MOUSE_CLICK = 'pigment/module/EXPRESSION_MOUSE_CLICK';
const UPDATE_AT = 'pigment/module/UPDATE_AT';
const MOVE_ITEM = 'pigment/module/MOVE_ITEM';


const type = Type.singleton;


const contents = Immutable.fromJS([
  new Definition({
    name: 'goal',
    defn: new Lam(
      new Binder({ name: 'x', type }),
      new Lam(
        new Binder({ name: 'y', type }),
        type
      )
    ),
    visibility: MODULE_PUBLIC,
  }),
  new Definition({
    name: "pairer",
    defn: new Lam(
      new Binder({ name: 'x', type }),
      new Lam(
        new Binder({ name: 'y', type }),
        type
        // new Row(
        //   new Var(mkRel('..', '..', 'binder'), type),
        //   new Var(mkRel('..', 'binder'), type)
        // )
      )
    ),
    visibility: MODULE_PUBLIC,
  }),
  new Note({
    name: "about pairer",
    defn: "text of the note",
  }),
  // {
  //   name: "pairer example",
  //   defn: new Tuple(new Var('x'), new Var('y')),
  //   type: "example",
  // },
  new Property({
    name: "pairer property",
    defn: new Var(mkAbs('TODO'), type),
  }),
  new Definition({
    name: 'uses var',
    defn: new Lam(
      new Binder({ name: 'x', type }),
      new Var(mkRel('..', 'binder'), type)
    ),
    visibility: MODULE_PRIVATE,
  }),
  new Definition({
    name: "has hole",
    defn: new Lam(
      new Binder({ name: 'x', type }),
      new Hole('hole', type)
    ),
    visibility: MODULE_PRIVATE,
  }),
]);


export class WidgetState extends Record({
  module: null,
  mouseSelection: null,
}, 'widgetstate') {}


export const writeHandlers = [
  WidgetState, transit.makeWriteHandler({
    tag: () => 'widgetstate',
    rep: v => [v.module, v.mouseSelection],
  })
];


export const readHandlers = {
  'widgetstate': ([module, mouseSelection]) =>
    new WidgetState({ module, mouseSelection }),
};


const initialState = new WidgetState({
  module: new Module({
    name: 'example module',
    contents
  }),
  mouseSelection: null,
});


export default function reducer(state = initialState, action = {}) {
  switch (action.type) {
    case DEFINITION_RENAME:
      const { index, newName } = action;

      const newArr = state.contents.slice();
      newArr[index] = {
        name: newName,
        defn: newArr[index].defn,
      };

      return state.set('contents', newArr);

    case EXPRESSION_MOUSE_CLICK:
      return state.set('mouseSelection', action.path);

    case UPDATE_AT:
      const { ref, update } = action;
      return state.updateIn(ref.path, update);

    case MOVE_ITEM:
      const { beforeIx, afterIx } = action;
      return state.updateIn(['module', 'contents'], contents => {
        const item = contents.get(beforeIx);

        return contents
          .splice(beforeIx, 1)
          .splice(afterIx, 0, item);
      });

    default:
      return state;
  }
}


// TODO(joel) - I'm planning to develop this in a dangerous way at first --
// just look up a ref when you want to know about it. The dangerous part is
// that the ref could have updated without updating things that rely on it.
// Right?
export function lookupRef(state: WidgetState, ref: AbsRef): Tm {
  // this is slick. thank you records!
  return state.getIn(ref.path);
}


export function isPathHighlighted(mouseSelection: ?List<string>,
                                  path: List<string>): boolean {
  return Immutable.is(mouseSelection, path);
  // this path is highlighted if the current mouse selection is a prefix
  if (mouseSelection == null) {
    return false;
  }

  for (var i = 0; i < mouseSelection.size; i++) {
    if (mouseSelection.get(i) !== path.get(i)) {
      return false;
    }
  }

  return true;
}


// to autocomplete a hole, we need to know:
// * its type
// * its scope
// * its prefix
export function findCompletions(state: WidgetState,
                                type: Tm,
                                ref: AbsRef,
                                prefix: string): Array<Binder> {
  var matches = [];

  // walk from the root to the ref, collecting matching binders
  var currentLoc = state;
  ref.path.forEach(piece => {
    console.log('piece', piece);
    currentLoc = currentLoc.get(piece);

    if (currentLoc instanceof Lam) {
      console.log('islam');
      var binder = currentLoc.binder;
      console.log(binder.type, type);
      if (binder.type.unify(type) != null) {
        console.log('unifies');
        console.log(binder.name);
        if (binder.name.startsWith(prefix)) {
          console.log('isprefix');
          matches.push(binder);
        }
      }
    }
  });

  return matches;
}


export function isLoaded(globalState) {
  return globalState.module && globalState.module.loaded;
}


export function moveItem(beforeIx: number, afterIx: number) {
  return {
    type: MOVE_ITEM,
    beforeIx,
    afterIx,
  };
}


export function renameDefinition(index, newName) {
  return {
    type: DEFINITION_RENAME,
    index,
    newName,
  };
}


export function expressionMouseClick(path) {
  return {
    type: EXPRESSION_MOUSE_CLICK,
    path,
  };
}


export function updateAt(ref: AbsRef, update) {
  return {
    type: UPDATE_AT,
    ref,
    update,
  };
}

export function load() {
  return {
    types: [],
    promise: client => client.get('/loadWidgets'),
  };
}
