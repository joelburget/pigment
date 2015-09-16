import transit from 'transit-js';
import { List, Record } from 'immutable';
import Immutable from 'immutable';

import {
  Module, Note, Definition, Property, Example,
  MODULE_PUBLIC, MODULE_PRIVATE
  } from '../aspects/module/data';

import Lam from '../aspects/lambda/data';
import { read as readRegistry } from '../theory/registry';
import { VARIABLE, INTRO, ELIM, Hole, Type } from '../theory/tm';

// import { Var, Hole, Type } from '../theory/tm';
// import { Rec, Row } from '../theory/record';
// import { mkRel, mkAbs } from '../theory/ref';

import type { Ref } from '../theory/ref';
import type { Tm } from '../theory/tm';

const DEFINITION_RENAME = 'pigment/module/DEFINITION_RENAME';
const EXPRESSION_MOUSE_CLICK = 'pigment/module/EXPRESSION_MOUSE_CLICK';
const UPDATE_AT = 'pigment/module/UPDATE_AT';
const MOVE_ITEM = 'pigment/module/MOVE_ITEM';
const ADD_NEW = 'pigment/module/ADD_NEW';
const FILL_HOLE = 'pigment/module/FILL_HOLE';


export class ModuleState extends Record({
  module: null,
  mouseSelection: null,
}, 'modulestate') {}


export const writeHandlers = [
  ModuleState, transit.makeWriteHandler({
    tag: () => 'modulestate',
    rep: v => [v.module, v.mouseSelection],
  }),
];


export const readHandlers = {
  'modulestate': ([module, mouseSelection]) =>
    new ModuleState({ module, mouseSelection }),
};


// const type = Type.singleton;


const contents = Immutable.fromJS([
  // new Definition({
  //   name: 'goal',
  //   defn: new Lam(
  //     new Binder({ name: 'x', type }),
  //     new Lam(
  //       new Binder({ name: 'y', type }),
  //       type
  //     )
  //   ),
  //   visibility: MODULE_PUBLIC,
  // }),
  // new Definition({
  //   name: "pairer",
  //   defn: new Lam(
  //     new Binder({ name: 'x', type }),
  //     new Lam(
  //       new Binder({ name: 'y', type }),
  //       type
  //       // new Row(
  //       //   new Var(mkRel('..', '..', 'binder'), type),
  //       //   new Var(mkRel('..', 'binder'), type)
  //       // )
  //     )
  //   ),
  //   visibility: MODULE_PUBLIC,
  // }),
  // new Note({
  //   name: "about pairer",
  //   defn: "text of the note",
  // }),
  // new Example({
  //   name: "pairer example",
  //   // defn: new Tuple(new Var('x'), new Var('y')),
  //   defn: type,
  //   type: "example",
  // }),
  // new Property({
  //   name: "pairer property",
  //   // defn: new Var(mkAbs('TODO'), type),
  //   defn: type,
  // }),
  // new Definition({
  //   name: 'uses var',
  //   defn: new Lam(
  //     new Binder({ name: 'x', type }),
  //     new Var(mkRel('..', 'binder'), type)
  //   ),
  //   visibility: MODULE_PRIVATE,
  // }),
  // new Definition({
  //   name: "has hole",
  //   defn: new Lam(
  //     new Binder({ name: 'x', type }),
  //     new Hole('hole', type)
  //   ),
  //   visibility: MODULE_PRIVATE,
  // }),
]);


const scratch = new Definition({
  name: 'new definition',
  defn: new Hole(
    '_',
    Type.singleton
  ),
  visibility: MODULE_PUBLIC,
});


const initialState = new ModuleState({
  module: new Module({
    name: 'example module',
    contents,
    scratch,
  }),
  mouseSelection: null,
});


export default function reducer(state = initialState, action = {}) {
  switch (action.type) {
    case DEFINITION_RENAME:
      {
        const { path, newName } = action;

        // eg ['module', 'contents', index, 'name']
        return state.setIn(path.push('name'), newName);
      }

    case EXPRESSION_MOUSE_CLICK:
      return state.set('mouseSelection', action.path);

    case UPDATE_AT:
      const { ref, update } = action;
      return state.updateIn(ref.path, update);

    case MOVE_ITEM:
      return state;

      // const { beforeIx, afterIx } = action;
      // return state.updateIn(['module', 'contents'], contents => {
      //   const item = contents.get(beforeIx);

      //   return contents
      //     .splice(beforeIx, 1)
      //     .splice(afterIx, 0, item);
      // });

    case ADD_NEW:
      // TODO this only applies to definitions
      const { type, name, visibility } = action.payload;

      return state
        .updateIn(['module', 'contents'],
                  contents => contents.push(state.module.scratch))
        .setIn(['module', 'scratch'], scratch);

    case FILL_HOLE:
      {
        const { path, itemType, category, item } = action;

        // the item we're going to fill the hole with. not quite the same as the
        // item we get from the action because when it's an intro or elimination
        // form that item is a class
        var fillItem;

        if (category === VARIABLE) {
          fillItem = item;
        } else if (category === INTRO) {
          // need a default value to fill the hole with
          // - we need a protocol for defaults

          // in this case item is class
          fillItem = item.fillHole(itemType);
        } else if (category === ELIM) {
          fillItem = item.fillHole(itemType);
        }

        return state.setIn(path, fillItem);
      }

    default:
      return state;
  }
}


// TODO(joel) - I'm planning to develop this in a dangerous way at first --
// just look up a ref when you want to know about it. The dangerous part is
// that the ref could have updated without updating things that rely on it.
// Right?
export function lookupRef(state: ModuleState, ref: AbsRef): Tm {
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
export function findCompletions(state: ModuleState,
                                type: Tm,
                                ref: AbsRef,
                                prefix: string): Array<Binder> {
  var matches = [];

  // walk from the root to the ref, collecting matching binders
  var currentLoc = state;
  ref.path.forEach(piece => {
    currentLoc = currentLoc.get(piece);

    if (currentLoc instanceof Lam) {
      var binder = currentLoc.binder;
      if (binder.type.unify(type) != null) {
        if (binder.name.startsWith(prefix)) {
          matches.push(binder);
        }
      }
    }
  });

  // find forms that could match this thing. ~using slots!!~
  // scratch that slots thing... really interesting that this uses almost no
  // information about the actual hole we're trying to fill
  const intro = readRegistry()
    .filter(cls => cls === type.constructor)
    .toArray();
  const elims = readRegistry()
    .filter(cls => cls.form === ELIM)
    .toArray();

  return {
    variables: matches,
    intros: intro, // invariant -- intros should have length 1
    elims,
  };
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


export function renameDefinition(path, newName) {
  return {
    type: DEFINITION_RENAME,
    path,
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

export function addNew(payload) {
  return { type: ADD_NEW, payload };
}

export function fillHole(path, itemType, category, item) {
  return {
    type: FILL_HOLE,
    path,
    itemType,
    category,
    item,
  }
}

export function load() {
  return {
    types: [],
    promise: client => client.get('/loadWidgets'),
  };
}
