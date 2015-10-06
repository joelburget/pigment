import transit from 'transit-js';
import { List, Record } from 'immutable';
import Immutable from 'immutable';

import isPrefix from '../util/isPrefix';

import Module, {
  Note, Definition, Property, Example,
  MODULE_PUBLIC, MODULE_PRIVATE
  } from '../aspects/module/data';

// XXX only importing here for the side effect of these registering
import Row from '../aspects/row/data';
import Label from '../aspects/label/data';
import Rec from '../aspects/record/data';
import Variant from '../aspects/variant/data';
import Lam from '../aspects/lambda/data';

import { OPEN } from '../theory/edit';
import { read as readRegistry } from '../theory/registry';
import { VARIABLE, INTRO, ELIM, Hole, Type } from '../theory/tm';
import { AbsRef } from '../theory/ref';

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
const OPEN_NEW_EDIT = 'pigment/module/OPEN_NEW_EDIT';


export class ModuleState extends Record({
  module: null,         // Module
  mouseSelection: null, // Path
  openEdit: null,       // Edit
}, 'modulestate') {}


export const writeHandlers = [
  ModuleState, transit.makeWriteHandler({
    tag: () => 'modulestate',
    rep: v => [v.module, v.mouseSelection, v.openEdit],
  }),
];


export const readHandlers = {
  'modulestate': ([module, mouseSelection, openEdit]) =>
    new ModuleState({ module, mouseSelection, openEdit }),
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


const scratchTy = new Hole(null, Type.singleton);
const scratch = new Definition({
  // TODO: 'new definition' here, 'new item' in module/view
  name: 'new definition',
  defn: new Hole('_', scratchTy),
  visibility: MODULE_PUBLIC,
  type: scratchTy,
});


const initialState = new ModuleState({
  module: new Module({
    name: 'example module',
    contents,
    scratch,
  }),
  mouseSelection: null,
  openEdit: null,
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

    // 1. make sure we have an open edit
    // 2. add to it
    case OPEN_NEW_EDIT:
      const { path, catalyst } = action;
      // XXX does catalyst have a path?
      const focus = itemGetFocus(state, path);

      // Action = {
      //   id: string;
      //   title: string;
      //   value?: any;
      // }
      //
      // Action => List<Edit>
      const edit = focus.performEdit(catalyst);

      // TODO - I think we want to be a little more sophisticated here:
      // - if an edit can be completed (closed) we should do that!
      // - there are two slightly different concepts
      //   1. opening a new edit (and the transitive closure of conflicts),
      //      which is what happens here.
      //   2. continuing an open edit (resolving conflicts). closing the last
      //      conflict should close the open edit.
      //   * though this command only necessarily does (1), it can also do (2)

      // TODO record the sequence of edits!
      var newState;

      // There's already an open edit -- add to its closure
      if (state.openEdit) {
        newState = state.openEdit.resolve(edit);

      // Open our new edit
      } else if (edit.status === OPEN) {
        newState = state.set('openEdit', edit);

      // The new edit is immediately closed
      } else {
        newState = state.setIn(path, edit.after);
      }

      return newState;

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


// Look up some definition in the module. It's possible that there'll be focus
// within the module, which we *actually* want to get.
function itemGetFocus(state: ModuleState, path: List<string>) {
  var defn = state.getIn(path);
  const { mouseSelection } = state;

  // If the mouse selection is within this definition, use the selected term
  // instead.
  if (mouseSelection && isPrefix(path, mouseSelection)) {
    return state.getIn(mouseSelection);
  } else {
    return defn.defn;
  }
}


export function getActions(state: ModuleState, path: List<string>) {
  return itemGetFocus(state, path).actions();
}


// to autocomplete a hole, we need to know:
// * its type
// * its scope
// * its prefix
export function findCompletions(state: ModuleState,
                                type: Tm,
                                ref: AbsRef,
                                prefix: string): Array<Binder> {
  let matches = [];

  try {
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
  } catch (err) {
    // TODO(joel) fix this properly by not using the fake path .type in the
    // module render.
    matches = [];
  }

  // really interesting that this uses almost no information about the actual
  // hole we're trying to fill
  const intros = readRegistry()
    .filter(cls => cls.typeClass === type.constructor)
    .toArray();
  const elims = readRegistry()
    .filter(cls => cls.form === ELIM)
    .toArray();

  return {
    variables: matches,
    intros, // invariant -- intros should have length 1
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
  };
}

export function openNewEdit(path: List<string>, catalyst: string) {
  return {
    type: OPEN_NEW_EDIT,
    catalyst,
    path,
  };
}

export function load() {
  return {
    types: [],
    promise: client => client.get('/loadWidgets'),
  };
}
