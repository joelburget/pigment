import keymirror from '../utils/symbol-keymirror';

export const messages = keymirror({
  SET_FIELD: null,
  REMOVE_FIELD: null,
  SET_DOCUMENTATION: null,
  MAKE_DEFINITION: null,
  FILL_HOLE: null,

  // eliminator stuff
  UNIFY: null,
  STEP: null,
});

// TODO - drop?
export class Ty {
  receiveSignal(global) {
    return global;
  }
}
