import keymirror from 'keymirror';

export const messages = keymirror({
  SET_FIELD: null,
  REMOVE_FIELD: null,
  SET_DOCUMENTATION: null,
  UNIFY: null,
  MAKE_DEFINITION: null,
  FILL_HOLE: null,
});

export class Ty {
  receiveSignal(global) {
    return global;
  }
}
