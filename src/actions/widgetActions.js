import {
  WIDGET_LOAD,
  WIDGET_LOAD_SUCCESS,
  WIDGET_LOAD_FAIL,
  DEFINITION_RENAME,
} from './actionTypes';

export function renameDefinition(index, newName) {
  return {
    type: DEFINITION_RENAME,
    index,
    newName,
  };
}

export function load() {
  return {
    types: [WIDGET_LOAD, WIDGET_LOAD_SUCCESS, WIDGET_LOAD_FAIL, DEFINITION_RENAME],
    promise: (client) => client.get('/loadWidgets')
  };
}
