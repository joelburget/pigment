import {
  DEFINITION_RENAME,

  EXPRESSION_MOUSE_DEPRESS,
  EXPRESSION_MOUSE_ENTER,

  MOUSE_UP,
} from './actionTypes';

export function renameDefinition(index, newName) {
  return {
    type: DEFINITION_RENAME,
    index,
    newName,
  };
}

export function expressionMouseDepress(element) {
  return {
    type: EXPRESSION_MOUSE_DEPRESS,
    element,
  };
}

export function expressionMouseOver(element) {
  return {
    // TODO this name is no longer accurate
    type: EXPRESSION_MOUSE_ENTER,
    element,
  };
}

export function mouseup() {
  return { type: MOUSE_UP };
}

export function load() {
  return {
    types: [
      DEFINITION_RENAME,
      EXPRESSION_MOUSE_DEPRESS,
      EXPRESSION_MOUSE_ENTER,
      MOUSE_UP,
    ],
    promise: (client) => client.get('/loadWidgets'),
  };
}
