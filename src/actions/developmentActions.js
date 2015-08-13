import {
  TOOLBOX_SEARCH,
  NAME_CLICK,
} from './actionTypes';

export function load() {
  return {
    types: [TOOLBOX_SEARCH, NAME_CLICK],
  };
}
