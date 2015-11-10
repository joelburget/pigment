export const NEW_GADGET = 'NEW_GADGET';
export const NEW_SLOT = 'NEW_SLOT';
export const REMOVE_SLOT = 'REMOVE_SLOT';

export function newGadget(name = '') {
  return {
    type: NEW_GADGET,
    name,
  };
}

export function newSlot(path, name) {
  return {
    type: NEW_SLOT,
    path,
    name,
  };
}

export function removeSlot(path) {
  return {
    type: REMOVE_SLOT,
    path,
  };
}
