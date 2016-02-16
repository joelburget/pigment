// @flow
import Firmament from '../models/Firmament';

import type { NewFieldSignal } from '../messages';


export function handler(
  global: Firmament,
  signal: NewFieldSignal
): Firmament {
  const { name, path } = signal;
  const pointer = global.followPath(path);
  const loc = global.getLocation(pointer);
  const newData = loc.data.update('fields', fields => fields.push(name));

  const holeSubLoc = {
    tag: 'IMMEDIATE',
    location: global.holePointer,
  };

  const newLoc = loc
    .set('data', newData)
    .setIn(['locations', name], holeSubLoc);

  if (pointer === global.holePointer) {
    debugger;
  }
  return global.update(pointer, newLoc);
}
