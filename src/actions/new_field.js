// @flow
import React, { PropTypes } from 'react';

import Firmament from '../models/Firmament';
import { NEW_FIELD } from '../messages';
import findName from '../utils/findName';

import type { Element } from 'react';

import type { Path } from '../models/Firmament';
import type { GlobalContext, NewFieldSignal } from '../messages';


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
