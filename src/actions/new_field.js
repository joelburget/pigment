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

  const newLoc = loc
    .set('data', newData)
    .setIn(['locations', name], global.holePointer);

  if (pointer === global.holePointer) {
    debugger;
  }
  return global.update(pointer, newLoc);
}


export function NewField(
  { path }: { path: Path },
  { global, signal }: GlobalContext<NewFieldSignal>
) : Element {
  return (
    <button onClick={() => handleClick(global, signal, path)}>
      New Row
    </button>
  );
}

NewField.propTypes = {
  path: PropTypes.shape({
    root: PropTypes.symbol,
    steps: PropTypes.array,
  }).isRequired,
};

NewField.contextTypes = {
  signal: PropTypes.func.isRequired,
  global: PropTypes.instanceOf(Firmament).isRequired,
};

function handleClick(
  global: Firmament,
  signal: (path: Path, signal: NewFieldSignal) => void,
  path: Path,
) : void {
  const loc = global.getPath(path);
  const name = findName(loc.data.fields, 'new row');

  console.log('started handling');
  signal(
    path,
    {
      action: NEW_FIELD,
      name,
      path,
    }
  );

  console.log('finished handling');
}
