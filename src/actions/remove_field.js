// @flow
import React, { PropTypes } from 'react';

import { REMOVE_FIELD } from '../messages';
import deleteButtonStyle from '../styles/deleteButtonStyle';

import type { Element } from 'react';

import type { RemoveFieldSignal } from '../messages';
import type Firmament, { Path } from '../models/Firmament';


export function DeleteButton(
  { path, name }: { path: Path, name: string },
  { signal }: { signal: (path: Path, sig: RemoveFieldSignal) => void }
  ) : Element {
  const clickHandler = () => {
    signal(path, { action: REMOVE_FIELD, name, path });
  };

  return (
    <button onClick={clickHandler} style={deleteButtonStyle}>
      delete
    </button>
  );
}

DeleteButton.propTypes = {
  path: PropTypes.shape({
    root: PropTypes.symbol,
    steps: PropTypes.array,
  }).isRequired,
  name: PropTypes.string.isRequired,
};

DeleteButton.contextTypes = {
  signal: PropTypes.func.isRequired,
};


export function handler(
  global: Firmament,
  signal: RemoveFieldSignal
): Firmament {
  const { name, path } = signal;
  const pointer = global.followPath(path);
  const loc = global.getPath(path);
  const loc_ = loc
    .updateIn(['data', 'fields'], fields => {
      return fields.filter(field => field !== name);
    })
    .deleteIn(['locations', name]);

  // TODO garbage collect field?
  return global.setIn(['memory', pointer], loc_);
}
