// @flow
import React, { PropTypes } from 'react';

import { POKE_HOLE } from '../messages';
import deleteButtonStyle from '../styles/deleteButtonStyle';

import type { Element } from 'react';

import type { PokeHoleSignal } from '../messages';
import type { Path } from '../models/Firmament';


export default function PokeHole(
  { path }: { path: Path },
  { signal }: { signal: (path: Path, sig: PokeHoleSignal) => void }
  ) : Element {
  const clickHandler = () => {
    signal(path, { action: POKE_HOLE, path });
  };

  return (
    <button onClick={clickHandler} style={deleteButtonStyle}>
      poke hole
    </button>
  );
}

PokeHole.contextTypes = {
  signal: PropTypes.func.isRequired,
};
