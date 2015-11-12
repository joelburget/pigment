import React from 'react';

import deleteButtonStyle from '../styles/deleteButtonStyle';


import { POKE_HOLE } from '../messages';


export default function pokeHole(path, level) {
  const clickHandler = () => {
    this.context.signal(path, { action: [POKE_HOLE], path, level });
  };

  return (
    <button onClick={clickHandler} style={deleteButtonStyle}>
      poke hole
    </button>
  );
}
