import React from 'react';

import deleteButtonStyle from '../styles/deleteButtonStyle';


export const POKE_HOLE = Symbol('poke hole');


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
