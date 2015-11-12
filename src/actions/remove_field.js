import React from 'react';

import deleteButtonStyle from '../styles/deleteButtonStyle';

import { REMOVE_FIELD } from '../messages';

export function removeField(path, key) {
  const clickHandler = () => {
    this.context.signal(path, { action: REMOVE_FIELD, name: key, path });
  };

  return (
    <button onClick={clickHandler} style={deleteButtonStyle}>
      delete
    </button>
  );
}
