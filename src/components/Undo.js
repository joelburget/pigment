// @flow

import React, { Component, PropTypes } from 'react';

import Firmament from '../models/Firmament';

import type { Element } from 'react';

export default class Undo extends Component {
  render(): Element {
    const { globalHistory, onUndo } = this.props;
    const disabled = globalHistory.length === 1;

    return (
      <div>
        <button
          disabled={disabled}
          onClick={() => onUndo()}>
          undo
        </button>
      </div>
    );
  }
}

Undo.propTypes = {
  globalHistory:
    PropTypes.arrayOf(
      PropTypes.instanceOf(Firmament)
    ).isRequired,
  onUndo: PropTypes.func.isRequired,
};
