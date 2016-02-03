// @flow

import React, { Component, PropTypes } from 'react';

import Firmament from '../models/Firmament';

import type { Element } from 'react';


type UndoProps = {
  globalHistory: Array<Firmament>;
  historyIndex: number;
  onUndo: () => void;
  onRedo: () => void;
};


export default class Undo extends Component {
  render(): Element {
    const { globalHistory, historyIndex, onUndo, onRedo } = this.props;

    const undoDisabled = historyIndex === 0;
    const redoDisabled = historyIndex === globalHistory.length - 1;

    const undoCount = historyIndex;
    const redoCount = globalHistory.length - historyIndex - 1;

    return (
      <div>
        <button
          disabled={undoDisabled}
          onClick={() => onUndo()}
        >
          undo ({undoCount})
        </button>
        <button
          disabled={redoDisabled}
          onClick={() => onRedo()}
        >
          redo ({redoCount})
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
  historyIndex: PropTypes.number.isRequired,
  onUndo: PropTypes.func.isRequired,
  onRedo: PropTypes.func.isRequired,
};
