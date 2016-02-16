// @flow

import React from 'react';

import Firmament from '../models/Firmament';

import type { Element } from 'react';


type UndoProps = {
  globalHistory: Array<Firmament>;
  historyIndex: number;
  onUndo: () => void;
  onRedo: () => void;
};


export default function Undo(
  { globalHistory, historyIndex, onUndo, onRedo }: UndoProps
): Element {
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
