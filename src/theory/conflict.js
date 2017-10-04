// @flow
import { List, Record } from 'immutable';
import invariant from 'invariant';

import type Edit, { Action } from './edit';


const ConflictShape = Record({
  left: null,
  right: null,
});


const TAKE_LEFT = 'TAKE_LEFT';
const TAKE_RIGHT = 'TAKE_RIGHT';


export default class Conflict extends ConflictShape {

  actions(): List<Action> {
    return List([
      {
        title: 'take left',
        id: TAKE_LEFT,
      },
      {
        title: 'take right',
        id: TAKE_RIGHT,
      },
    ]);
  }

  performEdit(id: string): Edit {
    invariant(
      id === TAKE_LEFT || id === TAKE_RIGHT,
      'Conflict only knows TAKE_LEFT and TAKE_RIGHT'
    );

    return {
      TAKE_LEFT: this.left,
      TAKE_RIGHT: this.right,
    }[id];
  }

}
