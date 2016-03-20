// @flow
import R from 'ramda';

import type Scheduler from './scheduler';

export type ForwardChange<A> = {
  tag: 'FORWARD_CHANGE';

  // did we change anything / gain information over the old?
  gain: boolean;

  content: A;
};

export type Contradiction = {
  tag: 'CONTRADICTION';

  errorMessage: string;

  // TODO more information - the haskell version has this data constructor:
  // `Contradiction !(HashSet Name) String`
  // names: Immutable.Set<Name>;
};

export type Change<A> = ForwardChange<A> | Contradiction;
export type Merge<A> = (left: A, right: A) => Change<A>;

export type Protocol<A> = {
  merge: Merge<A>;
};

export type CellExtra<A> = {
  name?: string;
  content?: A;
};

// A cell contains "information about a value" rather than a value per se.
//
// - https://github.com/ekmett/propagators/blob/master/src/Data/Propagator/Cell.hs
//
// The shared connection mechanism is called a "cell" and the machines they
// connect are called "propagators".
export default class Cell<A> {
  scheduler: Scheduler;
  protocol: Protocol<A>;
  name: ?string;
  content: ?A;
  neighbors: Array<Cell<mixed>>;

  constructor(
    scheduler: Scheduler,
    protocol: Protocol<A>,
    extra: CellExtra<A>
  ) {
    this.scheduler = scheduler;
    this.protocol = protocol;
    this.name = extra.name || null;
    this.content = extra.content || null;
    this.neighbors = [];
  }

  _member(cell: Cell): boolean {
    return R.contains(cell, this.neighbors);
  }

  newNeighbor(neighbor: Cell) {
    if (!this._member(neighbor)) {
      this.neighbors.push(neighbor);
      this.scheduler.alertPropagators([neighbor]);
    }
  }

  // Update the value of this cell, propagating any updates
  addContent(increment: A) {
    const answer = this.protocol.merge(this.content, increment);
    if (answer.tag === 'CONTRADICTION') {
      throw new Error('Ack! Inconsistency!\n' + answer.message);
    } else if (answer.gain) {
      this.content = answer.content;
      this.scheduler.alertPropagators(this.neighbors);
    }

    // else no change
  }
}
