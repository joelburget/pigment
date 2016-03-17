// @flow
// import Immutable from 'immutable';
import R from 'ramda';

import type Scheduler from './scheduler';

type ForwardChange<A> = {
  tag: 'FORWARD_CHANGE';

  // did we change anything / gain information over the old?
  gain: boolean;

  content: A;
};

type Contradiction = {
  tag: 'CONTRADICTION';

  errorMessage: string;

  // TODO more information - the haskell version has this data constructor:
  // `Contradiction !(HashSet Name) String`
  // names: Immutable.Set<Name>;
};

type Change<A> = ForwardChange<A> | Contradiction;

// A cell contains "information about a value" rather than a value per se.
//
// - https://github.com/ekmett/propagators/blob/master/src/Data/Propagator/Cell.hs
//
// The shared connection mechanism is called a "cell" and the machines they
// connect are called "propagators".
export class Cell<A> {
  mergeStrategy: (left: A, right: A) => Change<A>;

  constructor(
    scheduler: Scheduler,
    mergeStrategy: (left: A, right: A) => Change<A>
  ) {
    this.scheduler = scheduler;
    this.mergeStrategy = mergeStrategy;
    this.neighbors = [];
    this.content = null;
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
    const answer = this.mergeStrategy(this.content, increment);
    if (answer.tag === 'CONTRADICTION') {
      throw new Error('Ack! Inconsistency!\n' + answer.message);
    } else if (answer.gain) {
      this.content = answer.content;
      this.scheduler.alertPropagators(this.neighbors);
    }

    // else no change
  }
}

export class Propagator {
  scheduler: Scheduler;

  constructor(
    scheduler: Scheduler,
    neighbors: Array<Cell>,
    todo: () => void
  ) {
    this.scheduler = scheduler;

    for (let cell of neighbors) {
      cell.newNeighbor(todo);
    }

    this.scheduler.alertPropagators([todo]);
  }
}

export function compoundPropagator(
  scheduler: Scheduler,
  neighbors: Array<Cell<mixed>>,
  toBuild: Function
): Propagator {
  // XXX understand this
  let done = false;
  function test() {
    if (!done && !R.all(x => x.content == null, neighbors)) {
      done = true;
      toBuild();
    }
  }

  return new Propagator(scheduler, neighbors, test);
}

// Ensures that if any cell contents are still `null`, the result is `null`.
//
// This does *not* build a propagator.
//
// "lift-to-cell-contents"
const liftToCellContents = R.curry(function liftToCellContents_(
  f: Function,
  args: Array<mixed>
): mixed {
  return R.any(x => x == null, args) ? null : R.apply(f, args);
});

// "function->propagator-constructor"
export const functionPropagator = R.curry(function functionPropagator_(
  scheduler: Scheduler,
  f: Function,
  cells: Array<Cell<mixed>>
): Propagator {
  const output = R.last(cells);
  const inputs = R.init(cells);
  const liftedF = liftToCellContents(f);

  return new Propagator(
    scheduler,
    inputs,
    () => output.addContent(
      liftedF(inputs.map(input => input.content))
    )
  );
});

export function makeCells(scheduler: Scheduler, mergers): Array<Cell<mixed>> {
  return mergers.map(merger => new Cell(scheduler, merger));
}
