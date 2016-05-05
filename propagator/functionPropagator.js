// @flow
import R from 'ramda';

import Propagator from './propagator';

import type Cell from './cell';
import type Scheduler from './scheduler';

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

class FunctionPropagator extends Propagator {
  scheduler: Scheduler;
  neighbors: Array<Cell<mixed>>;
  f: Function;

  constructor(
    scheduler: Scheduler,
    neighbors: Array<Cell<mixed>>,
    f: Function
  ) {
    super(scheduler, neighbors);
    this.f = f;
    this.inputs = R.init(neighbors);
    this.output = R.last(neighbors);
  }

  run() {
    const {f, inputs, output} = this;
    const liftedF = liftToCellContents(f);
    output.addContent(liftedF(inputs.map(input => input.content)));
  }
}

// "function->propagator-constructor"
//
// Lift a function over these to a propagator network. This is returns a
// directional propagator.
const functionPropagator = R.curry(function functionPropagator_(
  f: Function,
  scheduler: Scheduler,
  // TODO separate inputs and output
  cells: Array<Cell<mixed>>
): Propagator {
  return new FunctionPropagator(scheduler, cells, f);
});

export default functionPropagator;
