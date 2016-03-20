// @flow
import R from 'ramda';

import Cell from './cell';
import Propagator from './propagator';

import type Scheduler from './scheduler';

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

// TODO: take initial value for all cells
type CellDescription<A> = Protocol | [Protocol, A];

export function makeCells(
  scheduler: Scheduler,
  protocols: { [key:string]: CellDescription<mixed> }
): { [key:string]: Cell<mixed> } {
  return R.mapObjIndexed(
    (desc, name) => {
      if (Array.isArray(desc)) {
        const [ protocol, content ] = desc;
        return new Cell(scheduler, protocol, { name, content });
      } else {
        return new Cell(scheduler, desc, { name });
      }
    },
    protocols
  );
}
