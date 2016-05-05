import R from 'ramda';

import functionPropagator from './functionPropagator';

function merge(x: ?number, y: ?number): Change<number> {
  if (x === y) {
    return {
      tag: 'FORWARD_CHANGE',
      gain: false,
      content: x,
    };
  } else {
    return {
      tag: 'CONTRADICTION',
      message: 'number merge contradiction: ' + JSON.stringify(x) + ' /= ' + JSON.stringify(y),
    };
  }
}

const adder = functionPropagator(R.add);
const subtractor = functionPropagator(R.subtract);

export function sum(
  scheduler: Scheduler,
  x: Cell<number>,
  y: Cell<number>,
  total: Cell<number>
) {
  adder(scheduler, [x, y, total]);
  subtractor(scheduler, [total, x, y]);
  subtractor(scheduler, [total, y, x]);
}

export default {
  merge,
  sum,
};
