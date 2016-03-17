import R from 'ramda';

import { functionPropagator } from './index';

export type Interval = [number, number];

export function intersectIntervals(
  [l0, l1]: Interval,
  [r0, r1]: Interval
): Interval {
  return [
    Math.max(l0, r0),
    Math.min(l1, r1),
  ];
}

export function intervalEqual(
  [l0, l1]: Interval,
  [r0, r1]: Interval
): boolean {
  return l0 === r0 && l1 === r1;
}

export function emptyInterval([low, high]: Interval): boolean {
  return low > high;
}

// TODO always start with the infinite interval, rather than null
export function merge(
  content: Interval,
  increment: Interval
): Change<Interval> {
  if (content == null || increment == null) {
    const content = content || increment;
    return {
      tag: 'FORWARD_CHANGE',
      gain: content != null,
      content,
    };
  }

  const newRange = intersectIntervals(content, increment);
  if (intervalEqual(newRange, content)) {
    return {
      tag: 'FORWARD_CHANGE',
      gain: false,
      content,
    };
  } else if (intervalEqual(newRange, increment)) {
    return {
      tag: 'FORWARD_CHANGE',
      gain: true,
      increment,
    };
  } else if (emptyInterval(newRange)) {
    return {
      tag: 'CONTRADICTION',
      message: 'interval merge contradiction',
    };
  } else {
    return {
      tag: 'FORWARD_CHANGE',
      gain: true,
      newRange,
    };
  }
}

function mulInterval([xLow, xHigh], [yLow, yHigh]): Interval {
  return [xLow * yLow, xHigh * yHigh];
}

function divInterval(x: Interval, [yLow, yHigh]: Interval): Interval {
  return mulInterval(x, [1 / yHigh, 1 / yLow]);
}

function squareInterval([low, high]: Interval): Interval {
  return [low * low, high * high];
}

function sqrtInterval([low, high]: Interval): Interval {
  return [Math.sqrt(low, low), Math.sqrt(high, high)];
}

const intervalMultiplier = functionPropagator(R.__, mulInterval);
const intervalDivider = functionPropagator(R.__, divInterval);
const intervalSquarer = functionPropagator(R.__, squareInterval);
const intervalSqrter = functionPropagator(R.__, sqrtInterval);

export function intervalProduct(scheduler, x, y, total) {
  intervalMultiplier(scheduler, [x, y, total]);
  intervalDivider(scheduler, [total, x, y]);
  intervalDivider(scheduler, [total, y, x]);
}

export function intervalQuadratic(scheduler, x, x2) {
  intervalSquarer(scheduler, [x, x2]);
  intervalSqrter(scheduler, [x2, x]);
}

export default {
  merge,
  times: intervalMultiplier,
  division: intervalDivider,
  square: intervalSquarer,
  sqrt: intervalSqrter,
};
