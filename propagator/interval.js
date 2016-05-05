import functionPropagator from './functionPropagator';

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

export function merge(
  content: Interval,
  increment: Interval
): Change<Interval> {
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
      content: increment,
    };
  } else if (emptyInterval(newRange)) {
    return {
      tag: 'CONTRADICTION',
      message: 'interval merge contradiction: ' + JSON.stringify(content) + " doesn't merge with " + JSON.stringify(increment),
    };
  } else {
    return {
      tag: 'FORWARD_CHANGE',
      gain: true,
      content: newRange,
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
  return [Math.sqrt(low), Math.sqrt(high)];
}

const intervalMultiplier = functionPropagator(mulInterval);
const intervalDivider = functionPropagator(divInterval);
const intervalSquarer = functionPropagator(squareInterval);
const intervalSqrter = functionPropagator(sqrtInterval);

export function intervalProduct(scheduler, x, y, total) {
  intervalMultiplier(scheduler, [x, y, total]);
  intervalDivider(scheduler, [total, x, y]);
  intervalDivider(scheduler, [total, y, x]);
}

export function intervalQuadratic(scheduler, x, x2) {
  intervalSquarer(scheduler, [x, x2]);
  intervalSqrter(scheduler, [x2, x]);
}

export const bottom = [Number.NEGATIVE_INFINITY, Number.POSITIVE_INFINITY];
export const nonNegativeBottom = [0, Number.POSITIVE_INFINITY];

export default {
  merge,
  bottom,
  nonNegativeBottom,
  times: intervalMultiplier,
  division: intervalDivider,
  square: intervalSquarer,
  sqrt: intervalSqrter,
};
