import almostEqual from 'almost-equal';
import test from 'ava';
import R from 'ramda';

import Scheduler from './scheduler';
import { Cell, Propagator, compoundPropagator, functionPropagator, makeCells } from './index';
import { intervalMerge, intervalQuadratic, intervalProduct } from './interval';

function numberMerger(x: ?number, y: ?number): Change<number> {
  if (x == null || y == null) {
    const content = x || y;
    return {
      tag: 'FORWARD_CHANGE',
      gain: content != null,
      content,
    };
  } else if (x === y) {
    return {
      tag: 'FORWARD_CHANGE',
      gain: false,
      content: x,
    };
  } else {
    return {
      tag: 'CONTRADICTION',
      message: 'number merge contradiction: ' + x + ' /= ' + y,
    };
  }
}

test('getting a value from a cell', t => {
  const scheduler = new Scheduler();
  const x = new Cell(scheduler, numberMerger);

  t.is(x.content, null);
  x.addContent(2);

  scheduler.run();

  t.is(x.content, 2);
});

const adder = functionPropagator(R.__, R.add);
const subtractor = functionPropagator(R.__, R.subtract);

function sum(scheduler, x, y, total) {
  adder(scheduler, [x, y, total]);
  subtractor(scheduler, [total, x, y]);
  subtractor(scheduler, [total, y, x]);
}

test('adder', t => {
  const scheduler = new Scheduler();
  const [x, y, xPlusY] =
    makeCells(scheduler, [numberMerger, numberMerger, numberMerger]);

  sum(scheduler, x, y, xPlusY);
  x.addContent(2);
  y.addContent(2);

  scheduler.run();

  t.is(xPlusY.content, 4);
});

test('running backwards', t => {
  const scheduler = new Scheduler();
  const [x, y, xPlusY] =
    makeCells(scheduler, [numberMerger, numberMerger, numberMerger]);

  sum(scheduler, x, y, xPlusY);
  x.addContent(2);
  xPlusY.addContent(4);

  scheduler.run();

  t.is(y.content, 2);
});

// h = 1/2 g t^2
function fallDuration(scheduler, t, h) {
  return compoundPropagator(scheduler, [t, h], () => {
    const [g, oneHalf, tSquared, gtSquared] =
      makeCells(scheduler, [intervalMerge, intervalMerge, intervalMerge, intervalMerge]);

    // XXX constant propagator?
    g.addContent([9.789, 9.832]);
    oneHalf.addContent([0.5, 0.5]);
    intervalQuadratic(scheduler, t, tSquared);
    intervalProduct(scheduler, g, tSquared, gtSquared);
    intervalProduct(scheduler, oneHalf, gtSquared, h);
  });
}


test('partial information', t => {
  const scheduler = new Scheduler();
  const [fallTime, buildingHeight] =
    makeCells(scheduler, [intervalMerge, intervalMerge]);

  fallDuration(scheduler, fallTime, buildingHeight);
  fallTime.addContent([2.9, 3.1]);

  const [heightMin, heightMax] = buildingHeight.content;
  t.true(almostEqual(heightMin, 41.163, 0.001));
  t.true(almostEqual(heightMax, 47.243, 0.001));
});


test('partial information flowing the other way', t => {
  const scheduler = new Scheduler();
  const [fallTime, buildingHeight] =
    makeCells(scheduler, [intervalMerge, intervalMerge]);

  fallDuration(scheduler, fallTime, buildingHeight);
  buildingHeight.addContent([44.514, 47.243]);

  const [timeMin, timeMax] = fallTime.content;
  t.true(almostEqual(timeMin, 3.009, 0.001));
  t.true(almostEqual(timeMax, 3.107, 0.001));
});
