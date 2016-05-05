import almostEqual from 'almost-equal';
import test from 'ava';

import Scheduler from './scheduler';
import Cell from './cell';
import Propagator from './propagator';
import functionPropagator from './functionPropagator';
import makeCells from './makeCells';
import Interval, { intervalQuadratic, intervalProduct } from './interval';
import Num, { sum } from './number';
import Type, { application, arrowType, baseType } from './type';
import Nullable from './nullable';

test('getting a value from a cell', t => {
  const scheduler = new Scheduler();
  const x = new Cell(scheduler, Nullable(Num), null, 'x');

  t.is(x.content, null);
  x.addContent(2);

  scheduler.run();

  t.is(x.content, 2);
});

test('sum', t => {
  const scheduler = new Scheduler();
  const {x, y, xPlusY} = makeCells(scheduler, {
    x: [Nullable(Num), null],
    y: [Nullable(Num), null],
    xPlusY: [Nullable(Num), null],
  });

  sum(scheduler, x, y, xPlusY);
  x.addContent(2);
  y.addContent(2);

  scheduler.run();

  t.is(xPlusY.content, 4);
});

test('sum running backwards', t => {
  const scheduler = new Scheduler();
  const {x, y, xPlusY} = makeCells(scheduler, {
    x: [Nullable(Num), null],
    y: [Nullable(Num), null],
    xPlusY: [Nullable(Num), null],
  });

  sum(scheduler, x, y, xPlusY);
  x.addContent(2);
  xPlusY.addContent(4);

  scheduler.run();

  t.is(y.content, 2);
});

// h = 1/2 g t^2
class FallDurationPropagator extends Propagator {
  run() {
    const {neighbors: [t, h], scheduler} = this;
    const {g, oneHalf, tSquared, gtSquared} = makeCells(scheduler, {
      g: [Interval, Interval.bottom],
      oneHalf: [Interval, Interval.bottom],
      tSquared: [Interval, Interval.bottom],
      gtSquared: [Interval, Interval.bottom],
    });

    // XXX constant propagator?
    g.addContent([9.789, 9.832]);
    oneHalf.addContent([0.5, 0.5]);
    // tSquared = t ^ 2
    intervalQuadratic(scheduler, t, tSquared);

    // gt^2 = g * t^2
    intervalProduct(scheduler, g, tSquared, gtSquared);

    // h = 1/2 gt^2
    intervalProduct(scheduler, oneHalf, gtSquared, h);
  }
}


test('partial information', t => {
  const scheduler = new Scheduler();
  const {fallTime, buildingHeight} = makeCells(scheduler, {
    fallTime: [Interval, Interval.nonNegativeBottom],
    buildingHeight: [Interval, Interval.nonNegativeBottom],
  });

  new FallDurationPropagator(scheduler, [fallTime, buildingHeight]);
  fallTime.addContent([2.9, 3.1]);

  scheduler.run();

  const [heightMin, heightMax] = buildingHeight.content;
  t.true(almostEqual(heightMin, 41.163, 0.001));
  t.true(almostEqual(heightMax, 47.243, 0.001));
});


test('partial information flowing the other way', t => {
  const scheduler = new Scheduler();
  const {fallTime, buildingHeight} = makeCells(scheduler, {
    fallTime: [Interval, Interval.nonNegativeBottom],
    buildingHeight: [Interval, Interval.nonNegativeBottom],
  });

  new FallDurationPropagator(scheduler, [fallTime, buildingHeight]);
  buildingHeight.addContent([44.514, 47.243]);

  scheduler.run();

  const [timeMin, timeMax] = fallTime.content;
  t.true(almostEqual(timeMin, 3.009, 0.001));
  t.true(almostEqual(timeMax, 3.107, 0.001));
});


// send a number to an interval
test('adaptors', t => {
});


test('type checking / synthesis', t => {
  const scheduler = new Scheduler();

  // f : a -> b -> b -> a
  // x : Foo
  // y : Bar
  // z : ?
  // w : ?
  //
  // =>
  //
  // f : Foo -> Bar -> Bar -> Foo
  // z : Bar
  // w : Foo
  const {f, x, y, z, w} = makeCells(scheduler, {
    f: [Type, arrowType({ x: null, y: null, z: null }, null)],
    x: [Type, baseType('Foo')],
    y: [Type, baseType('Bar')],
    z: [Type, null],
    w: [Type, null],
  });

  application(scheduler, f, {x, y, z}, w);

  scheduler.run();

  t.is(f.content.args.x.name, 'Foo');
  t.is(f.content.args.y.name, 'Bar');

  // TODO
  // t.is(x.content, 'Bar');
  // t.is(w.content, 'Foo');
});


test('provenance', t => {
});
