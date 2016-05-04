// @flow
import type Scheduler from './scheduler';
import type Cell from './cell';

export default class Propagator {
  scheduler: Scheduler;
  neighbors: Array<Cell<mixed>>;

  constructor(
    scheduler: Scheduler,
    neighbors: Array<Cell<mixed>>,
    // instructions for how to construct this propagator network on demand,
    // only if some neighbor actually has a value
  ) {
    this.scheduler = scheduler;
    this.scheduler.registerPropagator(this, neighbors);
    this.neighbors = neighbors;
  }

  run() {
    throw new Error('propagator run not implemented!');
  }
}
