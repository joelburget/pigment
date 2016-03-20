// @flow
import type Scheduler from './scheduler';
import type Cell from './cell';

export default class Propagator {
  scheduler: Scheduler;

  constructor(
    scheduler: Scheduler,
    neighbors: Array<Cell<mixed>>,
    todo: () => void
  ) {
    this.scheduler = scheduler;

    for (let cell of neighbors) {
      cell.newNeighbor(todo);
    }

    this.scheduler.alertPropagators([todo]);
  }
}
