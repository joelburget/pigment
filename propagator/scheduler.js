// @flow
import type Cell from './cell';
import type Propagator from './propagator';

export default class Scheduler {
  cells: Map<number, Cell<mixed>>;
  propagators: Map<number, Propagator>;
  propagatorsDependentOnCell: Map<number, Set<number>>;
  dirtyCells: Set<number>;
  idGen: number;

  constructor() {
    this.idGen = 0;
    this.cells = new Map();
    this.propagators = new Map();
    this.propagatorsDependentOnCell = new Map();
    this.dirtyCells = new Set();
  }

  _getId() {
    return this.idGen++;
  }

  registerPropagator(
    propagator: Propagator,
    neighborCells: Array<Cell<mixed>>
  ): number {
    const propId = this._getId();
    const neighbors = neighborCells.map(cell => cell.id);

    for (let id of neighbors) {
      const set = this.propagatorsDependentOnCell.get(id);
      set.add(propId)
    }

    this.propagators.set(propId, propagator);
    return propId;
  }

  registerCell(cell: Cell<mixed>):number {
    const cellId = this._getId();
    this.cells.set(cellId, cell);
    this.propagatorsDependentOnCell.set(cellId, new Set());
    return cellId;
  }

  markDirty(id: number) {
    this.dirtyCells.add(id);
  }

  run() {
    while (this.dirtyCells.size > 0) {
      const setIter = this.dirtyCells.keys();
      const id = setIter.next().value;
      this.dirtyCells.delete(id);

      const propIds = this.propagatorsDependentOnCell.get(id);
      for (const id of propIds) {
        const propagator = this.propagators.get(id);
        propagator.run();
      }
    }
  }

  // abortProcess
}
