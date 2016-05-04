// @flow
import R from 'ramda';

import Cell from './cell';

import type Scheduler from './scheduler';
import type {Protocol} from './cell';


type CellDescription<A> = [Protocol, A];

export default function makeCells(
  scheduler: Scheduler,
  protocols: { [key:string]: CellDescription<mixed> }
): { [key:string]: Cell<mixed> } {
  return R.mapObjIndexed(
    ([protocol, content], name) =>
      new Cell(scheduler, protocol, content, name),
    protocols
  );
}
