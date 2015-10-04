import transit from 'transit-js';
import { List, Set, OrderedMap, Map } from 'immutable';

export const writeHandlers = [
  List, transit.makeWriteHandler({
    tag: () => 'iL',
    rep: v => v.toArray(),
  }),
  Set, transit.makeWriteHandler({
    tag: () => 'iS',
    rep: v => v.toArray(),
  }),
  OrderedMap, transit.makeWriteHandler({
    tag: () => 'iO',
    rep: v => v.toArray(),
  }),
  Map, transit.makeWriteHandler({
    tag: () => 'iM',
    rep: v => v.toArray(),
  }),
];

export const readHandlers = {
  'iL': rep => List(rep),
  'iS': rep => Set(rep),
  'iO': rep => OrderedMap(rep),
  'iM': rep => Map(rep),
}
