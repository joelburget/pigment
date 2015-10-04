import transit from 'transit-js';
import { List, Set, OrderedMap, Map } from 'immutable';

export const writeHandlers = [
  List, transit.makeWriteHandler({
    tag: () => 'iL',
    rep: vec => vec.toArray(),
  }),
  Set, transit.makeWriteHandler({
    tag: () => 'iS',
    rep: vec => vec.toArray(),
  }),
  OrderedMap, transit.makeWriteHandler({
    tag: () => 'iO',
    rep: vec => vec.toArray(),
  }),
  Map, transit.makeWriteHandler({
    tag: () => 'iM',
    rep: vec => vec.toArray(),
  }),
];

export const readHandlers = {
  'iL': rep => List(rep),
  'iS': rep => Set(rep),
  'iO': rep => OrderedMap(rep),
  'iM': rep => Map(rep),
};
