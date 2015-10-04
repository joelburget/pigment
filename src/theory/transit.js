import transit from 'transit-js';

import { AbsRef, RelRef } from './ref';
import { Type, Var, Hole } from './tm';
import Edit from './edit';

export const writeHandlers = [

  Edit, transit.makeWriteHandler({
    tag: () => 'edit',
    rep: v => [v.status, v.world, v.catalyst, v.closure],
  }),

  // tm
  Type, transit.makeWriteHandler({
    tag: () => 'type',
    rep: () => [],
    stringRep: 'ty',
  }),
  Hole, transit.makeWriteHandler({
    tag: () => 'hole',
    rep: v => [v.name, v.type],
  }),
  Var, transit.makeWriteHandler({
    tag: () => 'var',
    rep: v => [v.ref, v.type],
  }),

  // ref
  AbsRef, transit.makeWriteHandler({
    tag: () => 'absref',
    rep: v => v.path,
  }),
  RelRef, transit.makeWriteHandler({
    tag: () => 'relref',
    rep: v => v.path,
  }),

];


export const readHandlers = {

  'edit': ([status, world, catalyst, closure]) =>
    new Edit({ status, world, catalyst, closure }),

  // tm
  'type': () => Type.singleton,
  'hole': rep => new Hole(rep[0], rep[1]),
  'var': rep => new Var(rep[0], rep[1]),

  // ref
  'absref': path => new AbsRef({ path }),
  'relref': path => new RelRef({ path }),

};
