/* eslint id-length: 0 */
import transit from 'transit-js';

import { FreeVar, BoundVar } from './ref';
import { Type, Var, Hole } from './tm';
import Edit from './edit';
import Relation from './relation';

export const writeHandlers = [

  Relation, transit.makeWriteHandler({
    tag: () => 'relation',
    rep: v => [v.type, v.subject, v.object],
  }),

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
  FreeVar, transit.makeWriteHandler({
    tag: () => 'absref',
    rep: v => v.path,
  }),
  BoundVar, transit.makeWriteHandler({
    tag: () => 'relref',
    rep: v => v.path,
  }),

];


export const readHandlers = {

  'relation': ([type, subject, object]) =>
    new Relation({ type, subject, object }),

  'edit': ([status, world, catalyst, closure]) =>
    new Edit({ status, world, catalyst, closure }),

  // tm
  'type': () => Type.singleton,
  'hole': ([name, type]) => new Hole({ name, type }),
  'var': ([ref, type]) => new Var({ ref, type }),

  // ref
  'absref': path => new FreeVar({ path }),
  'relref': path => new BoundVar({ path }),

};
