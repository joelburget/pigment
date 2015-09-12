import transit from 'transit-js';

import { AbsRef, RelRef } from './ref';
import { Type, Var, Hole, } from './tm';
import { Binder, Lam, App, Arr } from './lambda';
import { Label, Rec, RowKind, Row, SelectRow, ExtendRow, RestrictRow } from './record';


export const writeHandlers = [
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

  // lambda
  Binder, transit.makeWriteHandler({
    tag: () => 'binder',
    rep: v => [v.name, v.type],
  }),
  Lam, transit.makeWriteHandler({
    tag: () => 'lam',
    rep: v => [v.binder, v.body],
  }),
  App, transit.makeWriteHandler({
    tag: () => 'app',
    rep: v => [v.func, v.arg],
  }),
  Arr, transit.makeWriteHandler({
    tag: () => 'arr',
    rep: v => [v.domain, v.codomain],
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

  // record
  Label, transit.makeWriteHandler({
    tag: () => 'label',
    rep: v => v.name,
  }),
  Rec, transit.makeWriteHandler({
    tag: () => 'rec',
    rep: v => [v.values, v.type],
  }),
  RowKind, transit.makeWriteHandler({
    tag: () => 'rowkind',
    rep: v => [],
    stringRep: 'rowkind',
  }),
  Row, transit.makeWriteHandler({
    tag: () => 'row',
    rep: v => v.description,
  }),
  SelectRow, transit.makeWriteHandler({
    tag: () => 'selectrow',
    rep: v => [v.label, v.rec, v.type],
  }),
  ExtendRow, transit.makeWriteHandler({
    tag: () => 'extendrow',
    rep: v => [v.rec, v.label, v.value],
  }),
  RestrictRow, transit.makeWriteHandler({
    tag: () => 'restrictrow',
    rep: v => [v.rec, v.label, v.type],
  }),
];


export const readHandlers = {
  // tm
  'type': () => Type.singleton,
  'hole': rep => new Hole(rep[0], rep[1]),
  'var': rep => new Var(rep[0], rep[1]),

  // lambda
  'binder': rep => new Binder({ name: rep[0], type: rep[1] }),
  'lam': rep => new Lam(rep[0], rep[1]),
  'app': rep => new App(rep[0], rep[1]),
  'arr': rep => new Arr(rep[0], rep[1]),

  // ref
  'absref': path => new AbsRef({ path }),
  'relref': path => new RelRef({ path }),

  // record
  'label': rep => new Label(rep),
  'rec': rep => new Rec(rep[0], rep[1]),
  'rowkind': () => RowKind.singleton,
  'row': rep => new Row(rep),
  'selectrow': rep => new SelectRow(rep[0], rep[1], rep[2]),
  'extendrow': rep => new ExtendRow(rep[0], rep[1], rep[2]),
  'restrictrow': rep => new RestrictRow(rep[0], rep[1], rep[2]),
};
