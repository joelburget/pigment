import { Type, Var } from '../theory/tm';
import { mkSuccess, mkStuck, bind } from '../theory/evaluation';
import { mkRel, mkAbs } from '../theory/ref';
import Lam from '../aspects/lambda/data';

const type = Type.singleton;

export const id = new Lam(
  'x',
  type,
  new Var(mkRel('..', 'binder'), type),
  type,
);


export const k = new Lam(
  'x',
  type,
  new Lam(
    'y',
    type,
    new Var(mkRel('..', '..', 'binder'), type),
    type
  ),
  type
);
