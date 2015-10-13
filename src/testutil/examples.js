/* eslint id-length: 0 */
import { Type, Var } from '../theory/tm';
import { mkRel } from '../theory/ref';
import Lam from '../aspects/lambda/data';

const type = Type.singleton;

export const id = new Lam(
  'x',
  type,
  new Var({ ref: mkRel('..', 'binder'), type }),
  type,
);


export const k = new Lam(
  'x',
  type,
  new Lam(
    'y',
    type,
    new Var({ ref: mkRel('..', '..', 'binder'), type }),
    type
  ),
  type
);
