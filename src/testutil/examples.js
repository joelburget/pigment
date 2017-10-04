/* eslint id-length: 0 */
import { Type, Var } from '../theory/tm';
import { mkBound } from '../theory/ref';
import { mkFunction } from '../aspects/function/data';

const type = Type.singleton;

export const id = mkFunction(
  'x',
  type,
  new Var({ ref: mkBound('..', 'binder'), type }),
  type,
);


export const k = mkFunction(
  'x',
  type,
  mkFunction(
    'y',
    type,
    new Var({ ref: mkBound('..', '..', 'binder'), type }),
    type
  ),
  type
);
