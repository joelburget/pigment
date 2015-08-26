import { Type, Var } from '../src/theory/tm';
import { mkSuccess, mkStuck, bind } from '../src/theory/evaluation';
import { Lam, App, Binder } from '../src/theory/lambda';
import { empty as emptyCtx } from '../src/theory/context';
import { mkRel, mkAbs } from '../src/theory/ref';

const type = Type.singleton;

export const id = new Lam(
  new Binder({ name: 'x', type }),
  new Var(mkRel('..', 'binder'), type)
);


export const k = new Lam(
  new Binder({ name: 'x', type }),
  new Lam(
    new Binder({ name: 'y', type }),
    new Var(mkRel('..', '..', 'binder'), type)
  )
);
