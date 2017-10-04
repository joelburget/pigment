// @flow
//
// The best reference for all this stuff is The Locally Nameless Representation
// by Arthur Chargueraud. Brilliant for understanding why everything is
// structured this way. I quote from it liberally in this doc.

import { Record } from 'immutable';

import { Tm } from './tm';
import { FreeVar, BoundVar } from './ref';

import type { Set } from 'immutable';

const ScopeShape = Record({
  binder: null, // { string: Tm }
  body: null, // Tm (or Scope?)
}, 'scope');


export default class Scope extends ScopeShape {
  open(tm: Tm) {
    return this.open_(0, tm);
  }

  // [bound/tm]
  open_(bound: number, tm: Tm) {
    return this.body.open(bound, tm);
  }

  // Epigram reloaded calls this `close`
  substEnv(ctx: Context, threshold: number): Scope {
    const { binder, body } = this;
    return new Scope({
      binder,
      body: body.substEnv(ctx, threshold + 1)
    });
  }
}

// * /Variable opening/ turns some bound variables into free variables.
//   It is used to investigate the body of an abstraction.
//
// * /Variable closing/ turns some free variables into bound variables.
//   It is used to build an abstraction  given a representation of its body.
//
//
// * Substitution replaces free variables with terms
// * Closing replaces free variables with bound variables
// * Opening replaces bound variables with terms

// TODO: make method?
//
// Provide a fresh name to /open/ the abstraction.
//
// The result of applying /variable opening/ to `t` and `x` is a term that
// describes the body of the abstaction.
//
// More precisely (TODO)
export function open(scope: Scope, u: Tm): Tm {
  return open_(scope, 0, u);
}

function open_(scope: Scope, k: number, u: Tm): Tm {
  if (tm instanceof BoundVar) {
    const { i } = tm;
    return i === k ? u : tm;
  } else if (tm instanceof FreeVar) {
    return tm;
  } else if (tm instanceof Abs) {
    return tm.subst(k + 1, u);
  } else {
    return tm.subst(k, u);
  }

  // BoundVar i -> i === k ? u : BoundVar i
  // FreeVar y -> FreeVar y
  // App t1 t2 -> App (subst t1 k u) (subst t2 k u)
  // Abs t -> Abs (subst t (k + 1) u)
}

export function varOpen(scope: Scope, x: Name): Tm {
  return open_(scope, 0, new FreeVar(x));
}

// Build a term by applying the /variable closing/ operation.
//
// All variables named `x` in `t` are abstracted.
export function close(t: Tm, x: Name): Scope {
}


// XXX Tm vs Scope
function close_(k: number, x: Name, t: Tm): Scope {
  // BoundVar i -> BoundVar i
  // FreeVar y -> x === y ? BoundVar k : FreeVar y
  // App t1 t2 -> App (close_ k x t1) (close_ k x t2)
  // Abs t -> Abs (close_ (k + 1) x t)
}

export function freeVars(tm: Tm): Set<string> {
  BoundVar i -> Set()
  FreeVar x -> Set(x)
  App t1 t2 -> freeVars(t1).union(freeVars(t2))
  Abs t -> freeVars(t)
}

export function fresh(name: string, tm: Tm): Boolean {
  return freeVars(tm).includes(name);
}

export function closed(tm: Tm): Boolean {
  return freeVars(tm).isEmpty();
}

export function subst(x: string, u: Tm, scope: Scope): Scope {
  BoundVar i -> BoundVar i
  FreeVar y -> x === y ? u : FreeVar y
  App t1 t2 -> App (subst x y t1) (subst x u t2)
  Abs t -> Abs (subst x u t)
}

// alternatively:
export function subst(x: String, u: Tm, t: Tm): Tm {
  return open(close(t, x), u);
}

export function betaReduce(tm: Tm): Tm {
  App (Abs t) u -> open(t, u)
}
