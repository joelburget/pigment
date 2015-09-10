// A context holds the value (and type) of all the variables in scope

import { Map } from 'immutable';
import type { Tm } from './tm';
import { mkSuccess, mkStuck } from './evaluation';
import type { EvaluationResult } from './evaluation';
import type { AbsRef } from './ref';


export type Context = Map<AbsRef, Tm>;


export function lookup(ctx: Context,
                       ref: AbsRef):
                         Tm {
  return ctx.get(ref);
}


export function add(ctx: Context,
                    ref: AbsRef,
                    tm: Tm): Context {
  return ctx.set(ref, tm);
}


export var empty = Map();
