// @flow
// A context holds the value (and type) of all the variables in scope

import { Map } from 'immutable';
import type { Expression } from './tm';
import { mkSuccess, mkStuck } from './evaluation';
import type EvaluationResult from './evaluation';


export type Context = Map<string, Expression>;


export function lookup(ctx: Context,
                       name: string):
                         Expression {
  return ctx.get(name);
}


export function add(c: Context,
                    v: string,
                    e: Expression): Context {
  return c.set(v, e);
}


export var empty = Map();
