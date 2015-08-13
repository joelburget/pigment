// A context holds the value (and type) of all the variables in scope

import { Map } from 'immutable';
import type { Expression } from './tm';


type Context = Map<string, [Expression, Expression]>;


export function lookupValue(c: Context, v: string): Expression {
  return c.get(v)[0];
}


export function lookupType(c: Context, v: string): Expression {
  return c.get(v)[1];
}


export function add(c: Context,
                    v: string,
                    e: [Expression, Expression]): Context {
  return c.set(v, e);
}


export const empty = Map();
