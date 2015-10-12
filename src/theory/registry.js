// @flow

import Immutable from 'immutable';

import type { Tm } from './tm';


const registry = {};


export function read(): Map<string, Tm> {
  return Immutable.fromJS(registry);
}


export function register(name: string, cls: any): void {
  registry[name] = cls;
}
