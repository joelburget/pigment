// @flow

import Immutable from 'immutable';

import type { Tm } from './tm';


const registry = {};


const NAME_KEY = '_name';


export type TmRecordEntry = { _name: string }
// export type QueryResult = Array<[string, Tm]>


export function read(): Map<string, Tm> {
  return Immutable.fromJS(registry);
}


export function register(name: string, cls: any): void {
  registry[name] = cls;
}


// TODO this isn't used. cut it?
export function deserialize(obj: TmRecordEntry): any {
  const name = obj[NAME_KEY];

  const withoutName = {};
  Object.keys(obj).forEach(key => {
    if (key !== NAME_KEY) {
      const value = obj[key];

      withoutName[key] = value.has(NAME_KEY) ? deserialize(value) : value;
    }
  });
  delete withoutName[NAME_KEY];

  return new registry[name](withoutName);
}
