// @flow

import Immutable from 'immutable';

import type { Tm } from './tm';
import unify from './unify';


let registry = {};


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

  let withoutName = {};
  Object.keys(obj).forEach(key => {
    if (key !== NAME_KEY) {
      const value = obj[key];

      withoutName[key] = value.has(NAME_KEY) ? deserialize(value) : value;
    }
  });
  delete withoutName[NAME_KEY];

  return new registry[name](withoutName);
}


// // if this works it's going to be *so cool*.
// // * try unifying the most general form (slots are variables) of each
// //   registered form
// // * if it unifies keep that unified form
// // * return all unified forms
// export function unifiersOf(tm: Tm): QueryResult {
//   const results = [];

//   // XXX surely we have to do something with form
//   // * form is the class -- we need a way to instantiate it with all variables
//   // * can see how that works for lambda -- how about records?
//   registry.forEach((form, name) => {
//     const unified = unify(tm, form);
//     if (unified != null) {
//       results.push([name, unified]);
//     }
//   });

//   return results;
// }
