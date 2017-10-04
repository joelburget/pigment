// @flow
//
// global reference

import { List, Record, is } from 'immutable';
import ImmutablePropTypes from 'react-immutable-proptypes';
import { PropTypes } from 'react';


export class BoundVar extends Record({ index: 0, name: null }) {
  is(ref: Ref, root: FreeVar): boolean {
    return ref instanceOf BoundVar ?
      ref.index === this.index : // XXX also disambiguate name
      XXX;
  }
}


export class FreeVar extends Record({ path: null }) {
  extend(ref: BoundVar): FreeVar {
    const path = this.path.concat(ref.path);
    return new FreeVar({ path });
  }

  is(ref: Ref, root: FreeVar): boolean {
    return ref instanceof FreeVar ?
      is(this, ref) :
      XXX;
  }
}


export type Ref = BoundVar | FreeVar;


export function mkBound(index: number, ?name: string): BoundVar {
  return new BoundVar({ index, name });
}


// export function mkFree(...parts: Array<string>): FreeVar {
//   const path = List(parts);
export function mkFree(): FreeVar {
  const path = List(arguments);
  return new FreeVar({ path });
}


export const PropTypesPath = ImmutablePropTypes.listOf(PropTypes.string);
export const PropTypesBoundVar = PropTypes.instanceOf(BoundVar);
export const PropTypesFreeVar = PropTypes.instanceOf(FreeVar);
export const PropTypesRef = PropTypes.oneOfType([
  PropTypesBoundVar,
  PropTypesFreeVar,
]);
