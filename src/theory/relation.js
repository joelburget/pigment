// @flow

// The notion of a relation between two terms (by which I mean terms, types,
// kinds, etc).
//
// * x "is of type" y
// * x "accepts term" y
//   - This is really the same as the first: y "is of type" x
//   - Is it though? The relationship is directional, only telling us about x.
// * x "is" y
//   - perhaps this is subtype-aware?
//
// I'm not yet sure if these are all the relations we care about, but they're
// all I can think of at the moment.

import { Record } from 'immutable';

export const IS_TYPE = 'IS_TYPE';
export const ACCEPTS_TERM = 'ACCEPTS_TERM';
export const MATCHES = 'MATCHES';

export const Relation = Record({
  type: MATCHES, // x _ y
  subject: null, // _ matches y
  object: null,  // x matches _
});
