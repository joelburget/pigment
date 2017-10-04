// @flow

// I think unification should join variable binding among the pantheon of
// things we provide as infrastructure. Done in a simple, easy to understand
// way. What other pieces of infrastructure are fundamental, simple, and
// powerful?
//
// * pattern matching (SICP draws a connection between unification and pattern
//   matching)
//   - unification is a generalization of pattern matching in which both the
//     pattern and datum may contain variables
// * evaluation
// * editing / history / persistence

import defnEq from './definitionalEquality';

import type Context from './context';
import type { Tm } from './tm';


export default function unify(pat1: Tm, pat2: Tm, frame: Context): ?Tm {
  // interesting case: holes are not symmetrical -- something else taking the
  // lead in unification will reject a hole, but a hole will accept anything.

  // TODO account for variables and holes! Are these special cased? How do we
  // specify that they're really just big slots?
  //
  // Use definitional equality for now, then figure out how to do something
  // more sophisticated later.

  // XXX need types to be equal, not terms!
  return defnEq(ty1, ty2) ?
    pat1.form.unify(pat1, pat2) :
    null;
}
