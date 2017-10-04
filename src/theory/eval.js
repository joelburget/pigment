// @flow
//
// What type of evaluation is this? Not sure yet. Concerns:
//
// * Allowing / tracking effects
// * What type of result do we return?
//   - normal form
//   - head normal
//   - weak head normal
//
// Evaluation order: I think this is simpler, and rather neat. Computation
// really only happens at eliminators, so they define evaluation order through
// their step functions.

import type { Tm } from './tm';
import type { Context } from './context';

export default function eval(tm: Tm, ctx: Context) {
}
