// @flow

import halfZip from '../util/halfzip';

import type { Tm } from './tm';

export default function unify(tm1: Tm, tm2: Tm): ?Tm {
  // TODO is this an okay way to check they're the same type?
  // TODO account for variables and holes! Are these special cased? How do we
  // specify that they're really just big slots?
  if (tm1.constructor === tm2.constructor) {
    // halfzip together the slots!
    const zipped = halfZip(tm1.slots(), tm1.slots());

    if (zipped) {
      const unifiedSlots = zipped.map(([left, right]) => unify(left, right));

      if (unifiedSlots.every(unifier => unifier != null)) {
        return new tm.constructor(unifiedSlots);
      }
    }
  }

  return null;
}
