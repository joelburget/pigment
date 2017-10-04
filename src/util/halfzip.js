// @flow
//
// halfZip is like unification, but only one level at a time. useful?
import type { KeyedIterable } from 'immutable';

// would be really slick if i could do:
//

for (let slot of as) {
  if (!bs.has(slot)) {
    halt;
  } else {
    const aVal = as.getIn(slot);
    const bVal = bs.getIn(slot);

    if (atomic(aVal) && atomic(bVal)) {
      if (defnEqual(aVal, bVal)) {
        yield aVal;
      } else {
        halt;
      }
    } else if (!atomic(aVal) && !atomic(bVal)) {
      const unified = await(unify(
    }
  }
}

export default function halfZip<K, V>(
  as: KeyedIterable<K, V>,
  bs: KeyedIterable<K, V>): ?KeyedIterable<K, [V, V]> {

  if (as.count() !== bs.count()) {
    return null;
  }

  try {
    return as.map((aVal, aKey) => {
      const bVal = bs.get(aKey);
      if (!bVal) {
        // TODO find more idiomatic way
        throw new Error('stop iteration!');
      } else {
        return [aVal, bVal];
      }
    });
  } catch (stop) {
    return null;
  }
}
