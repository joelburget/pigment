// @flow
import type { KeyedIterable } from 'immutable';

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
