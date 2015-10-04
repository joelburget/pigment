import { is } from 'immutable';
import type { List } from 'immutable';

export default function isPrefix<X>(xs: List<X>, ys: List<X>) {
  if (xs.size === 0) {
    return true;
  } else if (ys.size === 0) {
    return false;
  } else {
    return is(xs.first(), ys.first()) &&
      isPrefix(xs.shift(), ys.shift());
  }
}
