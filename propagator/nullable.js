import R from 'ramda';

import type Merge from './cell';

function merge<A>(aMerge: Merge<A>, x: ?A, y: ?A): Change<A> {
  if (x == null || y == null) {
    const content = x || y;
    return {
      tag: 'FORWARD_CHANGE',
      gain: content != null,
      content,
    };
  } else {
    return aMerge(x, y);
  }
}

// Return a new protocol based on the original merge function
export default protocol => ({
  merge: R.partial(merge, [protocol.merge]),
});
