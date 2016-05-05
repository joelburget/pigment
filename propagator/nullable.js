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
//
// TODO: think about whether / how we can modify the rest of the operations
// exported by the original protocol to be nullable. We can kind of get away
// with not doing it because `liftToCellContents` checks that all its arguments
// are non-null before proceeding, but that's just a hack. And that check
// should go away!
export default ({merge: aMerge, ...protocol}) => ({
  merge: R.partial(merge, [aMerge]),
  protocol,
});
