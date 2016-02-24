// @flow
import Immutable from 'immutable';

type ForwardChange = {
  tag: 'FORWARD_CHANGE';

  // did we change anything / gain information over the old?
  gain: boolean;
};

type Contradiction = {
  tag: 'CONTRADICTION';

  errorMessage: string;

  // TODO more information - the haskell version has this data constructor:
  // `Contradiction !(HashSet Name) String`
  // names: Immutable.Set<Name>;
};

type Change<A> = ForwardChange | Contradiction;

// A cell contains "information about a value" rather than a value per se.
//
// - https://github.com/ekmett/propagators/blob/master/src/Data/Propagator/Cell.hs
//
// The shared connection mechanism is called a "cell" and the machines they
// connect are called "propagators".
class Cell<A> {
  mergeStrategy: (left: A, right: A): Change<A>;

  constructor(
}
