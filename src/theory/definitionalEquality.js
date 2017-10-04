// @flow

import invariant from 'invariant';

import { CANONICAL } from './tm';


export default function definitionallyEqual(tm1, tm2) {
  // TODO - this assumes the invariant that they're both canonical forms.
  // Is that a valid assumption? Is it strong enough?
  invariant(
    tm1.form === CANONICAL && tm2.form === CANONICAL,
    'both terms passed to `definitionallyEqual` must be canonical'
  );

  return tm1.form === tm2.form && tm1.form.equals(tm1, tm2);
}
