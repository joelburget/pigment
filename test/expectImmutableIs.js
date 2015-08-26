import expect from 'expect';
import { is } from 'immutable';

export default function expectImmutableIs(a, b) {
  var msg = JSON.stringify(a) + " isn't " + JSON.stringify(b);
  return expect(is(a, b)).toBe(true, msg);
}
