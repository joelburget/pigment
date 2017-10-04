import expect from 'expect';
import { List } from 'immutable';

import { mkBound, mkFree, BoundVar, FreeVar } from '../ref';

import expectImmutableIs from '../../testutil/expectImmutableIs';


describe('ref', () => {
  it('mkBound', () => {
    const rel = mkBound(1, 'arg');
    const expected = new BoundVar({ index: 1, name: 'arg' });

    expectImmutableIs(rel, expected);
  });

  it('mkFree', () => {
    const abs = mkFree('module', 'function');
    const expected = new FreeVar({ path: List(['module', 'function']) });

    expectImmutableIs(abs, expected);
  });

  it('extends abs refs', () => {
    expectImmutableIs(
      mkFree('a', 'b').extend(mkBound('c', 'd')),
      mkFree('a', 'b', 'c', 'd')
    );
  });

  it('compares abs refs', () => {
    expect(
      mkFree('a', 'b', 'c').is(mkFree('a', 'b', 'c'), mkFree())
    ).toBe(true);

    expect(
      mkFree('a', 'b', 'c').is(mkFree('a', 'b', 'c', 'd', '..'), mkFree())
    ).toBe(true);
  });

  it('compares rel refs', () => {
    // TODO - do we want to support this?
    expect(
      mkBound('a', 'b', 'c').is(mkBound('a', 'b', 'c'), mkFree())
    ).toBe(true);

    expect(
      mkBound('a', 'b', 'c').is(mkBound('a', 'b', 'c', 'd', '..'), mkFree())
    ).toBe(true);
  });

  it('compares mixed refs', () => {
    expect(
      mkFree('a', 'b', 'c').is(mkBound('a', 'b', 'c'), mkFree())
    ).toBe(true);

    expect(
      mkBound('a', 'b', 'c').is(mkFree('a', 'b', 'c', 'd', '..'), mkFree())
    ).toBe(true);

    expect(
      mkBound('..', '..').is(mkFree('a'), mkFree('a', 'b', 'c'))
    ).toBe(true);

    expect(
      mkFree('a').is(mkBound('..', '..'), mkFree('a', 'b', 'c'))
    ).toBe(true);
  });
});
