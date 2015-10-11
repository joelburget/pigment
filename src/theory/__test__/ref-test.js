import expect from 'expect';
import { List } from 'immutable';

import { mkRel, mkAbs, RelRef, AbsRef } from '../ref';

import expectImmutableIs from '../../testutil/expectImmutableIs';


describe('ref', () => {
  it('mkRel', () => {
    const rel = mkRel('..', 'arg');
    const expected = new RelRef({ path: List(['..', 'arg']) });

    expectImmutableIs(rel, expected);
  });

  it('mkAbs', () => {
    const abs = mkAbs('module', 'function');
    const expected = new AbsRef({ path: List(['module', 'function']) });

    expectImmutableIs(abs, expected);
  });

  it('normalizes rel refs', () => {
    {
      const redundant = mkRel('a', 'b', '..', 'c', '..').normalize();
      const expected = mkRel('a');
      expectImmutableIs(redundant, expected);
    }

    {
      const redundant = mkRel('a', '..', 'b', '..').normalize();
      const expected = mkRel();
      expectImmutableIs(redundant, expected);
    }

    {
      const redundant = mkRel('..', 'b', '..').normalize();
      const expected = mkRel('..');
      expectImmutableIs(redundant, expected);
    }
  });

  it('normalizes abs refs', () => {
    {
      const redundant = mkAbs('a', 'b', '..', 'c', '..').normalize();
      const expected = mkAbs('a');
      expectImmutableIs(redundant, expected);
    }

    {
      const redundant = mkAbs('a', '..', 'b', '..').normalize();
      const expected = mkAbs();
      expectImmutableIs(redundant, expected);
    }

    {
      const redundant = mkAbs('..', 'b', '..');
      expect(() => { redundant.normalize(); }).toThrow();
    }
  });

  it('relativizies abs refs', () => {
    expectImmutableIs(
      mkAbs('a', 'b', 'c').relativize(mkRel('..', '..')),
      mkRel('..', '..', 'a', 'b', 'c')
    );
  });

  it('extends rel refs', () => {
    expectImmutableIs(
      mkRel('a', 'b').extend(mkRel('c', 'd')),
      mkRel('a', 'b', 'c', 'd')
    );
  });

  it('extends abs refs', () => {
    expectImmutableIs(
      mkAbs('a', 'b').extend(mkRel('c', 'd')),
      mkAbs('a', 'b', 'c', 'd')
    );
  });

  it('compares abs refs', () => {
    expect(
      mkAbs('a', 'b', 'c').is(mkAbs('a', 'b', 'c'), mkAbs())
    ).toBe(true);

    expect(
      mkAbs('a', 'b', 'c').is(mkAbs('a', 'b', 'c', 'd', '..'), mkAbs())
    ).toBe(true);
  });

  it('compares rel refs', () => {
    expect(
      mkRel('a', 'b', 'c').is(mkRel('a', 'b', 'c'), mkAbs())
    ).toBe(true);

    expect(
      mkRel('a', 'b', 'c').is(mkRel('a', 'b', 'c', 'd', '..'), mkAbs())
    ).toBe(true);
  });

  it('compares mixed refs', () => {
    expect(
      mkAbs('a', 'b', 'c').is(mkRel('a', 'b', 'c'), mkAbs())
    ).toBe(true);

    expect(
      mkRel('a', 'b', 'c').is(mkAbs('a', 'b', 'c', 'd', '..'), mkAbs())
    ).toBe(true);

    expect(
      mkRel('..', '..').is(mkAbs('a'), mkAbs('a', 'b', 'c'))
    ).toBe(true);

    expect(
      mkAbs('a').is(mkRel('..', '..'), mkAbs('a', 'b', 'c'))
    ).toBe(true);
  });
});
