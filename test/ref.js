import expect from 'expect';
import { List } from 'immutable';

import expectImmutableIs from './expectImmutableIs';
import { mkRel, mkAbs, RelRef, AbsRef } from '../src/theory/ref';


describe('ref', () => {
  it('mkRel', () => {
    var rel = mkRel('..', 'arg');
    var expected = new RelRef({ path: List(['..', 'arg']) });

    expectImmutableIs(rel, expected);
  });

  it('mkAbs', () => {
    var abs = mkAbs('module', 'function');
    var expected = new AbsRef({ path: List(['module', 'function']) });

    expectImmutableIs(abs, expected);
  });

  it('normalizes rel refs', () => {
    var redundant = mkRel('a', 'b', '..', 'c', '..').normalize();
    var expected = mkRel('a');
    expectImmutableIs(redundant, expected);

    var redundant = mkRel('a', '..', 'b', '..').normalize();
    var expected = mkRel();
    expectImmutableIs(redundant, expected);

    var redundant = mkRel('..', 'b', '..').normalize();
    var expected = mkRel('..');
    expectImmutableIs(redundant, expected);
  });

  it('normalizes abs refs', () => {
    var redundant = mkAbs('a', 'b', '..', 'c', '..').normalize();
    var expected = mkAbs('a');
    expectImmutableIs(redundant, expected);

    var redundant = mkAbs('a', '..', 'b', '..').normalize();
    var expected = mkAbs();
    expectImmutableIs(redundant, expected);

    var redundant = mkAbs('..', 'b', '..');
    var expected = mkAbs('..');
    expect(() => { redundant.normalize(); }).toThrow();
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
