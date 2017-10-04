// @flow

// Variants! I suppose records and variants together are the way to go!

import { List, Record, Set } from 'immutable';
import invariant from 'invariant';

import { CANONICAL, ELIMINATOR } from '../../theory/tm';
import { register } from '../../theory/registry';
import defnEq from '../../theory/definitionalEquality';
import unify from '../../theory/unify';

// import type { EvaluationResult } from '../../theory/evaluation';
import type { Tm } from '../../theory/tm';
import type Edit, { Action } from '../../theory/edit';


const VariantTy = Record({
  row: null, // : Row
}, 'variantty');


const variantTyConstructor = {
  ruleType: CANONICAL,

  getPieces: function* getPieces(tm: Tm) {
    // XXX
    yield* tm.data.row;
  },

  actions(): List<Action> {
    return List([]);
  },

  performEdit(): Edit {
    invariant(
      false,
      'Variant.performEdit knows nothing!'
    );
  },

  equals(tm1: Tm, tm2: Tm): Boolean {
    return defnEq(tm1.row, tm2.row);
  },

  unify(tm1: Tm, tm2: Tm): ?Tm {
    const row = unify(tm1.row, tm2.row);
    return row != null ?
      new VariantTy({ row }) :
      null;
  },

};


const Variant = Record({
  label: null, // Label
  value: null, // Tm
}, 'variant');


// Interesting special cases:
// * enumerations
// * single-field variants (newtype, essentially)
//
// Both would be useful to visually distinguish.
const variantConstructor = {
  ruleType: CANONICAL,

  getPieces: function* getPieces(tm: Tm) {
    // XXX
    yield* tm.data.row;
  },

  actions(): List<Action> {
    return List([]);
  },

  performEdit(): Edit {
    invariant(
      false,
      'Variant.performEdit knows nothing!'
    );
  },

  equals(tm1: Tm, tm2: Tm): Boolean {
    const { label: l1, value: v1 } = tm1;
    const { label: l2, value: v2 } = tm2;
    return defnEq(l1, l2) && defnEq(v1, v2);
  },

  unify(tm1: Tm, tm2: Tm): ?Tm {
    const { label: l1, value: v1 } = tm1;
    const { label: l2, value: v2 } = tm2;

    const label = unify(l1, l2);
    if (label == null) {
      return null;
    }

    const value = unify(v1, v2);
    if (value == null) {
      return null;
    }

    return new Variant({ label, value });
  },

};


// (a -> r) ... (z -> r) -> Variant [a...z] -> r
const caseElimination = {
  ruleType: ELIMINATOR,
  getPieces: function* getPieces(tm: Tm) {
    yield* tm.data.recursors;
  },
  step(tm: Tm): Tm {
    // TODO recursors, variant
    // TODO label,
    const { recursors, variant } = tm.data;
    const { label, value } = variant.data;
    // TODO this depends on functions -- is that cool?
    return mkApplication(recursors[label], value);
  },
};


const feature = {
  constructors: Set([variantConstructor, variantTyConstructor]),
  eliminators: Set([caseElimination]),

  canTyRules: Set([
    // variantty : Row -> *
    // variant : variantty
  ]),
  elimTyRules: Set([
    // caseElim: (a -> r) ... (z -> r) -> Variant [a...z] -> r
  ]),

  searchAliases: ['variant', 'sum'],
};

export default feature;

register('variant', feature);
