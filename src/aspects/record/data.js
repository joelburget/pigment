// @flow

import { List, Record as ImmRecord, Set } from 'immutable';
import invariant from 'invariant';

import { CANONICAL, ELIMINATOR } from '../../theory/tm';
import { register } from '../../theory/registry';
import { openNewEdit } from '../../theory/edit';
import { mkBound } from '../../theory/ref';
import defnEq from '../../theory/definitionalEquality';
import unify from '../../theory/unify';

import { ADD_ENTRY, addEntry, makeLabel } from '../../commands/addEntry';
import { POKE_HOLE, pokeHole, doPokeHole } from '../../commands/pokeHole';

import type { Tm } from '../../theory/tm';
import type Edit, { Action } from '../../theory/edit';
import type { FreeVar } from '../../theory/ref';
import type { Context } from '../../theory/context';


// formation

const RecordTy = ImmRecord({
  row: null, // : Row
});


// export const mkRecordTy = row => new Tm(
//   ['Record', 'formation'], new RecordTy({ row })
// );


const recordTyConstructor = {
  ruleType: CANONICAL,

  getPieces: function* getPieces(tm: Tm) {
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
      new RecordTy({ row }) :
      null;
  },

};


// introduction
//
// * literal : { values }
//
// * restrict : { l : a | r } -> { r }
//   r - l
//   update:
//     { l := x | r } = { l = x | r - l }
//   rename:
//     { l <- m | r } = { l = r.m | r - m }
//
// * extend : a -> { r } -> { l : a | r }
//   { l = e | r }
//   origin = { x = 0 | { y = 0 | {} } }
//   origin = { x = 0, y = 0 }

const Record = ImmRecord({
  values: null, // Map<string, Tm>
}, 'record');


// export const mkLiteral = values => new Tm(
//   ['Record', 'intros', 'Record'], new Record({ values })
// );


const recordConstructor = {
  ruleType: CANONICAL,

  // unify this term and its environment!
  unificationRules() {},

  unify(tm1: Tm, tm2: Tm) {
    const { values: values1 } = tm1;
    const { values: values2 } = tm2;

    // what happens when the rows don't match?
    // what happens when the rows match but the values don't
  },

  getPieces: function* getPieces(tm: Tm) {
    yield* tm.data.values;
  },

  actions(): List<Action> {
    return List([addEntry, pokeHole]);
  },

  // TODO should this use Row.performEdit instead of building its own row?
  performEdit(id: string): Edit {
    invariant(
      id === ADD_ENTRY || id === POKE_HOLE,
      'Rec.performEdit only knows of ADD_ENTRY and POKE_HOLE'
    );

    if (id === ADD_ENTRY) {
      const { values } = this;
      const label = makeLabel(values);

      const ty = new Hole({ type: Type.singleton });
      const val = new Hole({ type: ty });

      const newTm = new Record(
        values.set(label, val),
        XXX
        // new Row(type.entries.set(label, ty))
      );

      return openNewEdit(id, this, newTm, new List());
    } else { // id === POKE_HOLE
      return doPokeHole(this);
    }
  },

};


/*
const Restrict = ImmRecord({
  record: null,
  label: null,
}, 'restrict');


export const mkRestrict = (record: Record, label: string) => new Tm(
  ['Record', 'intros', 'Restrict'], new Restrict({ record, label })
);


const restrict = {
  term: XXX,
  type: mkRow(XXX),
  getPieces: ({ subterms }) => XXX,
  step: (root: FreeVar, ctx: Context) => {
    XXX;
  },
  actions: () => List([]),
  performEdit: (id: string) => {
    invariant(
      false,
      "restrict doesn't know any operations yet. in particular, " + id
    );
  }
};


const Extend = ImmRecord({
  record: null,
  label: null,
  value: null,
}, 'extend');


export const mkExtend = (record: Record, label: string, value: Tm) => new Tm(
  ['Record', 'intros', 'Extend'], new Extend({ record, label, value })
);


const extend = {
  term: XXX,
  type: mkRow(XXX),
  getPieces: XXX,
  step: (root: FreeVar, ctx: Context) => {
    XXX;
  },
  actions: () => List([]),
  performEdit: (id: string) => {
    invariant(
      false,
      "extend doesn't know any operations yet. in particular, " + id
    );
  }
};
*/


// elimination
//
// record primitive operations
// * select : { l : a | r } -> a
//   r.l
//   distance p = sqrt (p.x * p.x + p.y * p.y)

const Select = ImmRecord({
  record: null,
  label: null,
}, 'select');


// export const mkSelect = (record: Record, label: string) => new Tm(
//   ['Record', 'elims', 'Select'], new Select({ record, label })
// );


// l -> Record [a .. l:r .. z] -> r
const selectElimination = {
  ruleType: ELIMINATOR,
  getPieces: function* getPieces(tm: Tm) {
    // XXX
    yield* tm.data.record;
  },
  step(tm: Tm): Tm {
    const { label, record } = tm.data;
    return record.get(label);
  },
};


const feature = {
  constructors: Set([recordConstructor, recordTyConstructor]),
  eliminators: Set([selectElimination]), // also extension, restriction

  canTyRules: Set(),
  elimTyRules: Set(),

  searchAliases: ['record', 'product'],
};


export default feature;

register('record', feature);
