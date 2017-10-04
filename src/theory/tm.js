// @flow
import { List, Record } from 'immutable';

import type { FreeVar } from './ref';
import type Edit, { Action } from './edit';
import Scope from './scope';
import Context from './context';


const TmShape = Record({
  id: null, // unique identifier
  data: null,
  form: null, // Canonical | Eliminator
}, 'tm');


export class Tm extends TmShape {
  // bind a free variable to make a scope
  close(free: FreeVar): Scope {
    return this.close_(0, free);
  }

  // replace some free variable with a given bound variable
  close_(bound: number, free: FreeVar): Scope {
    // delegate to tm class
    // TODO replace this.form.close
    return this.form.close(this, bound, free);
  }

  // substitute the environment for bound variables
  // Epigram reloaded calls this `close`
  //
  // threshold: "the first bound variable to replace". Anything less than this
  // you leave bound. Anything greater than or equal to, you replace.
  substEnv(ctx: Context, threshold: number): Scope {
    return ctx.size === 0 ?
      this :
      // TODO replace this.form.substEnv
      this.form.substEnv(this, ctx, threshold);
    // TODO - see epigram reloaded for interesting rule re bound variables
  }
}


const CANONICAL = 'CANONICAL';
const ELIMINATOR = 'ELIMINATOR';


export type Canonical = {
  ruleType: CANONICAL;

  // where this thing belongs, what it expects of its neighbors
  rule: Rule;

  // getPieces -> traverse?
  getPieces: Function; // (tm: Tm) => *Scope
  actions: () => List<Action>;
  performEdit: (id: string) => Edit;

  equals: (tm1: Tm, tm2: Tm) => Boolean;
  unify: (tm1: Tm, tm2: Tm) => ?Tm;
};


export type Eliminator = {
  ruleType: ELIMINATOR;

  // where this thing belongs, what it expects of its neighbors
  rule: Rule;

  // getPieces -> traverse?
  getPieces: Function; // (tm: Tm) => *Scope

  // describe the evaluation semantics
  step: Function; // TODO signature
};


const OfType = Record({
  subject: null,
  object: null,
});


// A rule operates in much the same way as a traditional inference rule:
//
// > Hey, given the context you're in, it's possible to use this form
//
// The preconditions are a telescope, with bound variables. The postcondition
// is a term.
export type Rule = (subject: Tm) =>
  // TODO - describe how to bind a term and a type together


export type Feature = {
  // (canonical) constructors for any relevant terms and types
  constructors: Set<Canonical>;
  eliminators: Set<Eliminator>;

  // not sure if it's necessary to separate these, but epigram does
  canTyRules: Set<Rule>;
  elimTyRules: Set<Rule>;

  // names that will bring up this form through autocomplete
  searchAliases: Set<string>;
};
