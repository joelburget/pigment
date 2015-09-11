// @flow
//
// TODO:
// * user-defined types
// * source positions? how does this relate to names?
import { List, Set, Record } from 'immutable';
import transit from 'transit-js';

import { lookup } from './context';
import { mkStuck, mkSuccess } from './evaluation';

import type { Context } from './context';
import type { EvaluationResult } from './evaluation';
import type { Ref, AbsRef } from './ref';
import type { TmRecordEntry } from './registry';


export type Tm = {
  // * We're not really using Context. I'm not sure it's necessary given our
  //   model of computation.
  // * Instead we can pass in the arguments it's being applied to. Tie this in
  //   with the binding structure we expect to know from a term and we should
  //   always know the right amount of arguments to pass in.
  evaluate: (root: AbsRef, ctx: Context) => EvaluationResult;

  subst: (root: AbsRef, ref: Ref, value: Tm) => Tm;

  // the only time this is optional is for Type itself
  getType: () => Tm;

  unify: (tm: Tm) => ?Tm;
};


export class Type {
  static name: string;

  // $flowstatic
  static singleton: Type = new Type();

  evaluate(root: AbsRef, ctx: Context): EvaluationResult {
    return mkSuccess(this);
  }

  subst(root: AbsRef, ref: Ref, value: Tm): Tm {
    return this;
  }

  getType(): Tm {
    return this;
  }

  unify(tm: Tm): ?Tm {
    return tm === this ? this : null;
  }
}


var holeShape = Record({
  name: null,
  type: null,
}, 'hole');

export class Hole extends holeShape {

  constructor(name: ?string, type: Object): void {
    super({ type, name });
  }

  getType(): Tm {
    return this.type;
  }

  evaluate(root: AbsRef, ctx: Context): EvaluationResult {
    return mkStuck(this);
  }

  subst(root: AbsRef, ref: Ref, value: Tm): Tm {
    return ref.is(this.ref, root) ? value : this;
  }

  unify(tm: Tm): ?Tm {
    return this.type.unify(tm.getType()) == null ?
      null :
      tm;
  }
}


var varShape = Record({
  ref: null,
  type: null
}, 'var');

export class Var extends varShape {

  constructor(ref: Ref, type: Tm): void {
    super({ ref, type });
  }

  getType(): Tm {
    return this.type;
  }

  evaluate(root: AbsRef, ctx: Context): EvaluationResult {
    throw new Error('evaluating variable!');
    // return mkSuccess(lookup(ctx, this.ref));
  }

  subst(root: AbsRef, ref: Ref, value: Tm): Tm {
    return ref.is(this.ref, root) ? value : this;
  }

  unify(tm: Tm): ?Tm {
    return this.type.unify(tm.getType()) == null ?
      null :
      tm;
  }
}
