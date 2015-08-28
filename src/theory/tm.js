// @flow
//
// TODO:
// * user-defined types
// * source positions? how does this relate to names?
import { List, Set, Record } from 'immutable';

import { lookup } from './context';
import type { Context } from './context';
import { mkStuck, mkSuccess } from './evaluation';
import type { EvaluationResult } from './evaluation';
import type { AbsRef, Ref } from './ref';


export type Tm = {
  evaluate: (root: AbsRef, ctx: Context) => EvaluationResult;

  subst: (root: AbsRef, ref: Ref, value: Tm) => Tm;

  // the only time this is optional is for Type itself
  getType: () => Tm;
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
}

Type.name = 'type';


var holeShape = Record({
  type: null,
  name: null,
  ref: null,
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

}
