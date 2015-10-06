// @flow
//
// TODO:
// * source positions? how does this relate to names?
import invariant from 'invariant';
import { List, Record, Iterable } from 'immutable';

import { mkStuck, mkSuccess } from './evaluation';
import { register } from './registry';
import { openNewEdit } from './edit';

import type { EvaluationResult } from './evaluation';
import type { Ref, AbsRef } from './ref';
import type Edit, { Action } from './edit';


export const VARIABLE = 'VARIABLE';
export const INTRO = 'INTRO';
export const ELIM = 'ELIM';
export type IntroElim = INTRO | ELIM;


export type Tm = {
  // * Instead we can pass in the arguments it's being applied to. Tie this in
  //   with the binding structure we expect to know from a term and we should
  //   always know the right amount of arguments to pass in.
  evaluate: (root: AbsRef, args: [Tm]) => EvaluationResult;

  subst: (root: AbsRef, ref: Ref, value: Tm) => Tm;

  getType: () => Tm;

  slots: () => Iterable<K, V>;

  actions: () => List<Action>;

  performEdit: (id: string) => Edit;

  // static form: IntroElim;

  // static typeClass
  // - the class of the type this inhabits!
  // - INTRO *only*

  // static fillHole(type: Tm) => Tm
  // - return an instance that fills this type of hole
  // - INTRO *only*
};


const POKE_HOLE = 'POKE_HOLE';


export class Type {
  static name: string;

  // $flowstatic
  static singleton: Type = new Type();

  evaluate(root: AbsRef, args: [Tm]): EvaluationResult {
    return mkSuccess(this);
  }

  subst(root: AbsRef, ref: Ref, value: Tm): Tm {
    return this;
  }

  getType(): Tm {
    return this;
  }

  slots(): Iterable<K, V> {
    return Iterable();
  }

  actions(): List<Action> {
    return List([
      {
        id: POKE_HOLE,
        title: 'poke hole',
      },
    ]);
  }

  performEdit(id: string): Edit {
    invariant(
      id === POKE_HOLE,
      'Type.edit only knows of POKE_HOLE'
    );

    return openNewEdit(
      id,
      this,
      new Hole(null, Type.singleton),
      List()
    );
  }

  static typeClass = Type;

  static fillHole(type: Tm): Type {
    invariant(
      type === Type.singleton,
      'Type asked to fill a hole of type other than Type'
    );

    return Type.singleton;
  }

  static form = INTRO;
}

register('type', Type);


const HoleShape = Record({
  name: null,
  type: null,
}, 'hole');

export class Hole extends HoleShape {

  constructor(name: ?string, type: Object): void {
    super({ type, name });
  }

  evaluate(root: AbsRef, args: [Tm]): EvaluationResult {
    return mkStuck(this);
  }

  subst(root: AbsRef, ref: Ref, value: Tm): Tm {
    return ref.is(this.ref, root) ? value : this;
  }

  slots() {
    throw new Error('Hole.slots - unimplemented');
  }

  actions(): List<Action> {
    return List();
  }

  // static form = INTRO;
}


// what's the difference between a variable and a hole?
// a variable is intangible / a hole sits in for a term
// a slot can be a variable, but not a hole
//
// what's a slot? a term or a variable?


const VarShape = Record({
  ref: null,
  type: null
}, 'var');

export class Var extends VarShape {

  constructor(ref: Ref, type: Tm): void {
    super({ ref, type });
  }

  evaluate(root: AbsRef, args: [Tm]): EvaluationResult {
    throw new Error('evaluating variable!');
  }

  subst(root: AbsRef, ref: Ref, value: Tm): Tm {
    return ref.is(this.ref, root) ? value : this;
  }

  slots() {
    throw new Error('Var.slots - unimplemented');
  }

  actions(): List<Action> {
    return List();
  }

  // static form =
}


const ConflictShape = Record({
  left: null,
  right: null,
});


export class Conflict extends ConflictShape {

  actions(): List<Action> {
    return List([
      {
        name: 'take left',
        action: () => {
          console.log('conflict: take left', this.left);
          return this.left;
        }
      },
      {
        name: 'take right',
        action: () => {
          console.log('conflict: take right', this.right);
          return this.right;
        }
      },
    ]);
  }

}
