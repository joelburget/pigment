// @flow
//
// TODO:
// * source positions? how does this relate to names?
import invariant from 'invariant';
import { List, Record } from 'immutable';

import { mkStuck, mkSuccess } from './evaluation';
import { register } from './registry';
import { POKE_HOLE, pokeHole, doPokeHole } from '../commands/pokeHole';

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


export class Type {
  static name: string;

  // $flowstatic
  static singleton: Type = new Type();

  evaluate(root: AbsRef): EvaluationResult {
    return mkSuccess(this);
  }

  subst(root: AbsRef, ref: Ref, value: Tm): Tm {
    return this;
  }

  actions(): List<Action> {
    return List([pokeHole]);
  }

  performEdit(id: string): Edit {
    invariant(
      id === POKE_HOLE,
      'Type.edit only knows of POKE_HOLE'
    );

    return doPokeHole(this);
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

Type.singleton.type = Type.singleton;

register('type', Type);


const HoleShape = Record({
  name: null,
  type: null,
}, 'hole');

export class Hole extends HoleShape {

  constructor(name: ?string, type: Tm): void {
    super({ name, type });
  }

  evaluate(root: AbsRef, args: [Tm]): EvaluationResult {
    return mkStuck(this);
  }

  subst(root: AbsRef, ref: Ref, value: Tm): Tm {
    return ref.is(this.ref, root) ? value : this;
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

  actions(): List<Action> {
    return List();
  }

  // static form =
}


const ConflictShape = Record({
  left: null,
  right: null,
});


const TAKE_LEFT = 'TAKE_LEFT';
const TAKE_RIGHT = 'TAKE_RIGHT';

export class Conflict extends ConflictShape {

  actions(): List<Action> {
    return List([
      {
        title: 'take left',
        id: TAKE_LEFT,
      },
      {
        title: 'take right',
        id: TAKE_RIGHT,
      },
    ]);
  }

  performEdit(id: string): Edit {
    invariant(
      id === TAKE_LEFT || id === TAKE_RIGHT,
      'Conflict only knows TAKE_LEFT and TAKE_RIGHT'
    );

    return {
      TAKE_LEFT: this.left,
      TAKE_RIGHT: this.right,
    }[id];
  }

}
