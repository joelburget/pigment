// @flow

import { Record } from 'immutable';


export const MODULE_PUBLIC = 'module/MODULE_PUBLIC';
export const MODULE_PRIVATE = 'module/MODULE_PRIVATE';
// idris also has abstract, though i'm not sure when it's useful

type Visibility = MODULE_PUBLIC | MODULE_PRIVATE;


export class ModuleState extends Record({
  module: null,
  mouseSelection: null,
}, 'modulestate') {}


// This is gross / tricky -- need this type to align with the export list
// from the Module, which is implicit -- you need to look at only
// definitions, and then only at the subset which are public.
export class ModuleType extends Record({
  contents: null // List<Ty>
}, 'moduletype') {}


var moduleShape = Record({
  name: null,     // string
  contents: null, // List<Note | Definition | Property | Example>
}, 'module');

export class Module extends moduleShape {
  getType(): Tm {
    const contents = this.contents
    .filter(
      item => item instanceof Definition && item.visibility === MODULE_PUBLIC
    )
    .map(item => item.getType());

    return new ModuleType({ contents });
  }

  evaluate(root: AbsRef, ctx: Context): EvaluationResult {
    throw new Error('unimplemented: Module.evaluate');
  }

  subst(root: AbsRef, ref: Ref, value: Tm): Tm {
    throw new Error('unimplemented: Module.subst');
  }

  unify(tm: Tm): ?Tm {
    throw new Error('unimplemented: Module.unify');
  }
}

export class Note extends Record({
  name: null, // string;
  defn: null, // string;
}, 'note') {}

export class Definition extends Record({
  name: null, // string;
  defn: null, // Tm;
  visibility: null, // Visibility;
}, 'definition') {}

export class Property extends Record({
  name: null, // string;
  defn: null, // Tm;
}, 'property') {}

export class Example extends Record({
  name: null, // string;
  defn: null, // Tm;
}, 'example') {}
