// @flow

import { List, Record } from 'immutable';
import invariant from 'invariant';

import { register } from '../../theory/registry';
import { ADD_ENTRY, addEntry } from '../../commands/addEntry';

import type { Tm } from '../../theory/tm';
import type { EvaluationResult } from '../../theory/evaluation';
import type Edit, { Action } from '../../theory/edit';


export const MODULE_PUBLIC = 'module/MODULE_PUBLIC';
export const MODULE_PRIVATE = 'module/MODULE_PRIVATE';
// idris also has abstract, though i'm not sure when it's useful


export type Visibility = MODULE_PUBLIC | MODULE_PRIVATE;


const ModuleShape = Record({
  name: null,     // string
  contents: null, // List<Note | Definition | Property | Example>
  scratch: null,  // Note | Definition | Property | Example
}, 'module');


export default class Module extends ModuleShape {
  step(): EvaluationResult {
    throw new Error('unimplemented: Module.step');
  }

  subst(): Tm {
    throw new Error('unimplemented: Module.subst');
  }

  unify(): ?Tm {
    throw new Error('unimplemented: Module.unify');
  }

  actions(): List<Action> {
    return List([addEntry]);
  }

  performEdit(id: string): Edit {
    invariant(
      id === ADD_ENTRY,
      'Module only konws ADD_ENTRY'
    );

    throw new Error('Module.performEdit -- not implemented yet');
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

register('module', Module);
