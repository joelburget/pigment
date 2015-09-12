import transit from 'transit-js';
import { ModuleState } from './data';
import { Module, Note, Definition, Property, Example } from './data';


export const writeHandlers = [
  ModuleState, transit.makeWriteHandler({
    tag: () => 'modulestate',
    rep: v => [v.module, v.mouseSelection],
  }),

  Module, transit.makeWriteHandler({
    tag: () => 'module',
    rep: v => [v.name, v.contents],
  }),
  Note, transit.makeWriteHandler({
    tag: () => 'note',
    rep: v => [v.name, v.defn],
  }),
  Definition, transit.makeWriteHandler({
    tag: () => 'definition',
    rep: v => [v.name, v.defn, v.visibility],
  }),
  Property, transit.makeWriteHandler({
    tag: () => 'property',
    rep: v => [v.name, v.defn],
  }),
  Example, transit.makeWriteHandler({
    tag: () => 'example',
    rep: v => [v.name, v.defn],
  }),
];


export const readHandlers = {
  'modulestate': ([module, mouseSelection]) =>
    new ModuleState({ module, mouseSelection }),

  'module': ([name, contents]) => new Module({ name, contents }),
  'note': ([name, defn]) => new Note({ name, defn }),
  'definition': ([name, defn, visibility]) => new Definition({ name, defn, visibility }),
  'property': ([name, defn]) => new Property({ name, defn }),
  'example': ([name, defn]) => new Example({ name, defn }),
};
