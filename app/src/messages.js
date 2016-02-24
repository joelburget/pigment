// @flow
import type { Record } from 'immutable';
import type { Component } from 'react';

import type Firmament, {
  Path,
} from './models/Firmament';


export const NEW_FIELD = 'NEW_FIELD';
export const FILL_HOLE = 'FILL_HOLE';

// ../actions (these have buttons)
export const REMOVE_FIELD = 'REMOVE_FIELD';
export const POKE_HOLE = 'POKE_HOLE';

// eliminator stuff
export const UNIFY = 'UNIFY';
export const STEP = 'STEP';

export const IMPLEMENTATION_UPDATED = 'IMPLEMENTATION_UPDATED';
export const REFERENCE_UPDATED = 'REFERENCE_UPDATED';

// variants
export const ADD_VARIANT = 'ADD_VARIANT';
export const REMOVE_VARIANT = 'REMOVE_VARIANT';

// symbology

// * introductions are just dumb data.
// * computation happens in eliminators.
// * introductions and eliminations know how to form and have semantic
//   modification operations
export const INTRODUCTION = 'INTRODUCTION';
export const ELIMINATION = 'ELIMINATION';

export type Introduction = {
  name: string;
  symbol: Symbol;
  type: 'INTRODUCTION' | 'ELIMINATION';
  minLevel: number;
  // handlers: recordTyHandlers,
  render: Component;
  data: Record;
};

// unifies with anything!
export const METAVAR = 'METAVAR';

/*
export type IntroProtocol = {
  [FILL_HOLE]: Function;
};

export type ElimProtocol = {
  [STEP]: Function;
};
*/


export type GlobalContext<A> = {
  global: Firmament;
  signal: (path: Path, signal: A) => void;
};

export type Reference = {
  tag: 'REFERENCE';

  parent: Symbol;
  name: string;
  // location: Symbol;
};

export type Immediate = {
  tag: 'IMMEDIATE';
  location: Symbol;
};

export type ImmediateFill = {
  tag: 'IMMEDIATE_FILL';
  introduction: Introduction;
};

export type SubLocation = Reference | Immediate;

export type FillHoleSignal = {
  action: 'FILL_HOLE';
  referer: Symbol;
  holeName: string;

  fill: ImmediateFill | Reference;
};

export type PokeHoleSignal = {
  action: 'POKE_HOLE';
  path: Path;
};

export type UnifySignal = {
  action: 'UNIFY';
  primary: Symbol;
  other: Symbol;
  path: Path;
};

export type NewFieldSignal = {
  action: 'NEW_FIELD';
  name: string;
  path: Path;
};

export type RemoveFieldSignal = {
  action: 'REMOVE_FIELD';
  name: string;
  path: Path;
};

export type ImplementationUpdatedSignal = {
  action: 'IMPLEMENTATION_UPDATED';
  target: Symbol;
  signal: AnySignal;
};

export type ReferenceUpdatedSignal = {
  action: 'REFERENCE_UPDATED';
  referer: Symbol;
  original: Symbol;
  name: string;
  signal: AnySignal;
};

export type AddVariantSignal = {
  action: 'ADD_VARIANT';
  path: Path;
  tag: string;
  type: Symbol;
};

export type RemoveVariantSignal = {
  action: 'REMOVE_VARIANT';
  path: Path;
  tag: string;
};

export type AnySignal
  = NewFieldSignal
  | RemoveFieldSignal
  | ImplementationUpdatedSignal
  | ReferenceUpdatedSignal
  | AddVariantSignal
  | RemoveVariantSignal;

export type RowLike = {
  NEW_FIELD: Function;
  REMOVE_FIELD: Function;
};
