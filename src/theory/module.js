// @flow

import { Record } from 'immutable';

export class Module extends Record({
  name: null,
  contents: null,
}, 'module') {}

export class Note extends Record({
  name: null, // string;
  defn: null, // string;
}, 'note') {}

export class Definition extends Record({
  name: null, // string;
  defn: null, // Tm;
}, 'definition') {}

export class Property extends Record({
  name: null, // string;
  defn: null, // Tm;
}, 'property') {}

export class Example extends Record({
  name: null, // string;
  defn: null, // Tm;
}, 'example') {}
