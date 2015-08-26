// @flow

import { OrderedMap, Record } from 'immutable';

import { Type } from './tm';
import type { Tm } from './tm';
import { mkSuccess } from './evaluation';
import type { EvaluationResult } from './evaluation';
import type { AbsRef, Ref } from './ref';
import type { Context } from './context';


// record primitive operations
// * select : { l : a | r } -> a
//   r.l
//   distance p = sqrt (p.x * p.x + p.y * p.y)
// * restrict : { l : a | r } -> { r }
//   r - l
//   update:
//     { l := x | r } = { l = x | r - l }
//   rename:
//     { l <- m | r } = { l = r.m | r - m }
// * extend : a -> { r } -> { l : a | r }
//   { l = e | r }
//   origin = { x = 0 | { y = 0 | {} } }
//   origin = { x = 0, y = 0 }


var labelShape = Record({
  name: null,
}, 'label');

export class Label extends labelShape {

  constructor(name: string): void {
    super({ name });
  }

  getType(): Tm {
    return Type.singleton;
  }

  evaluate(root: AbsRef, ctx: Context): EvaluationResult {
    return mkSuccess(this);
  }
}


var recordShape = Record({
  values: null,
  type: null,
}, 'rec');

export class Rec extends recordShape {

  constructor(values: OrderedMap<string, Tm>, type: Row) {
    super({ values, type });
  }

  getType(): Tm {
    return this.type;
  }

  evaluate(root: AbsRef, ctx: Context): EvaluationResult {
    // TODO evaluate all children?
    return mkSuccess(this);
  }
}


export class RowKind {
  static name: string;

  // $flowstatic
  static singleton: RowKind = new RowKind();

  getType(): Tm {
    return Type.singleton;
  }

  evaluate(root: AbsRef, ctx: Context): EvaluationResult {
    return mkSuccess(this);
  }

  subst(root: AbsRef, ref: Ref, value: Tm): Tm {
    return this;
  }
}

RowKind.name = 'rowkind';


var rowShape = Record({
  description: null,
}, 'row');

export class Row extends rowShape {

  // pass in the types of each label:
  // {
  //   x: Int,
  //   y: Int,
  // }
  constructor(description: OrderedMap<string, Tm>): void {
    super({ description });
  }

  getType(): Tm {
    return Type.singleton;
  }

  subst(root: AbsRef, ref: Ref, value: Tm): Tm {
    throw new Error('unimplemented Row.subst');
  }

  evaluate(root: AbsRef, ctx: Context): EvaluationResult {
    // TODO evaluate all children?
    return mkSuccess(this);
  }
}


var selectRowShape = Record({
  label: null,
  rec: null,
  type: null,
}, 'selectrow');

// _.l
// select : { l : a | r } -> a
export class SelectRow extends selectRowShape {

  constructor(label: Label, type: Tm, rec: Rec): void {
    // XXX children
    super({ label, type, rec });
  }

  getType(): Tm {
    return this.type;
  }

  evaluate(): EvaluationResult {
    return mkSuccess(this.rec.values.get(this.label.name));
  }
}


var extendRowShape = Record({
  rec: null,
  label: null,
  value: null,
}, 'extendrow');

// a -> { r } -> { l : a | r }
export class ExtendRow extends extendRowShape {

  constructor(rec: Rec, label: Label, value: Tm) {
    super({ rec, label, value });
  }

  getType(): Tm {
    var { rec, label, value } = this;
    return new Row(
      rec.type.description.set(label.name, value.type)
    );
  }

  evaluate(): EvaluationResult {
    var { rec, label, value } = this;
    var newRec = new Rec(
      rec.values.set(label.name, value),
      this.getType()
    );
    return mkSuccess(newRec);
  }
}


var restrictRowShape = Record({
  rec: null,
  label: null,
  type: null,
}, 'restrictrow');

// { l : a | r } -> { r }
export class RestrictRow extends restrictRowShape {

  constructor(rec: Rec, label: Label) {
    super({ rec, label });
  }

  getType(): Tm {
    var { rec, label } = this;
    return new Row(
      rec.type.description.delete(label.name)
    );
  }

  evaluate(): EvaluationResult {
    var { rec, label } = this;
    var newRec = new Rec(
      rec.values.delete(label.name),
      this.getType()
    );
    return mkSuccess(newRec);
  }
}
