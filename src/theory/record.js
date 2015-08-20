import { Expression, Type } from './tm';
import { mkSuccess } from './evaluation';
import { OrderedMap } from 'immutable';


export class Label extends Expression {
  static arity = [];
  static renderName = 'label';
  name: string;

  constructor(name: string): void {
    super([], [], Type.singleton); // XXX LabelType?
    this.name = name;
  }

  map(): Label {
    return this;
  }

  evaluate(): EvaluationResult<Expression> {
    return mkSuccess(this);
  }
}


export class Record extends Expression {
  // XXX arity
  static renderName = 'record';
  values: OrderedMap<string, Expression>;
  row: Row;

  constructor(values: OrderedMap<string, Expression>, row: Row) {
    super([], [], row);
    this.values = values;
    this.row = row;
  }

  map(): RowKind {
    return new Row(this.values.map(f));
  }

  evaluate(): EvaluationResult<Expression> {
    // TODO evaluate all children?
    return mkSuccess(this);
  }
}


export class RowKind extends Expression {
  static arity = [];
  static renderName = 'rowkind';
  static singleton = new RowKind();

  constructor(): void {
    super([], [], Type.singleton);
  }

  map(): RowKind {
    return this;
  }

  evaluate(): EvaluationResult<Expression> {
    return mkSuccess(this);
  }
}


export class Row extends Expression {
  // XXX arity
  static renderName = 'row';
  description: OrderedMap<string, Expression>;

  // pass in the types of each label:
  // {
  //   x: Int,
  //   y: Int,
  // }
  constructor(description: OrderedMap<string, Expression>): void {
    // XXX children
    super([], [], RowKind.singleton);
    this.description = description;
  }

  map(f: Function): Row {
    return new Row(this.description.map(f));
  }

  evaluate(): EvaluationResult<Expression> {
    // TODO evaluate all children?
    return mkSuccess(this);
  }
}


// _.l
// select : { l : a | r } -> a
export class SelectRow extends Expression {
  static renderName = 'selectrow';
  label: Label;
  type: Expression;
  record: Record;

  constructor(label: Label, type: Expression, record: Record): void {
    // XXX children
    super([], [], type);
    this.label = label;
    this.type = type;
    this.record = record;
  }

  map(f: Function): SelectRow {
    return new SelectRow(
      this.label.map(f),
      this.type.map(f),
      this.record.map(f)
    );
  }

  evaluate(): EvaluationResult<Expression> {
    return mkSuccess(this.record.values.get(this.label.name));
  }
}


// a -> { r } -> { l : a | r }
export class ExtendRow extends Expression {
  // static arity = XXX;
  static renderName = 'extendrow';
  record: Record;
  label: Label;
  value: Expression;

  constructor(record: Record, label: Label, value: Expression) {
    super([], []);
    this.record = record;
    this.label = label;
    this.value = value;
  }

  map(f): ExtendRow {
  }

  evaluate(): EvaluationResult<Expression> {
    const newRow = new Row(
      this.record.row.description.set(this.label.name, this.value.type)
    );
    const newRec = new Record(
      this.record.values.set(this.label.name, this.value),
      newRow
    );
    return mkSuccess(newRec);
  }
}


// { l : a | r } -> { r }
export class RestrictRow extends Expression {
  static renderName = 'restrictrow';

  constructor(record, label) {
    super([], []);
    this.record = record;
    this.label = label;
  }

  map(f): RestrictRow {
  }

  evaluate(): EvaluationResult<Expression> {
    const newRow = new Row(
      this.record.row.description.delete(this.label.name)
    );
    const newRec = new Record(
      this.record.values.delete(this.label.name),
      newRow
    );
    return mkSuccess(newRec);
  }
}



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
