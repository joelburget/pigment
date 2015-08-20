// @flow
//
// TODO:
// * user-defined types
// * source positions? how does this relate to names?
import { Var } from './abt';
import type { AbtBase as Abt } from './abt';
import { lookup } from './context';
import type { Context } from './context';
import { mkStuck, mkSuccess } from './evaluation';
import type { EvaluationResult } from './evaluation';


export class Expression {
  static arity: [number];
  static renderName: string;

  children: [ Abt ];
  type: Expression;

  map: (f: (x: Abt) => Abt) => Expression;

  // bleh. making an exception here since Lam.evaluate uses an extra parameter.
  // TODO figure out a better way.
  //
  // $flow-exception
  evaluate: (ctx: Context) => EvaluationResult<Expression>;

  constructor(children: [ Abt ], type: Expression): void {
    this.children = children;
    this.type = type;
  }
}


export class Type extends Expression {
  // $flowstatic
  static arity = [];
  // $flowstatic
  static renderName = "type";
  // $flowstatic
  static singleton = new Type();

  constructor(): void {
    // We make an exception here and allow the type to be null, so we don't end
    // up with Type referring to itself, because that makes testing harder
    // (involving JSON serialization).
    //
    // $flow-type-in-type
    super([], null);
    // circular json PITA
    // this.type = this;
  }

  map(): Type {
    return this;
  }

  evaluate(): EvaluationResult<Expression> {
    return mkSuccess(this);
  }
}


export class Hole extends Expression {
  // $flowstatic
  static arity = [];
  // $flowstatic
  static renderName = "hole";
  name: ?string;

  constructor(name: ?string, type: Expression): void {
    super([], type);
    this.name = name;
  }

  map(): Expression {
    return this;
  }

  evaluate(): EvaluationResult<Expression> {
    return mkStuck(this);
  }
}
