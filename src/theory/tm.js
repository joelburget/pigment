// @flow
//
// TODO:
// * user-defined types
// * source positions? how does this relate to names?
import Abt from './abt';
import { lookup } from './context';
import type { Context } from './context';
import { mkStuck, mkSuccess } from './evaluation';
import type { EvaluationResult } from './evaluation';


export class Expression extends Abt {
  static renderName: string;

  type: Expression;

  // bleh. making an exception here since Lam.evaluate uses an extra parameter.
  // TODO figure out a better way.
  //
  // $flow-exception
  evaluate: ((ctx: Context) => EvaluationResult<Expression>) &
            ((ctx: Context, x: Expression) => EvaluationResult<Expression>);

  constructor(children: Array<Abt>,
              binders: Array<Array<?string>>,
              type: Expression): void {
    super(children, binders);
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
    super([], [], null);
    // circular json PITA
    // this.type = this;
  }

  rename(oldName: string, newName: string): Type {
    return this;
  }

  subst(t: Abt, x: string): Type {
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
    super([], [], type);
    this.name = name;
  }

  rename(oldName: string, newName: string): Hole {
    return this;
  }

  subst(t: Abt, x: string): Hole {
    return this;
  }

  evaluate(): EvaluationResult<Expression> {
    return mkStuck(this);
  }
}


export class Var extends Expression {
  // $flowstatic
  static arity = [];
  // $flowstatic
  static renderName = "hole";
  name: ?string;

  constructor(name: ?string, type: Expression): void {
    super([], [], type);
    this.name = name;
  }

  rename(oldName: string, newName: string): Var {
    return oldName === this.name ? new Var(newName, this.type) : this;
  }

  subst(t: Abt, x: string): Abt {
    return x === this.name ? t : this;
  }

  evaluate(): EvaluationResult<Expression> {
    return mkStuck(this);
  }
}
