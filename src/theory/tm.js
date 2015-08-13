// TODO:
// * user-defined types
// * source positions? how does this relate to names?
import { Var, Abs, Tm, Abt } from './abt';


type EvaluationResult<A>
  = { type: 'success', value: A }
  | { type: 'stuck', value: A }


export function mkSuccess(e) {
  return {
    type: 'success',
    value: e,
  };
}


export function mkStuck(e) {
  return {
    type: 'stuck',
    value: e,
  };
}


export class Expression {
  arity: [number];
  children: [ Abt<Expression> ];
  // map: (Abt<Expression> => Abt<Expression>) => Expression;
  // evaluate: Context => EvaluationResult<Expression>;
}


export class EVar extends Expression {
  static arity = [];

  constructor(name: string) {
    super(arguments);
    this.children = [ new Var(name) ];
  }

  map(f) {
    let v = new EVar(this.children[0].name);
    v.children = v.children.map(f);
    return v;
  }

  evaluate(ctx: Context) {
    return lookupValue(ctx, this.children[0].name).evaluate();
  }
}


export class Type extends Expression {
  static arity = [];
  static singleton = new Type();

  constructor() {
    super(arguments);
    this.children = [];
  }

  map(f) {
    return this;
  }

  evaluate(ctx: Context) {
    return mkSuccess(this);
  }
}


export class Hole extends Expression {
  static arity = [];
  name: ?string;

  constructor(name: ?string): void {
    super(arguments);
    this.children = [];
    this.name = name;
  }

  map(f) {
    return this;
  }

  evaluate(ctx: Context) {
    return mkStuck(this);
  }
}
