// TODO:
// * user-defined types
// * source positions? how does this relate to names?
import { Var } from './abt';
import type { Abt } from './abt';
import { lookup } from './context';
import { mkStuck, mkSuccess } from './evaluation';


export class Expression {
  arity: [number];
  children: [ Abt<Expression> ];
  type: Expression;
  renderName: string;

  // map: (Abt<Expression> => Abt<Expression>) => Expression;
  // evaluate: Context => EvaluationResult<Expression>;

  constructor(children: [ Abt<Expression> ], type: Expression): void {
    this.children = children;
    this.type = type;
  }
}


// export class EVar extends Expression {
//   static arity = [];
//   static renderName = 'var';

//   constructor(name: string, type: Expression): void {
//     super([ new Var(name) ], type);
//   }

//   map(f): Expression {
//     let v = new EVar(this.children[0].name);
//     v.children = v.children.map(f);
//     return v;
//   }

//   evaluate(ctx: Context): EvaluationResult<Expression> {
//     return lookup(ctx, this.children[0].name).evaluate(ctx);
//   }
// }


export class Type extends Expression {
  static arity = [];
  static renderName = "type";
  static singleton = new Type();

  constructor(): void {
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
  static arity = [];
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
