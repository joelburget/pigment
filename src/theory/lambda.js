
import { Expression, Type } from './tm';
import { mkStuck, mkSuccess, bind } from './evaluation';
import type { EvaluationResult } from './evaluation';
import { Abt, Abs, Tm, mkTm } from './abt';
import { lookup, add } from './context';
import type { Context } from './context';
import upcast from './upcast';


export class Lam extends Expression {
  // $flowstatic
  static arity = [1];
  // $flowstatic
  static renderName = "lam";

  constructor(binder: ?string, body: Expression, type: Expression): void {
    super(
      [ body     ],
      [ [binder] ],
      type
    );
  }


  evaluate(ctx: Context, x: Expression): EvaluationResult<Expression> {
    return this.getChildAbs(0, [x]);
  }

//   evaluate(ctx: Context, x: Expression): EvaluationResult<Expression> {
//     var child: Abs = upcast(this.children[0], Abs);
//     var tm: Tm = child.instantiate([x])
//     var result: Abt = new Abt(tm.value.freevars, [tm]);
//     var result_ = upcast(result, Expression);
//     return mkSuccess(result_);
//   }
}


export class Arr extends Expression {
  // $flowstatic
  static arity = [0, 0];
  // $flowstatic
  static renderName = "arr";

  constructor(domain: Expression, codomain: Expression): void {
    super([ domain,   codomain ],
          [ [ null ], [ null ] ],
          Type.singleton
    );
  }

  domain(): Expression {
    return this.getChildTm(0);
  }

  codomain(): Expression {
    return this.getChildTm(1);
  }

  evaluate(ctx: Context): EvaluationResult<Expression> {
    throw new Error("TODO - Arr.evaluate");
  }
}


export class App extends Expression {
  // $flowstatic
  static arity = [0, 0];
  // $flowstatic
  static renderName = "app";

  constructor(f: Expression, x: Expression): void {
    var fType = f.type;
    if (fType instanceof Arr) {
      var codomain = fType.codomain();
      super([ f,        x        ],
            [ [ null ], [ null ] ],
            codomain
      );
    } else {
      throw new Error('runtime error in App constructor');
    }
  }

  func(): Expression {
    return this.getChildTm(0);
  }

  arg(): Expression {
    return this.getChildTm(1);
  }

  evaluate(ctx: Context): EvaluationResult<Expression> {
    return bind(
      this.arg().evaluate(ctx),
      arg => this.func().evaluate(ctx, arg)
    );
  }
}
