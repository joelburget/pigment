import { Expression, Type } from './tm';
import { mkStuck, mkSuccess, bind } from './evaluation';
import type { EvaluationResult } from './evaluation';
import { Abt, Abs, Tm, mkTm } from './abt';
import { lookup, add } from './context';
import type { Context } from './context';


function upcast(x, cls) {
  if (x instanceof cls) {
    return (x: cls);
  } else {
    throw new Error('failed upcast!');
  }
}


export class Lam extends Expression {
  // $flowstatic
  static arity = [1];
  // $flowstatic
  static renderName = "lam";

//   constructor(binder: ?string, body: Expression, type: Expression): void {
//     super(
//       [ body     ],
//       [ [binder] ],
//       type
//     );
//   }

  // evaluate(ctx: Context, x: Expression): EvaluationResult<Expression> {
  //   var child: Abs = upcast(this.children[0], Abs);
  //   var tm: Tm = child.instantiate([x])
  //   var result: Abt = new Abt(tm.value.freevars, [tm]);
  //   var result_ = upcast(result, Expression);
  //   return mkSuccess(result_);
  // }
}


// export class Arr extends Expression {
//   // $flowstatic
//   static arity = [0, 0];
//   // $flowstatic
//   static renderName = "arr";

//   constructor(domain: Expression, codomain: Expression): void {
//     super([ domain,   codomain ],
//           [ [ null ], [ null ] ],
//           Type.singleton
//     );
//   }

//   domain(): Expression {
//     var child: Tm = upcast(this.children[0], Tm);
//     var value: Abt = child.value;
//     return upcast(value, Expression);
//   }

//   codomain(): Expression {
//     var child: Tm = upcast(this.children[1], Tm);
//     var value: Abt = child.value;
//     return upcast(value, Expression);
//   }

//   evaluate(ctx: Context): EvaluationResult<Expression> {
//     throw new Error("TODO - Arr.evaluate");
//   }
// }


// export class App extends Expression {
//   // $flowstatic
//   static arity = [0, 0];
//   // $flowstatic
//   static renderName = "app";

//   constructor(f: Expression, x: Expression): void {
//     var fType = f.type;
//     if (fType instanceof Arr) {
//       var codomain = fType.codomain();
//       super([ f,        x        ],
//             [ [ null ], [ null ] ],
//             codomain
//       );
//     } else {
//       throw new Error('runtime error in App constructor');
//     }
//   }

//   func(): Expression {
//     var child: Tm = upcast(this.children[0], Tm);
//     var value: Abt = child.value;
//     return upcast(value, Expression);
//   }

//   arg(): Expression {
//     var child: Tm = upcast(this.children[1], Tm);
//     var value: Abt = child.value;
//     return upcast(value, Expression);
//   }

//   evaluate(ctx: Context): EvaluationResult<Expression> {
//     return bind(
//       this.arg().evaluate(ctx),
//       arg => this.func().evaluate(ctx, arg)
//     );
//   }
// }
