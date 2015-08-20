// @flow
import { Expression, Type } from './tm';
import { mkStuck, mkSuccess, bind } from './evaluation';
import type { EvaluationResult } from './evaluation';
import Abt from './abt';
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

  constructor(binder: ?string, body: Abt, type: Expression): void {
    super(
      [ body ],
      [ [ binder ] ],
      type
    );
  }

  // map1(f: (x: AbtBase) => AbtBase): Lam {
  //   // XXX we don't know the type here!
  //   return new Lam(f(this.children[0]), this.type);
  // }

  evaluate(ctx: Context, x: Expression): EvaluationResult<Expression> {
    var [[ binder ]] = this.binders;
    var [ child ] = this.children;

    this.subst

    // TODO - move instantiation to ABT
    var newCtx = ctx;
    if (binder != null) {
      newCtx = add(ctx, binder, x);
    }

    return upcast(child, Expression).evaluate(newCtx);
  }
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
    return upcast(this.children[0], Expression);
  }

  codomain(): Expression {
    return upcast(this.children[1], Expression);
  }

//   map(f: (x: AbtBase) => AbtBase): Arr {
//     return new Arr(f(this.domain()), f(this.codomain()));
//   }

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
      super([ f,        x ],
            [ [ null ], [ null ] ],
            codomain
      );
    } else {
      throw new Error('runtime error in App constructor');
    }
  }

  func(): Expression {
    return upcast(this.children[0], Expression);
  }

  arg(): Expression {
    return upcast(this.children[1], Expression);
  }

  // map(f: (x: AbtBase) => AbtBase): App {
  //   return new App(f(this.func()), f(this.arg()));
  // }

  evaluate(ctx: Context): EvaluationResult<Expression> {
    return bind(
      this.arg().evaluate(ctx),
      arg => this.func().evaluate(ctx, arg)
    );
  }
}
