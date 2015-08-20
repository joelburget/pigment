import { Expression, Type } from './tm';
import { mkSuccess } from './evaluation';
import { Arr, App } from './lambda';

export class External extends Expression {
  static renderName = 'external';
  static arity = [];

  constructor(e: any, type: Expression): void {
    super([], [], type);
    this.external = e;
  };

  map(): Expression {
    return this;
  }

  evaluate(ctx: Context): EvaluationResult<Expression> {
  }

  getType(ctx: Context) {
  }
}

// js primitives:
// * boolean
// * null
// * undefined
// * number
// * string
// * object (interesting interplay with tags / records)
//   - date
//   - array (typed arrays!)
//   - color, image, url!
// * function


export class JsExternalType extends Expression {
  typeName: string;

  constructor(typeName: string): void {
    super([], [], Type.singleton);
    this.typeName = typeName;
  }
}


export class JsBoolean extends External {
  external: boolean;
  static type = new JsExternalType('boolean');

  constructor(b: boolean): void {
    super(b, JsBoolean.type);
  }
}


export class JsExternalArr extends Expression {
  ty: Arr;

  constructor(ty: Arr): void {
    super([], [], Type.singleton);
    this.ty = ty;
  }
}


export class JsNumber extends External {
  external: number;
  static type = new JsExternalType('number');

  constructor(n: number): void {
    super(n, JsNumber.type);
  }
}


export class JsFunction extends External {
  external: Function;

  constructor(f: Function, ty: Arr) {
    super(f, new JsExternalArr(ty));
  }

  getResultType(): Expression {
    // const codomain = this.type.
  }
}


export class JsApp extends External {
  static arity = [0, 0];
  static renderName = "jsapp";

  constructor(f: JsFunction, x: External): void {
    super([ f, x ], undefined);
  }

  func(): Lam {
    return this.children[0];
  }

  arg(): Expression {
    return this.children[1];
  }

  map(f: Function): Expression {
    return new JsApp(f(this.func()), f(this.arg()));
  }

  evaluate(ctx: Context): EvaluationResult<Expression> {
    const f = this.func().external;
    const x = this.arg().external;

    // need to check if codomain is a function or regular external
    // - if function, we partially apply the parameter we've been given
    // - if external, we run it!
    if (this.type instanceof JsExternalArr) {
      return mkSuccess(new JsFunction(f.bind(null, x)));
    } else {
      // XXX need to get the actual constructor
      // * JsNumber
      // * JsString
      // * etc
      return mkSuccess(new External(f(x)));
    }
  }
}
