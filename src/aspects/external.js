import { Record } from 'immutable';

import { Tm, Type } from '../theory/tm';
import { mkSuccess } from '../theory/evaluation';
import Arr from './lambda/data';
import App from './application/data';

export class External extends Record({ external: null, type: null }, 'external') {

  constructor(external: any, type: Tm): void {
    super({ external, type });
  };

  evaluate(ctx: Context): EvaluationResult<Tm> {
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


export class JsExternalType extends Record({ typeName: null }, 'externaltype') {
  constructor(typeName: string): void {
    super({ typeName });
  }
}


export class JsBoolean extends External {
  external: boolean;
  static type = new JsExternalType('boolean');

  constructor(b: boolean): void {
    super(b, JsBoolean.type);
  }
}


export class JsExternalArr extends Record({ ty: null }, 'externalarr') {
  constructor(ty: Arr): void {
    super({ ty });
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

  getResultType(): Tm {
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

  arg(): Tm {
    return this.children[1];
  }

  evaluate(ctx: Context): EvaluationResult<Tm> {
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
