import { Record } from 'immutable';

import { Tm } from '../theory/tm';
import { mkSuccess } from '../theory/evaluation';
import Lam, { Arrow } from './lambda/data';

import type { EvaluationResult } from '../../theory/evaluation';


export class External extends Record({ external: null, type: null }, 'external') {

  constructor(external: any, type: Tm): void {
    super({ external, type });
  }

  step(): EvaluationResult<Tm> {
    throw new Error('External.step not yet implemented');
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

  constructor(bool: boolean): void {
    super(bool, JsBoolean.type);
  }
}


export class JsExternalArr extends Record({ ty: null }, 'externalarr') {
  constructor(ty: Arrow): void {
    super({ ty });
  }
}


export class JsNumber extends External {
  external: number;
  static type = new JsExternalType('number');

  constructor(num: number): void {
    super(num, JsNumber.type);
  }
}


export class JsFunction extends External {
  external: Function;

  constructor(fun: Function, ty: Arrow) {
    super(fun, new JsExternalArr(ty));
  }

  getResultType(): Tm {
    // const codomain = this.type.
  }
}


export class JsApp extends External {
  static arity = [0, 0];
  static renderName = 'jsapp';

  constructor(fun: JsFunction, arg: External): void {
    super([ fun, arg ], undefined);
  }

  func(): Lam {
    return this.children[0];
  }

  arg(): Tm {
    return this.children[1];
  }

  step(): EvaluationResult<Tm> {
    const fun = this.func().external;
    const arg = this.arg().external;

    // need to check if codomain is a function or regular external
    // - if function, we partially apply the parameter we've been given
    // - if external, we run it!
    if (this.type instanceof JsExternalArr) {
      return mkSuccess(new JsFunction(fun.bind(null, arg)));
    } else {
      // XXX need to get the actual constructor
      // * JsNumber
      // * JsString
      // * etc
      return mkSuccess(new External(fun(arg)));
    }
  }
}
