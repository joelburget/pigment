import expect from 'expect';

import { mkSuccess, bind } from '../theory/tm';
import Arr from './function/data';
import { JsBoolean, JsNumber, JsApp, JsFunction } from './external';

const disable = () => {};

disable('externals', () => {
  it('does booleans', () => {
    expect(new JsBoolean(true).external)
      .toBe(true);

    expect(new JsBoolean(false).external)
      .toBe(false);
  });

  it('does (increment) functions', () => {
    const numTy = JsNumber.type;
    const fun = new JsFunction(
      x => x + 1, // eslint-disable-line id-length
      new Arr(numTy, numTy)
    );
    const num = new JsNumber(0);

    expect(new JsApp(fun, num).step([]))
      .toEqual(mkSuccess(new JsNumber(1)));
  });

  it('does (curried) functions', () => {
    const numTy = JsNumber.type;
    const fun = new JsFunction(
      (x, y) => x + y, // eslint-disable-line id-length
      new Arr(numTy, Arr(numTy, numTy))
    );
    const num0 = new JsNumber(0);
    const num1 = new JsNumber(1);

    const computation = bind(
      new JsApp(fun, num0).step([]),
      fun_ => new JsApp(fun_, num1).step([])
    );

    expect(computation).toEqual(mkSuccess(num1));
  });
});
