import expect from 'expect';
import { mkSuccess, bind } from '../src/theory/tm';
import { Var, Abs, Tm } from '../src/theory/abt';
import { arr } from '../src/theory/lambda';
import { empty as emptyCtx } from '../src/theory/context';
import { JsBoolean, JsNumber, JsApp, JsFunction } from '../src/theory/external';
import { Map, Set } from 'immutable';
import Immutable from 'immutable';


describe('externals', () => {
  it('does booleans', () => {
    expect(new JsBoolean(true).external)
      .toBe(true);

    expect(new JsBoolean(false).external)
      .toBe(false);
  });

  it('does (increment) functions', () => {
    const numTy = JsNumber.type;
    const fun = new JsFunction(
      function(x) { return x + 1; },
      new arr(numTy, numTy)
    );
    const num = new JsNumber(0);

    expect(new JsApp(fun, num).evaluate(emptyCtx))
      .toEqual(mkSuccess(new JsNumber(1)));
  });

  it('does (curried) functions', () => {
    const numTy = JsNumber.type;
    const fun = new JsFunction(
      function(x, y) { return x + y; },
      new arr(numTy, arr(numTy, numTy))
    );
    const num0 = new JsNumber(0);
    const num1 = new JsNumber(1);

    const computation = bind(
      new JsApp(fun, num0).evaluate(emptyCtx),
      fun_ => new JsApp(fun_, num1).evaluate(emptyCtx)
    );

    expect(computation).toEqual(mkSuccess(num1));
  });
});
