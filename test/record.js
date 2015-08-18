import expect from 'expect';
import { Var, Abs, Tm } from '../src/theory/abt';
import { Label, Record, RowKind, Row, SelectRow, ExtendRow, RestrictRow }
  from '../src/theory/record';
import { Map, Set, OrderedMap } from 'immutable';
import Immutable from 'immutable';
import { JsNumber } from '../src/theory/external';
import { empty as emptyCtx } from '../src/theory/context';
import { mkSuccess, bind } from '../src/theory/evaluation'


describe('records', () => {
  const numTy = JsNumber.type;

  const xLabel = new Label('x');
  const yLabel = new Label('y');
  const zLabel = new Label('z');

  const xRow = new Row(OrderedMap({ x: numTy }));
  const xRec = new Record(OrderedMap({
    x: new JsNumber(0)
  }),
  xRow);

  const xyRow = new Row(OrderedMap({
    x: numTy,
    y: numTy,
  }));
  const xyRec = new Record(OrderedMap({
    x: new JsNumber(0),
    y: new JsNumber(1),
  }),
  xyRow);

  const xyzRow = new Row(OrderedMap({
    x: numTy,
    y: numTy,
    z: numTy,
  }));
  const xyzRec = new Record(OrderedMap({
    x: new JsNumber(0),
    y: new JsNumber(1),
    z: new JsNumber(2),
  }),
  xyzRow);

  it('creates and selects simple records', () => {
    // { x: 0, y: 1 }.x -> 0 : JsNumber
    const selectX = new SelectRow(xLabel, numTy, xyRec);
    expect(selectX.evaluate(emptyCtx))
      .toEqual(mkSuccess(new JsNumber(0)));
    expect(selectX.type)
      .toEqual(numTy);

    // { x: 0, y: 1 }.x -> 1 : JsNumber
    expect(new SelectRow(yLabel, numTy, xyRec).evaluate(emptyCtx))
      .toEqual(mkSuccess(new JsNumber(1)));
  });

  it('extends', () => {
    const extendedRec = new ExtendRow(xyRec, zLabel, new JsNumber(2));
    const evaluated = extendedRec.evaluate(emptyCtx).value;

    expect(
      Immutable.is(evaluated.type.description, xyzRow.description)
    ).toBe(true);

    // TODO this doesn't work because the JsNumbers are not object equal
    // expect(
    //   Immutable.is(evaluated.values, xyzRec.values)
    // ).toBe(true);
  });

  it('{ y: 1 | x: 0 }.y -> 1', () => {
    const expression = bind(
      new ExtendRow(xRec, yLabel, new JsNumber(1)).evaluate(emptyCtx),
      rec => new SelectRow(
        yLabel,
        numTy,
        rec
      )
    ).evaluate(emptyCtx);

    expect(expression.value).toEqual(new JsNumber(1));
  });

  it('{ y: 1 | x: 0 }.x -> 0', () => {
    const expression = bind(
      new ExtendRow(xRec, yLabel, new JsNumber(1)).evaluate(emptyCtx),
      rec => new SelectRow(
        xLabel,
        numTy,
        rec
      )
    ).evaluate(emptyCtx);

    expect(expression.value).toEqual(new JsNumber(0));
  });

  it('restricts xy', () => {
    const restrictedRec = new RestrictRow(xyRec, yLabel);
    const evaluated = restrictedRec.evaluate(emptyCtx).value;

    expect(
      Immutable.is(evaluated.type.description, xRow.description)
    ).toBe(true);
  });

  it('restricts xyz', () => {
    const restrictedRec = new RestrictRow(
      xyzRec,
      zLabel
    );
    const evaluated = restrictedRec.evaluate(emptyCtx).value;

    expect(
      Immutable.is(evaluated.type.description, xyRow.description)
    ).toBe(true);
  });
});
