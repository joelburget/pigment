import expect from 'expect';
import { Map, OrderedMap } from 'immutable';

import { Label, Rec, Row, SelectRow, ExtendRow, RestrictRow }
  from './data';
import { JsNumber } from '../external';
import { mkSuccess, bind } from '../../theory/evaluation';

import expectImmutableIs from '../../testutil/expectImmutableIs';


const emptyCtx = Map();


describe('records', () => {
  const numTy = JsNumber.type;

  const xLabel = new Label('x');
  const yLabel = new Label('y');
  const zLabel = new Label('z');

  const xRow = new Row(OrderedMap({ x: numTy }));
  const xRec = new Rec(
    OrderedMap({
      x: new JsNumber(0)
    }),
    xRow
  );

  const xyRow = new Row(OrderedMap({
    x: numTy,
    y: numTy,
  }));
  console.log(xyRow);
  const xyRec = new Rec(
    OrderedMap({
      x: new JsNumber(0),
      y: new JsNumber(1),
    }),
    xyRow
  );

  const xyzRow = new Row(OrderedMap({
    x: numTy,
    y: numTy,
    z: numTy,
  }));
  const xyzRec = new Rec(OrderedMap({
    x: new JsNumber(0),
    y: new JsNumber(1),
    z: new JsNumber(2),
  }),
  xyzRow);

  it('creates and selects simple records', () => {
    // { x: 0, y: 1 }.x -> 0 : JsNumber
    const selectX = new SelectRow(xLabel, numTy, xyRec);
    expect(selectX.step([]))
      .toEqual(mkSuccess(new JsNumber(0)));
    expect(selectX.type)
      .toEqual(numTy);

    // { x: 0, y: 1 }.x -> 1 : JsNumber
    expect(new SelectRow(yLabel, numTy, xyRec).step(emptyCtx))
      .toEqual(mkSuccess(new JsNumber(1)));
  });

  it('extends', () => {
    const extendedRec = new ExtendRow(xyRec, zLabel, new JsNumber(2));
    const stepped = extendedRec.step(emptyCtx).value;

    expectImmutableIs(
      stepped.type,
      xyzRow
    );

    // TODO this doesn't work because the JsNumbers are not object equal
    // expectImmutableIs(
    //   stepped.values,
    //   xyzRec.values
    // );
  });

  it('{ y: 1 | x: 0 }.y -> 1', () => {
    const expression = bind(
      new ExtendRow(xRec, yLabel, new JsNumber(1)).step(emptyCtx),
      rec => new SelectRow(
        yLabel,
        numTy,
        rec
      )
    ).step([]);

    expect(expression.value).toEqual(new JsNumber(1));
  });

  it('{ y: 1 | x: 0 }.x -> 0', () => {
    const expression = bind(
      new ExtendRow(xRec, yLabel, new JsNumber(1)).step(emptyCtx),
      rec => new SelectRow(
        xLabel,
        numTy,
        rec
      )
    ).step(emptyCtx);

    expect(expression.value).toEqual(new JsNumber(0));
  });

  it('restricts xy', () => {
    const restrictedRec = new RestrictRow(xyRec, yLabel);
    const stepped = restrictedRec.step(emptyCtx).value;

    expectImmutableIs(
      stepped.type,
      xRow
    );
  });

  it('restricts xyz', () => {
    const restrictedRec = new RestrictRow(
      xyzRec,
      zLabel
    );
    const stepped = restrictedRec.step(emptyCtx).value;

    expectImmutableIs(
      stepped.type,
      xyRow
    );
  });
});
