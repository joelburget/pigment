import expect from 'expect';
import { Type } from '../src/theory/tm';
import { mkSuccess, mkStuck, bind } from '../src/theory/evaluation';
import { mkVar, mkTm } from '../src/theory/abt';
import { Lam, App, Arr } from '../src/theory/lambda';
import { empty as emptyCtx } from '../src/theory/context';


describe('lambda', () => {
  const type = Type.singleton;

  const id = new Lam(
    'x',
    mkVar('x'),
    new Arr(type, type)
  );

//   const k = new Lam(
//     'x',
//     new Lam(
//       'y',
//       new Var('x'),
//       new Arr(
//         type,
//         new Lam(
//           'Y',
//           new Var('x'),
//           new Arr(new Var('Y', new Var('X')))
//         )
//       )
//     ),
//     new Arr(
//   );

  it('evaluates id', () => {
    expect(new App(id, type).evaluate(emptyCtx))
      .toEqual(mkSuccess(type));
  });

//   it('evaluates k', () => {
//     expect(new App(new App(k, type), id).evaluate(emptyCtx))
//       .toEqual(mkSuccess(type));
//   });

  // it('evaluates functions', () => {
  //   expect(id.evaluate(emptyCtx, type))
  //     .toEqual(mkStuck(id));

  //   expect(new App(id, type).evaluate(emptyCtx))
  //     .toEqual(mkSuccess(type));
  // });
});
