import expect from 'expect';
import { Type } from '../src/theory/tm';
import { mkSuccess, bind } from '../src/theory/evaluation';
import { Var, Abs, Tm } from '../src/theory/abt';
import { Lam, App, Arr } from '../src/theory/lambda';
import { empty as emptyCtx } from '../src/theory/context';
// import { Map, Set } from 'immutable';
// import Immutable from 'immutable';


describe('lambda', () => {
  const id = new Lam(
    new Abs('x', new Var('x')),
    new Arr(Type.singleton, Type.singleton)
  );

  const type = Type.singleton;

  /*
  const id = new Lam(
    'x',
    // XXX this is ALL broken
    // the variable right here doesn't know its type in a satisfactory way --
    // should maybe come from context?
    new EVar('x', EVar('X', Type.singleton)),
    // the Pi should use the structure of its bound variable ^ to generate its
    // type!
    ([ domain, codomain ]) => new Pi(Type.singleton, new Lam('X', new Arr(new EVar('X', new EVar('X')))))
  );

  const k = new Lam(
    'x',
    new Lam(
      'y',
      new EVar('x'),
      new Pi(Type.singleton, new Lam('Y', new Arr(new EVar('Y'), new EVar('X))))
    ),
    new Pi(Type.singleton, new Lam('X',
  );

  it('evaluates id', () => {
    expect(new App(id, Type.singleton).evaluate(emptyCtx))
      .toEqual(mkSuccess(Type.singleton));
  });

  it('evaluates k', () => {
    expect(new App(new App(k, Type.singleton), id).evaluate(emptyCtx))
      .toEqual(mkSuccess(Type.singleton));
  });
  */

  it('evaluates functions', () => {
    expect(id.evaluate(emptyCtx, type))
      .toEqual(mkStuck(id));

    expect(new App(id, Type.singleton).evaluate(emptyCtx))
      .toEqual(mkSuccess(Type.singleton));
  });
});
