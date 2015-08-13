import expect from 'expect';
// import { varString, gensym, dummy, Var, Pi, Type, Lambda, App, Abstraction, inferType, equal } from '../src/theory/tm';
import { Var, Abs, Tm } from '../src/theory/abt';
import { Map, Set } from 'immutable';
import Immutable from 'immutable';


type Ast<Abt> =
  { type: "lam", children: [ Abt ] } |
  { type: "app", children: [ Abt, Abt ] } |
  { type: "let", children: [ Abt, Abt ] } |
  { type: "unit", children: [] }

// value : pi, type, lambda
// neutral: var, app


class Ast {
  type: string;
  children: [ Abt ];

  constructor(type: string, children: [ Abt ]) {
    this.type = type;
    this.children = children;
  }
}


function expectImmutableIs(x, y) {
  expect(Immutable.is(x, y)).toBe(true, "`" + x + "` is not `" + y + "`");
}

describe('abt', () => {
  const xVar = new Var("x");
  const unit = new Tm(new Ast("unit", []));
  // let y = () in y
  const let1 = new Tm(new Ast("let", [
    new Abs("y", unit),
  ]));
  const let2 = new Tm(new Ast("let", [
    new Abs("x", new Var("y")),
  ]));
  const lambda1 = new Abs("x", new Var("x"));
  const lambda2 = new Abs("x", new Var("y"));

  it('knows free variables', () => {
    expectImmutableIs(
      xVar.freevars,
      Set(["x"])
    );

    expectImmutableIs(
      lambda1.freevars,
      Set([])
    );

    expectImmutableIs(
      lambda2.freevars,
      Set(["y"])
    );

    expectImmutableIs(
      let1.freevars,
      Set([])
    );

    expectImmutableIs(
      let2.freevars,
      Set(["y"])
    );
  });

  it('renames', () => {
  });
});
