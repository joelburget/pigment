import expect from 'expect';
// import { varString, gensym, dummy, Var, Pi, Type, Lambda, App, Abstraction, inferType, equal } from '../src/theory/tm';
import { Var, Abs, Tm } from '../src/theory/abt';
import { Map, Set } from 'immutable';
import Immutable from 'immutable';


type Ast<Abt> =
  { type: "lam", body: Abt } |
  { type: "app", e1: Abt, e2: Abt } |
  { type: "let", e1: Abt, e2: Abt } |
  { type: "unit" }


function map(f, ast) {
  switch (ast.type) {
    case "lam":
      return {
        type: "lam",
        body: f(ast.body),
      };

    case "app":
    case "let":
      return {
        type: ast.type,
        e1: f(ast.e1),
        e2: f(ast.e2),
      };

    case "unit":
      return ast;
  }
}


function join(m, ast) {
  switch (ast.type) {
    case "lam":
      return ast.body

    case "app":
    case "let":
      return m.join(ast.e1, ast.e2);

    case "unit":
      return m.unit;

  }
}


class Ast {
  type: string;
  obj: Object;

  constructor(type: string, obj: ?Object) {
    this.type = type;
    this.obj = obj || {};
  }

  abtNodes() {
    const names = Object.getOwnPropertyNames(this.obj);
    return names.map(name => this.obj[name]);
  }
}


function expectImmutableIs(x, y) {
  expect(Immutable.is(x, y)).toBe(true, "`" + x + "` is not `" + y + "`");
}

describe('abt', () => {
  const xVar = new Var("x");
  const unit = new Tm(new Ast("unit"));
  // let y = () in y
  const let1 = new Tm(new Ast("let", {
    e: new Abs("y", unit),
  }));
  const let2 = new Tm(new Ast("let", {
    e: new Abs("x", new Var("y")),
  }));
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
