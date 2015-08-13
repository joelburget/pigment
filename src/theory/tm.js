// TODO:
// * revolutionize type inference
// * sigma types
// * user-defined types
// * organize
// * source positions? how does this relate to names?
import Immutable from 'immutable';
const { Record, Map, List } = Immutable;
import { Var, Abs, Tm, Abt } from './abt';


type ExpressionDesc = {
  type: string,
  arity: [number],
}


type Expression = {
  type: string,
  children: [Abt<Expression>],
}


export const EVar = {
  type: "var",
  arity: [],
  // inferred: true,
};

export function mkVar(v: string): Expression {
  return {
    type: "var",
    children: [ new Var(v) ],
  };
}


export const Type = {
  type: "type",
  arity: [],
  // inferred: false,
};

export const mkType = {
  type: "type",
  children: [],
};


export const Hole = {
  type: "hole",
  arity: [],
};

export function mkHole(name: ?string): Expression {
  return {
    type: "hole",
    children: [],
    name,
  };
}


export const Lam = {
  type: "lam",
  arity: [1],
  // inferred: false,
};

export function mkLam(name: string, body: Expression): Expression {
  return {
    type: "lam",
    // TODO perhaps name should have a type
    children: [ new Abs(name, new Tm(body)) ],
  };
}


export const App = {
  type: "app",
  arity: [0, 0],
  // inferred: true,
};

export function mkApp(f: Expression, x: Expression): Expression {
  return {
    type: "app",
    children: [ new Tm(f), new Tm(x) ],
  };
}


export const Pi = {
  type: "pi",
  arity: [0, 1],
  // inferred: false,
};

export function mkPi(domain: Expression, codomain: Expression) {
  return {
    type: "pi",
    children: [ new Tm(domain), new Tm(codomain) ],
  };
}

export const Sigma = {
  type: "sigma",
  arity: [0, 1],
  // inferred: false,
};

export function mkSigma(domain: Expression, codomain: Expression) {
  return {
    type: "sigma",
    children: [ new Tm(domain), new Tm(codomain) ],
  };
}


// TODO - how do we telescopify the arity (also for sigma)?
export const Tuple = {
  type: "tuple",
  arity: [0, 1],
  // inferred: false,
};

// TODO - second param is binding according to above
export function mkTuple(inl: Expression, inr: Expression) {
  return {
    type: "tuple",
    children: [ new Tm(inl), new Tm(inr) ],
  };
}
