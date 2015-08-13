// utilities for going up and down the type ladder
//
// why is this important?
//
// getType is *the* way to extract the type of an expression! this is useful in
// a million ways, namely:
// * informing the user the type of the selected expression
// * etc (TODO)
//
// getInhabitants allows us to program for the user! given a type we can
// program for the user by filling in its unique inhabitant!

import { Seq } from 'immutable';
import type { Context } from './context';
import { lookupType, add } from './context';
import { mkPi, mkSigma, mkApp, mkType } from './tm';


export function getType(ctx: Context, e: Expression) {
  switch (e.type) {
    case "var":


    // * : *
    case "type":
      return e;

    case "hole":
      // TODO add type to holes (and every other term?)
      return e.type;

    case "lam":
      const [ abs ] = e.children;
      const varTy = undefined;
      // XXX we really need to annotate variables with types in abt
      // might be enough to add a type annotation to Abs
      const newCtx = add(ctx, abs.name, varTy);
      const resultTy = getType(newCtx, abs.body);

      return mkPi(varTy, resultTy);

    case "app":
      const [ f, x ] = e.children;
      const fTy = getType(ctx, f); // Pi(X; \x -> ?)
      const xTy = getType(ctx, x);

      // TODO no way this is right...
      return getType(ctx, mkApp(mkApp(fTy, xTy), x));

    case "pi":
    case "sigma":
      return mkType;

    case "tuple":
      const [ inl, inr ] = e.children;
      const lty = getType(ctx, inl);
      const newCtx = add(ctx, inr.name, lty);
      const rty = getType(newCtx, inr.body);

      return mkSigma(lty, rty);
  }
}


// TODO how to solve the problem of variables filling any hole?
export function getInhabitants(ctx: Context, e: Expression) {
  // TODO
  return Seq;
}
