import Immutable from 'immutable';
const { Record, Map, List } = Immutable;
import { Var, Abs, Tm } from './abt';
import { Lam, EVar, App, Type, Pi, Sigma } from './tm';


// two important things:
// * value vs neutral
// * inferred vs checked
//
// As shown by Watkins et al. (2004), bidirectional typechecking can be
// understood in terms of the normalization of intuitionistic type theory, in
// which normal forms correspond to the checking mode of bidirectional
// typechecking, and neutral (or atomic) terms correspond to the synthesis
// mode. This enables a proof of the elegant property that type annotations are
// only necessary at reducible expressions, and that normal forms need no
// annotations at all.


// TODO consider adding positions to Expression
// export class Ast {
//   type: Construction;
// }

//                            value        type

// TODO - judgements file / directory
export function inferType(ctx: Context, expr: Expression): Expression {
  if (expr.type === "lam") {
    // lambda inhabits pi

    // issue:
    // - blinding building constraints which propagate up
    //
    // solution:
    // - bidirectionality
    // - no, not okay with only inferring or checking at any given node
    const domain = Var("lam inference");
    // const codomain =
    const binding = inferAbtType(ctx, expr.children[0]);

    // XXX can't really infer lambda type -- need its type from context
    return {
      ...Pi,
      children: [
        inferAbtType(ctx, e1)
      ]
    };

  } else if (expr.type === "var") {
    // TODO what if undefined -- need to give back a variable
    return lookupType(ctx, expr);

  } else if (expr.type === "app") {
    const [ e1, e2 ] = expr.children;
    const funcTy = inferType(e1);
    const [ domain, codomain ] = funcTy.children;

    if (funcTy.type === "pi") {
      // check that the argument is the expected type
      // TODO we shouldn't really need to do this
      checkType(ctx, e2, domain);
      return codomain;
    } else {
      throw new Error("applying a non-function");
    }

  // XXX this isn't an ast form... how do we infer the type of a variable?
  // maybe every ast form is an introduction and is checked?
  } else if (expr.type === "type" ||
             expr.type === "pi" ||
             expr.type === "sigma") {
    return Type;

  } else {
    console.log("can't infer this thing", expr);
    throw new Error("can't infer this thing");
  }
}

// "As is standard in the proof-theoretic presentations of bidirectional
// typechecking, each of the introduction forms in our calculus has a
// corresponding checking rule."
export function checkType(ctx: Context,
                          expr: Expression,
                          // TODO - return some evidence!
                          type: Expression): void {
  if (expr.type === "lam" && type.type === "pi") {
    // XXX unabs?
    const [ x, expr_ ] = unabs(type);
    const [ domain, codomain ] = type.children;

    // assume the variable has the domain type
    const newCtx = extend(x, domain, null, ctx);

    check(newCtx, expr_, codomain);

  } else if (expr.type === "lam") {
    throw new Error("expected lambda to be an arrow");

  } else if (type.type === "pi") {
    throw new Error("pi expected a lambda");

  } else if (type.type === "sigma") {
    throw new Error("sigmas don't have inhabitants yet!");

  // TODO level-out branches
  } else if (type.type === "type") {
    // XXX what about app?
    if (expr.type === "pi") {
      const [ domain, codomain ] = pi.children;
      checkType(ctx, domain, Type);

      // XXX binding var?
      const newCtx = extend(pi.bindingVar, domain, null, ctx);
      // XXX just check it's lam(domain, codomain)?
      checkType(newCtx, codomain, null);

    } else if (expr.type === "sigma") {
      // XXX same questions here

    } else if (expr.type === "type") {
      // finally, an easy one. type-in-type all the way.
      return true;
    }

  } else {
    throw new Error("can't check this thing");
  }
}


// normalize the given expression in context
// - beta-reduction
// - definition unfolding
export function normalize(ctx: Context, e: Expression) {
  if (e instanceof Var) {
    const val = lookupValue(ctx, e.name);
    if (val) {
      return normalize(ctx, val);
    } else {
      return e;
    }

  } else if (e instanceof Pi) {
    return new Pi(normalizeAbstraction(ctx, e.abs));

  } else if (e instanceof Type) {
    return e;

  } else if (e instanceof Lambda) {
    return new Lambda(normalizeAbstraction(ctx, e.abs));

  } else if (e instanceof App) {
    const { e1, e2 } = e;
    const e1_ = normalize(ctx, e1);
    const e2_ = normalize(ctx, e2);

    if (e1_ instanceof Lambda) {
      const { variable: x, type: t, expr: e1__ } = e1_.abs;
      const ctx_ = List.of([[x, e2_]]);
      return normalize(ctx, subst(ctx_, e1__));
    } else {
      return new App(e1, e2);
    }
  }

}
