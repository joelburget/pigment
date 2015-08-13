


export function normalizeAbstraction(ctx: Context,
                                     abs: Abstraction): Abstraction {
  let { variable, type, expr } = abs;
  type = normalize(ctx, type);

  return new Abstraction(
    variable,
    type,
    normalize(extend(variable, type, null, ctx), expr)
  );
}


export function equal(ctx: Context, e1_: Expression, e2_: Expression) {
  const e1 = normalize(ctx, e1_);
  const e2 = normalize(ctx, e2_);

  if (e1 instanceof Var && e2 instanceof Var) {
    return Immutable.is(e1.name, e2.name);

  } else if (e1 instanceof Pi && e2 instanceof Pi) {
    return equalAbstraction(ctx, e1.abs, e2.abs);

  } else if (e1 instanceof Type && e2 instanceof Type) {
    return true;

  } else if (e1 instanceof Lambda && e2 instanceof Lambda) {
    return equalAbstraction(ctx, e1.abs, e2.abs);

  } else if (e1 instanceof App && e2 instanceof App) {
    const { e1: e11, e2: e12 } = e1;
    const { e1: e21, e2: e22 } = e2;

    return equal(ctx, e11, e21) && equal(ctx, e12, e22);

  } else {
    return false;
  }
}

export function equalAbstraction(ctx: Context,
                                 abs1: Abstraction,
                                 abs2: Abstraction): boolean {
  const { variable: x, type: t1, expr: e1 } = abs1;
  const { variable: y, type: t2, expr: e2 } = abs2;

  // Make both bound variables the same in the comparison of abstractions
  const ctx_ = List.of([[y, x]]);

  return equal(ctx, t1, t2) &&
         equal(ctx, e1, subst(ctx_, e2));
}
