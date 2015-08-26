

export class Type {
  static name: string;

  // $flowstatic
  static singleton: Type = new Type();

  // $flowstatic
  type: ?Tm = null;

  evaluate(): EvaluationResult<Tm> {
    return mkSuccess(this);
  }

  subst(ref: Ref, value: Tm): Tm {
    return this;
  }
}

Type.name = 'type';

