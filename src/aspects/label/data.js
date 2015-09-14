// @flow

import { Record, OrderedMap } from 'immutable';


var labelShape = Record({
  name: null,
}, 'label');

register('label', Label);

export class Label extends labelShape {

  constructor(name: string): void {
    super({ name });
  }

  getType(): Tm {
    return Type.singleton;
  }

  evaluate(root: AbsRef, ctx: Context): EvaluationResult {
    return mkSuccess(this);
  }
}

