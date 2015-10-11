// @flow
import { Record } from 'immutable';

import { Type } from './tm';
import EvaluationResult from './evaluation';


const EqualityShape = Record({
  of: null, // Tm
  type: Type.singleton,
}, 'equality');


// Propositional Equality type
export class Equality extends EqualityShape {
  static arity = [0];

  map(): Equality {
    throw new Error('unimplemented - Equality.map');
  }

  step(): EvaluationResult {
    throw new Error('unimplemented - Equality.step');
  }
}


const ReflShape = Record({
  left: null, // Tm
  right: null, // Tm
  type: Type.singleton,
}, 'refl');


// TODO come up with appropriate name for this
export class Refl extends ReflShape {
  static arity = [0, 0];

  map(): Equality {
    throw new Error('unimplemented - Refl.map');
  }

  step(): EvaluationResult {
    throw new Error('unimplemented - Refl.step');
  }
}
