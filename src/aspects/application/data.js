// @flow

import { Record, List } from 'immutable';

import { register } from '../../theory/registry';
import { bind } from '../../theory/evaluation';


var appShape = Record({
  func: null,
  arg: null,
  type: null,
}, 'app');

export default class App extends appShape {

  constructor(func: Tm, arg: Tm, type: Tm): void {
    var fType = func.getType();

    if (fType instanceof Arr) {
      var type = fType.codomain;
      super({ func, arg, type });
    } else {
      throw new Error('runtime error in App constructor');
    }
  }

  evaluate(root: AbsRef, ctx: Context): EvaluationResult {
    return bind(
      this.arg.evaluate(root.extend(mkRel('arg')), ctx),
      arg => this.func.evaluate(root.extend(mkRel('func')), ctx, arg)
    );
  }

  // hm... this hardly seems to make sense for app...
  subst(root: AbsRef, ref: Ref, value: Tm): Tm {
    throw new Error('unimplemented - App.subst');
  }

  getType(): Tm {
    return this.type;
  }

  slots(): Iterable<K, V> {
    return List([ this.type ]);
  }
}

register('app', App);
