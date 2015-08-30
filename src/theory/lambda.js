// @flow

import { List } from 'immutable';

import { TmRecord, Type } from './tm';
import type { Tm } from './tm';
import { mkStuck, mkSuccess, bind } from './evaluation';
import type { EvaluationResult } from './evaluation';
import { lookup, add } from './context';
import type { Context } from './context';
import type { RelRef, AbsRef, Ref } from './ref';
import { mkRel } from './ref';
import { register } from './registry';


export var Binder = TmRecord({ name: null, type: null }, 'binder');


var lamShape = TmRecord({
  binder: null,
  body: null,
}, 'lam');

export class Lam extends lamShape {

  constructor(binder: Binder, body: Tm): void {
    super({ binder, body });
  }

  getType(): Tm {
    return new Arr(this.binder.type, this.body.getType());
  }

  // apply just one argument
  evaluate(root: AbsRef, ctx: Context, arg: Tm): Tm {
    var { body, binder } = this;
    var binderName: ?string = binder.name;

    // if the name is null it's not really doing anything
    if (binderName != null) {
      body = body.subst(root, mkRel('..', 'binder'), arg);
    }
    // if the name is null it's not really doing anything

    return body.evaluate(root, mkRel('body'), ctx);
  }

  subst(root: AbsRef, ref: Ref, tm: Tm): Tm {
    return this.updateIn(
      ['body'],
      body => body.subst(
        root.extend(mkRel('body')),
        ref.goIn(),
        tm
      )
    );
  }

  // instantiate(values: List<?Tm>): Tm {
  //   var body: Tm = this.body;
  //   var binders: List<?string> = this.binders;

  //   var resultBinders: List<?string> = List().withMutations(resultBinders => {
  //     for (var i = 0; i < binders.length; i++) {
  //       var binder = binders.get(i);
  //       var value = values.get(i);

  //       // applying a value that's not used
  //       if (binder == null && value != null) {
  //         continue;

  //       // binder missing a value
  //       } else if (value == null) {
  //         resultBinders.push(binder);

  //       // binder != null && value != null
  //       } else if (binder != null) {
  //         var ref: Ref = this.mkRef(binder);
  //         // XXX withMutations
  //         body = body.subst(ref, value);
  //       }
  //     }
  //   });

  //   if (resultBinders.size === 0) {
  //     return new Lam(resultBinders, body);
  //   } else {
  //     return body;
  //   }
  // }
}

register('lam', Lam);


var arrShape = TmRecord({
  domain: null,
  codomain: null,
}, 'arr');

export class Arr extends arrShape {

  constructor(domain: Tm, codomain: Tm): void {
    super({ domain, codomain });
  }

  getType(): Tm {
    return Type.singleton;
  }

  evaluate(root: AbsRef, ctx: Context): EvaluationResult {
    throw new Error("TODO - Arr.evaluate");
  }
}

register('arr', Arr);


var appShape = TmRecord({
  func: null,
  arg: null,
}, 'app');

export class App extends appShape {

  constructor(func: Tm, arg: Tm): void {
    var fType = func.getType();

    if (fType instanceof Arr) {
      var type = fType.codomain;
      super({ func, arg });
    } else {
      throw new Error('runtime error in App constructor');
    }
  }

  getType(): Tm {
    return this.func.getType().codomain;
  }

  evaluate(root: AbsRef, ctx: Context): EvaluationResult {
    return bind(
      this.arg.evaluate(root.extend(mkRel('arg')), ctx),
      // arg => this.func.evaluate(root.extend(mkRel('func')), ctx, arg)
      arg => this.func.evaluate(root.extend(mkRel('func')), ctx, arg)
    );
  }
}

register('app', App);
