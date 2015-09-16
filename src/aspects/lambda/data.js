// @flow

import invariant from 'invariant';
import { Record, List } from 'immutable';

import { INTRO, Type } from '../../theory/tm';
import { mkRel } from '../../theory/ref';
import { register } from '../../theory/registry';

import type { Tm } from '../../theory/tm';
import type { RelRef, AbsRef, Ref } from '../../theory/ref';


var lamShape = Record({
  name: null,
  domain: null,
  body: null,
  codomain: null,
}, 'lam');

export default class Lam extends lamShape {

  constructor(name: string, domain: Tm, body: Tm, codomain: Tm): void {
    super({ name, domain, body, codomain });
  }

  // apply just one argument
  evaluate(root: AbsRef, args: [Tm]): Tm {
    var [ arg ] = args;
    var { body, name } = this;

    // if the name is null it's not really doing anything
    if (name != null) {
      body = body.subst(root, mkRel('..', 'binder'), arg);
    }
    // if the name is null it's not really doing anything

    return body.evaluate(root, mkRel('body'), ctx);
  }

  subst(root: AbsRef, ref: Ref, tm: Tm): Tm {
    return this.update(
      'body',
      body => body.subst(
        root.extend(mkRel('body')),
        ref.goIn(),
        tm
      )
    );
  }

  getType(): Tm {
    return new Arr(this.domain, this.codomain);
  }

  slots(): List<Tm> {
    // TODO lambda doesn't have codomain yet.
    return List([ this.domain, this.codomain ]);
  }

  static fillHole(type: Tm): Lambda {
    // invariant(type instanceof
    throw new Error('unimplemented - Lambda.fillHole');
    return new Lambda(
      name,
      domain,
      body,
      codomain
    );
  }

  static form = INTRO;

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
