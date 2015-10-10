// @flow

import invariant from 'invariant';
import { Record, List } from 'immutable';

import { INTRO, Type, Hole } from '../../theory/tm';
import { mkRel } from '../../theory/ref';
import { register } from '../../theory/registry';

import type { Tm } from '../../theory/tm';
import type { RelRef, AbsRef, Ref } from '../../theory/ref';


const ArrowShape = Record({
  domain: null,
  codomain: null,
  type: null,
});


export class Arrow extends ArrowShape {
  // TODO(joel) -- explore this concept that you might want to autocomplete
  // using any of a bunch of names.
  static searchAliases = ['arrow', 'function', 'lambda'];

  static form = INTRO;
  static typeClass = Type;

  static fillHole(type: Tm): Lambda {
    invariant(
      type instanceof Type,
      'Lambda can only fill holes of type Type'
    );

    // for now, just start with * -> *
    return new Arrow({
      domain: new Hole(null, type),
      codomain: new Hole(null, type),
      type,
    });
  }

  actions(): List<Action> {
    return List([]);
  }

  performEdit(id: string): Edit {
  }
}


register('arrow', Arrow);


const LamShape = Record({
  name: null, // string
  body: null, // Tm
  type: null, // Arrow
}, 'lam');

export default class Lam extends LamShape {

  // apply just one argument
  evaluate(root: AbsRef, args: [Tm]): Tm {
    const [ arg ] = args;
    let { body, name } = this;

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

  static fillHole(type: Tm): Lam {
    invariant(
      type instanceof Arrow,
      'Lam can only fill holes of type Arrow'
    );

    return new Lam({
      name: 'x',
      body: new Hole(null, type.codomain),
      type,
    });
  }

  static form = INTRO;
  static typeClass = Arrow;

  actions(): List<Action> {
    return List([]);
  }

  performEdit(id: string): Edit {
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
