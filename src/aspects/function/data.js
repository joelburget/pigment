// @flow
/* eslint id-length: 0 */

import { Record, List } from 'immutable';
import invariant from 'invariant';

// import { Type, Hole } from '../../theory/tm';
import { register } from '../../theory/registry';

// import type { EvaluationResult } from '../../theory/evaluation';
import type { Tm } from '../../theory/tm';
// import type Edit, { Action } from '../../theory/edit';


// introduction

const Arrow = Record({
  binder: null, // { string: Tm }
  body: null, // Tm
  // TODO - would be neat to build in these views
  // domain: null,
  // codomain: null,
}, 'arrow');


const mkArrow = (binder, body) => new Tm(
  // XXX this is not the constructor form
  ['Arrow', 'formation'], new Arrow({ binder, body })
);


const arrowConstructor = {
  actions: List([]),
  performEdit: () => {
    invariant(
      false,
      "Arrow doesn't know any edits"
    );
  },
};


// const arrowIntro = (() => {
//   const x = { x: new Hole('S', Type) };

//   return mkArrow(x, new Scope(x, new Hole('T', Type)));
// })();


const Func = Record({
  binder: null, // { [name]: Tm }
  body: null, // Tm
}, 'function');


const mkFunction = (binder, body) => new Tm(
  ['Arrow', 'intros', 'Function'], new Func({ binder, body })
);


function binderName(binder) {
  invariant(
    Object.keys(binder).length === 1,
    'binder must have exactly one key'
  );

  return Object.keys(binder)[0];
}


function binderTm(binder) {
  return binder[binderName(binder)];
}


// const S = new Hole('S', Type);
// const T = new Hole('T', Type);
// const t = new Hole('t', T);

const functionConstructor = {
  rule({ binder, body }) {

    // need to introduce some variables:

    // type of the subject
    const S = new UnificationVar('S', Type);

    // type of the result
    const T = new UnificationVar('T', Type);

    // result term
    const t = new UnificationVar('t', Type);

    binder
  },

  generateConstraints({ binder, body }) {
    OfType(binder,
  },

  // term: mkFunction({ x: S }, t),
  // type: mkArrow({ x: S }, T),
  // step: (root: FreeVar, ctx: Context) => {
  //   const { name } = this;
  //   let { body } = this;

  //   // if the name is null it's not really doing anything
  //   if (name != null) {
  //     const arg = ctx.get(name);
  //     body = body.subst(root, mkBound('..', 'binder'), arg);
  //   }
  //   // if the name is null it's not really doing anything

  //   return body.step(root, ctx.bind(mkBound('body')));
  // },
  // subst: (root: FreeVar, ref: Ref, tm: Tm) => {
  //   return this.update(
  //     'body',
  //     body => body.subst(
  //       root.extend(mkBound('body')),
  //       ref.goIn(),
  //       tm
  //     )
  //   );
  // },
  actions: List([]),
  performEdit: () => {
    invariant(
      false,
      "Function doesn't know any edits"
    );
  },
};


// elimination

const Application = Record({
  fun: null,
  arg: null,
}, 'application');


const mkApplication = (fun, arg) => new Tm(
  ['Arrow', 'elims', 'Application'], new Application({ fun, arg })
);


// const S = new Hole('S', Type);
// const T = new Hole('T', Type);
// const s = new Hole('s', S);

const application = {
  // term: mkApplication(
  //   new Hole(
  //     'f',
  //     new mkArrow({ x: S }, T)
  //   ),
  //   s
  // ),
  // // substitute x for s in T
  // type: T.subst('x', s),

  getPieces: function* getPieces() {
    // yield* [S, T, s];
  },

  step() {
    // TODO
  }
};


const feature = {
  constructors: Set([functionConstructor, arrowConstructor]),
  eliminators: Set([application]),

  canTyRules: Set(),
  elimTyRules: Set(),

  searchAliases: ['arrow', 'function', 'lambda'],
};

export default feature;

register('arrow', feature);
