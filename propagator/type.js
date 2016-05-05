// @flow

import R from 'ramda';

import Propagator from './propagator';
import Scheduler from './scheduler';
import Cell from './cell';

type BaseType = {
  tag: 'BASE_TYPE';
  name: string;
};

type ArrowType = {
  tag: 'ARROW_TYPE';
  args: { [key: string]: Type };
  result: Type;
};

export function baseType(name: string): BaseType {
  return {
    tag: 'BASE_TYPE',
    name,
  };
}

export function arrowType(
  args: {[key: string]: ?Type},
  result: ?Type
): ArrowType {
  return {
    tag: 'ARROW_TYPE',
    args,
    result,
  };
}

type Type = BaseType | ArrowType;

function merge(x: Type, y: Type): Change<Type> {
  const contra = {
    tag: 'CONTRADICTION',
    message: 'Type merge contradiction: ' + JSON.stringify(x) + ' /= ' + JSON.stringify(y),
  };

  // TODO maybe we want to replace this with immutable data structures?
  if (R.equals(x, y)) {
    return {
      tag: 'FORWARD_CHANGE',
      gain: false,
      content: x,
    };
  } else if (x.tag === 'BASE_TYPE' && y.tag === 'BASE_TYPE') {
    // both base types but with different names
    return contra;
  } else if (x.tag === 'ARROW_TYPE' && y.tag === 'ARROW_TYPE') {
    // here's the interesting case -- try to merge functions

    // first merge result
    const result_ = merge(x.result, y.result);
    if (result_.tag === 'CONTRADICTION') {
      return result_;
    }
    const result = result_.content;

    // then merge args: check that y brings a subset of x's keys
    if (R.difference(R.keys(y.args), R.keys(x.args)).length > 0) {
      return contra;
    }

    // all must merge cleanly
    let breakEarly = null;
    const args = R.mergeWith((x, y) => {
      const merged = merge(x, y);
      if (merged.tag === 'CONTRADICTION') {
        breakEarly = merged;
      } else {
        return merged.content;
      }
    }, x.args, y.args);

    if (breakEarly) {
      return breakEarly;
    }

    // TODO this almost works, but fails in the success case, since we end up
    // with tagged forward progress in our result
    // if (R.any(arg => arg.tag === 'CONTRADICTION', args)) {
    //   return contra;
    // }

    return {
      tag: 'FORWARD_CHANGE',
      gain: true,
      content: {
        tag: 'ARROW_TYPE',
        args,
        result,
      },
    };
  } else {
    return contra;
  }
}

// TODO generalize this to a lens into a structure?
// TODO for now we assume content is not null. this does not match the types
function bindPart(
  scheduler: Scheduler,
  f: Cell<ArrowType>,
  name: string,
  arg: Cell<Type>
) {
  // forward: knowledge of the function's type propagates to arg
  new Propagator(
    scheduler,
    [f],
    () => {
      const val = f.content.args[name];
      if (val != null) {
        arg.addContent(val);
      }
    }
  );

  // backward: arg propagates to the function's type
  // just dispatch to the merger, yay!
  new Propagator(
    scheduler,
    [arg],
    () => f.addContent(
      {
        tag: 'ARROW_TYPE',
        args: { [name]: arg.content },
        result: null,
      }
    )
  );
}

// application(scheduler, f, {x, y, z}, w);
export function application(
  scheduler: Scheduler,
  f: Cell<ArrowType>,
  args: { [key: string]: Cell<Type> },
  result: Cell<Type> // XXX need to also bind result
) {
  // for each slot, create a binding (two propagators) between the function's
  // param and the argument
  for (const name of Object.keys(args)) {
    const arg = args[name];
    bindPart(scheduler, f, name, arg);
  }
}

export default {
  merge,
};
