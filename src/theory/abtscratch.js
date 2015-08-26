// @flow
//
// The fundamental idea of an ABT is to separate binding into its own
// structure.

import { Record, Set } from 'immutable';


class Var extends Record({ name: null }) {
  rename(oldName: string, newName: string): Var {
    return this.name === oldName ? mkVar(newName) : this;
  }

  subst(value: Abt, name: string): Tm | Var {
    return this.name === name ? new Tm({ value }) : this;
  }
}

export function mkVar(name: string): Abt {
  return new Abt({
    freevars: Set([ name ]),
    children: [ new Var({ name }) ]
  });
}


// type Abs = {
//   names: Array<?string>;
//   value: Abt;
// };

// this is a multi-binder!
export class Abs extends Record({ names: null, value: null }) {
  instantiate(values: Array<Abt>): Abt {
    var result = this.value;
    this.names.forEach((name, i) => {
      if (name != null) {
        result = result.subst(values[i], name);
      }
    });
    return result;
  }

  rename(oldName: string, newName: string): Abs {
    // if we bind oldName at any point, then it's shadowed and we don't have to
    // rename our body.
    var shadowed = Set(this.names).includes(oldName);
    return shadowed ?
      this :
      new Abs({
        names: this.names,
        value: this.value.rename(oldName, newName),
      });
  }

  subst(t: Abt, x: string): Abs {
    // we really don't want to shadow any of these free variables
    var freevars: Set<string> = t.freevars.union(this.value.freevars);

    // come up with a fresh name for all of our bindings!
    // use newValue to track all these renamings!
    //
    // TODO - shouldn't this only be necessary in the case that x actually
    // occurs in this.value?
    var newValue = this.value;
    var names = this.names.map(name => {
      if (name == null) {
        return name;
      }

      // avoid a capture, substitute the new name if necessary.
      var name_ = fresh(name, freevars);
      if (name_ !== name) {
        newValue = newValue.rename(name, name_);
      }
      return name_;
    });

    return new Abs({ names, value: newValue.subst(t, x) });
  }
}


function fresh(name: string, taken: Set<string>): string {
  while (taken.contains(name)) {
    name += '_';
  }

  return name;
}

//

// type Tm = { value: Abt };

export class Tm extends Record({ value: null }) {
  renameTm(oldName: string, newName: string): Tm {
    return new Tm({ value: this.value.rename(oldName, newName) });
  }

  substTm(t: Abt, x: string): Tm {
    return new Tm({ value: this.value.subst(t, x) });
  }
}


type AbtChild = Var | Tm | Abs;


// type Abt {
//   freevars: Set<string>;
//   children: Array<AbtChild>;
// };

export class Abt extends Record({ freevars: null, children: null }) {
  rename(oldName: string, newName: string): Abt {
    return new Abt({
      freevars: this.freevars,
      children: this.children.map(child => child.rename(oldName, newName)),
    });
  }

  subst(t: Abt, x: string): Abt {
    return new Abt({
      freevars: this.freevars,
      children: this.children.map(child => child.subst(t, x))
    });
  }
}


export function mkTm(
  children: Array<Abt>,
  binders: Array<Array<?string>>): Abt {

  // for each thing in arity... build an Abs (if necessary)
  // or a tm / var
  var thisChildren = children.map((value, i) => {
    // which names are we being instructed to bind?
    var names = binders[i];

    // how many variables we need to bind
    var thisArity = names.length;

    // hm... maybe it's not even useful to distinguish between Abs and Tm.
    // would it be clearer to just use Abs as a generalization of Tm?
    if (thisArity > 0) {
      return new Abs({ names, value });
    } else {
      return new Tm({ value });
    }
  });

  function nodeFreevars(node: Abt | string): Set<string> {
    return node instanceof Abt ?
      node.freevars :
      Set.of(node);
  }

  var empty = Set();
  // XXX look at this.children or children?
  var internalFreevars = empty.union.apply(empty, children.map(nodeFreevars));
  var bound = empty.union.apply(
    empty,
    binders.map(arr => Set.of.apply(Set, arr))
  );

  var thisFreevars = internalFreevars.subtract(bound);

  return new Abt({ freevars: thisFreevars, children: thisChildren });
}
