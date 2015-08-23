// @flow
//
// The fundamental idea of an ABT is to separate binding into its own
// structure.

import { Set } from 'immutable';


class Var {
  name: string;

  rename(oldName: string, newName: string): Var {
    return this.name === oldName ? new Var(newName) : this;
  }

  subst(t: Abt, x: string): Tm | Var {
    return this.name === x ? new Tm(t) : this;
  }
}


// this is a multi-binder!
export class Abs {
  names: Array<?string>;
  value: Abt;

  constructor(names: Array<?string>, value: Abt) {
    this.names = names;
    this.value = value;
  }

  instantiate(values: Array<Abt>): Tm {
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
      new Abs(this.names, this.value.rename(oldName, newName));
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

    return new Abs(names, newValue.subst(t, x));
  }
}


function fresh(name: string, taken: Set<string>): string {
  while (taken.contains(name)) {
    name += '_';
  }

  return name;
}


export class Tm {
  value: Abt;

  constructor(value: Abt) {
    this.value = value;
  }

  rename(oldName: string, newName: string): Tm {
    return new Tm(this.value.rename(oldName, newName));
  }

  subst(t: Abt, x: string): Tm {
    return new Tm(this.value.subst(t, x));
  }
}


type AbtChild = Var | Abs | Tm;


// ABTs extend asts with variables and abstractions
export class Abt {
  // we look at the arity to figure out how many variables to bind!
  // static arity: Array<number>;

  freevars: Set<string>;

  // all children really could be Abs's. Might make some things simpler.
  children: Array<AbtChild>;

  constructor(freevars: Set<string>, children: Array<AbtChild>) {
    this.freevars = freevars;
    this.children = children;
  }

  rename(oldName: string, newName: string): Abt {
    return new Abt(
      this.freevars,
      this.children.map(child => child.rename(oldName, newName))
    );
  }

  subst(t: Abt, x: string): Abt {
    return new Abt(
      this.freevars,
      this.children.map(child => child.subst(t, x))
    );
  }
}


// export function mkTm(
//   children: Array<Abt>,
//   binders: Array<Array<?string>>): Abt {

//   // for each thing in arity... build an Abs (if necessary)
//   // or a tm / var
//   var thisChildren = children.map((child, i) => {
//     // which names are we being instructed to bind?
//     var names = binders[i];

//     // how many variables we need to bind
//     var thisArity = names.length;

//     // hm... maybe it's not even useful to distinguish between Abs and Tm.
//     // would it be clearer to just use Abs as a generalization of Tm?
//     if (thisArity > 0) {
//       return new Abs(names, child);
//     } else {
//       return new Tm(child);
//     }
//   });

//   function nodeFreevars(node: Abt | string): Set<string> {
//     return node instanceof Abt ?
//       node.freevars :
//       Set.of(node);
//   }

//   var empty = Set();
//   // XXX look at this.children or children?
//   var internalFreevars = empty.union.apply(empty, children.map(nodeFreevars));
//   var bound = empty.union.apply(
//     empty,
//     binders.map(arr => Set.of.apply(Set, arr))
//   );

//   var thisFreevars = internalFreevars.subtract(bound);

//   return new Abt(thisFreevars, thisChildren);
// }


// export function mkVar(name: string): Abt {
//   return new Abt(
//     Set([ name ]),
//     [ new Var(name) ]
//   );
// }
