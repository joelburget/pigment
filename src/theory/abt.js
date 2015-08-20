// @flow
//
// The fundamental idea of an ABT is to separate binding into its own
// structure.

import { Set } from 'immutable';


type Info =
  { type: 'var', name: string } |
  { type: 'abs', name: ?string, value: Abt } |
  { type: 'tm',


// ABTs extend asts with variables and abstractions
export default class Abt {
  // we look at the arity to figure out how many variables to bind!
  static arity: Array<number>;
  static updateBinders(
    tm: Abt,
    children: Array<Abt>,
    binders: Array<Array<?string>>
  ): Abt;

  freevars: Set<string>;

  children: Array<Abt>;
  binders: Array<Array<?string>>;

  function rename(oldName: string, newName: string): Abt {
    var children = this.children.map(child => child.rename(oldName, newName));
    var binders = this.binders.map(names => names.map(name => {
      return name === oldName ? newName : name;
    }));

    return updateBinders(this, children, binders);
  }

  function subst(t: Abt, x: string): Abt {
    var children =
  }

  constructor(children: Array<Abt>, binders: Array<Array<?string>>): void {
    function nodeFreevars(node: Abt | string): Set<string> {
      return node instanceof Abt ?
        node.freevars :
        Set.of(node);
    }

    var empty = Set();
    var internalFreevars = empty.union.apply(empty, children.map(nodeFreevars));
    var bound = empty.union.apply(
      empty,
      binders.map(arr => Set.of.apply(Set, arr))
    );

    this.freevars = internalFreevars.subtract(bound);
    this.children = children;
    this.binders = binders;
  }
}
