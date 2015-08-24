// @flow

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


//


export class Abs extends Record({ names: null, value: null }) {
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

//


type AbtChild = Var | Abs;


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
