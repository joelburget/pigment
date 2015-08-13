// @flow
//
// The fundamental idea of an ABT is to separate binding into its own
// structure. Instead of a traditional AST holding both binding and content
// nodes, we have two corecursive structures:
//
// * AST (describes the structure, ignores binding)
// * ABT (handles only binding)
//   - Var
//   - Abs
//   - Tm (embedded AST node)
//
// You need to provide

import { Set } from 'immutable';


type Ast = {
  rename: Function,
  map: Function
}


// ABTs extend asts with variables and abstractions
class AbtBase<A: Ast> {
  freevars: Set<string>;
}


export class Var<A: Ast> extends AbtBase<A> {
  name: string;

  constructor(name: string): void {
    super(arguments);
    this.freevars = Set([name]);
    this.name = name;
  }

  rename(oldName: string, newName: string): Var<A> {
    return oldName === this.name ? new Var(newName) : this;
  }

  subst(t: A, x: string): Var<A> {
    return x === this.name ? t : this;
  }
}


export class Abs<A: Ast> extends AbtBase<A> {
  name: string;
  body: AbtBase<A>;

  constructor(name: string, body: AbtBase<A>): void {
    super(arguments);
    this.freevars = body.freevars.remove(name);
    this.name = name;
    this.body = body;
  }

  rename(oldName: string, newName: string): Abs<A> {
    return oldName === this.name ?
      new Abs(newName,   this.body) :
      new Abs(this.name, this.body.rename(oldName, newName));
  }

  // substitute `t` for `x` in `this.body`
  subst(t: A, x: string): Abs<A> {
    var freevars: Set<string> = t.freevars.union(this.body.freevars);
    var x_: string = fresh(freevars, this.name);
    var e /*: AbtBase<A>*/ = this.body.rename(this.name, x_).subst(t, x);

    return new Abs(x_, e);
  }
}


export class Tm<A: Ast> extends AbtBase<A> {
  value: A;

  constructor(value: A): void {
    super(arguments);
    this.freevars = Set(value.children.map(node => node.freevars)).flatten();
    this.value = value;
  }

  rename(oldName: string, newName: string): Tm<A> {
    return this.value.map(v => v.rename(oldName, newName));
  }

  subst(t: A, x: string): Tm<A> {
    return this.value.map(v => v.subst(t, x));
  }
}


function fresh(vs: Set<string>, v: string): string {
  return vs.includes(v) ? fresh(vs, v + "'") : v;
}
