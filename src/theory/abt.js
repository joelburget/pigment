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
import { Expression as Ast } from './tm';


// TODO why did I have to use Expression instead of this subtype?
//
// // TODO would be cool to build in alpha-equivalence
// export type Ast = {
//   // rename(oldName: string, newName: string): Ast,
//   // subst(t: Ast, x: string): Ast,
//   map<A>(f: (x: AbtBase) => A): A
// };


// ABTs extend asts with variables and abstractions
export class AbtBase {
  freevars: Set<string>;
  rename: (oldName: string, newName: string) => AbtBase;
  subst: (t: AbtBase, x: string) => AbtBase;
}


function fresh(vs: Set<string>, v: string): string {
  return vs.includes(v) ? fresh(vs, v + "'") : v;
}


function map<A>(x: Ast, f: (x: Abt) => A): Array<A> {
  return x.children.map(f);
}


export class Var<A: Ast> extends AbtBase {
  name: string;

  constructor(name: string): void {
    super();
    this.freevars = Set([name]);
    this.name = name;
  }

  rename(oldName: string, newName: string): Var<A> {
    return oldName === this.name ? new Var(newName) : this;
  }

  subst(t: AbtBase, x: string): AbtBase {
    return x === this.name ? t : this;
  }
}


export class Abs<A: Ast> extends AbtBase {
  name: string;
  body: Ast;

  constructor(name: string, body: AbtBase): void {
    super();
    this.freevars = body.freevars.delete(name);
    this.name = name;
    this.body = body;
  }

  rename(oldName: string, newName: string): Abs<A> {
    var body = this.body;

    var f: ((node: Ast) => Ast) = node => node.rename(oldName, newName);

    return oldName === this.name ?
      new Abs(newName,   body) :
      new Abs(this.name, body.map(f));
  }

  // substitute `t` for `x` in `this.body`
  subst(t: AbtBase, x: string): Abs<A> {

    var freevars: Set<string> = t.freevars.union(this.freevars);
    var x_: string = fresh(freevars, this.name);
    var f: ((node: Ast) => Ast) = node =>
      node.rename(this.name, x_).subst(t, x);
    var e: Ast = this.body.map(f);

    return new Abs(x_, e);
  }
}


export class Tm<A: Ast> extends AbtBase {
  value: Ast;

  constructor(values: Array<Abt>): void {
    super();
    this.freevars = Set.of(values.map(node => node.freevars)).flatten();
    this.value = value;
  }

  rename(oldName: string, newName: string): Tm<A> {
    var f: ((node: Ast) => Ast) = node => node.rename(oldName, newName);
    return new Tm(this.value.map(node => node.rename(oldName, newName)));
  }

  subst(t: Ast, x: string): Tm<A> {
    var f: ((node: AbtBase) => AbtBase) = node => node.subst(t, x);
    return new Tm(this.value.map(f));
  }
}
