

export class Tm<A: Ast> extends AbtBase {
  value: A;

  constructor(value: A): void {
    super();
    this.freevars = Set.of(value.map(node => node.freevars)).flatten();
    this.value = value;
  }

  rename(oldName: string, newName: string): Tm<A> {
    return new Tm(this.value.rename(oldName, newName));
  }

  subst(t: A, x: string): Tm<A> {
    return new Tm(this.value.subst(t, x));
  }
}
