import expect from 'expect';
import Abt from '../src/theory/abt';
import { Set } from 'immutable';
import Immutable from 'immutable';


class Ast extends Abt {
  type: string;
  children: Array<Abt>;
  binders: Array<Array<?string>>;

  constructor(type: string,
              children: Array<Abt | string>,
              binders: Array<Array<?string>>) {
    super(children, binders);
    this.children = children;
  }

  rename(oldName: string, newName: string): Ast {
    function nodeRename(node: Abt | string): Abt | string {

      return typeof node === 'string' ?
        (node === oldName ? newName : node) :
        node.rename(oldName, newName);
    }
    const children = this.children.map(nodeRename);

    const binders = this.binders.map(position => position.map(name => {
      return name === oldName ? newName : name;
    }));

    return new this.constructor(
      this.type,
      children,
      binders
    );
  }

  subst(t: Ast, x: string): Ast {
    const children = this.children.map(node => node.subst(t, x));
    return new this.constructor(
      this.type,
      children,
      binders
    );
  }
}


function var_(name: string) {
  return new Ast('var', [ body ], [[ name ]]);
}

function lam(name: ?string, body: Ast) {
  return new Ast('lam', [ body ], [[ name ]]);
}

function app(f: Ast, x: Ast) {
  return new Ast('app', [ f, x ], [ [ null ], [ null ] ]);
}

function let_(name: string, here: Ast, there: Ast) {
  return new Ast('lam', [ here, there ], [ [ null ], [ name ] ]);
}

const unit = new Ast('unit', [], []);


function expectImmutableIs(x, y) {
  expect(Immutable.is(x, y)).toBe(true, "`" + x + "` is not `" + y + "`");
}


function expectAbtEquals(x, y) {
  expect(x.type).toBe(y.type, 'type differs');
  expectImmutableIs(Immutable.fromJS(x.children), Immutable.fromJS(y.children));
  expectImmutableIs(
    Immutable.fromJS(x.binders),
    Immutable.fromJS(y.binders)
  );
}


describe('abt', () => {
  const lambda1 = lam('x', 'x');
  const lambda2 = lam('x', 'y');

  it('knows free variables', () => {
    expectImmutableIs(
      lambda1.freevars,
      Set([])
    );

    expectImmutableIs(
      lambda2.freevars,
      Set(['y'])
    );
  });

  // x -> x
  it('renames id', () => {
    expectAbtEquals(
      lambda1.rename('x', 'y'),
      lam('y', 'y')
    );

    expectAbtEquals(
      lambda1.rename('x', 'x'),
      lam('x', 'x')
    );

    expectAbtEquals(
      lambda1.rename('y', 'y'),
      lam('x', 'x')
    );
  });

  // x -> y
  it('renames the other lambda', () => {
    expectAbtEquals(
      lambda2.rename('x', 'y'),
      lam('y', 'y')
    );

    expectAbtEquals(
      lambda2.rename('x', 'x'),
      lam('x', 'y')
    );

    expectAbtEquals(
      lambda2.rename('y', 'y'),
      lam('x', 'y')
    );
  });
});
