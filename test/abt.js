import expect from 'expect';
import { mkVar, mkTm, Abt } from '../src/theory/abt';
import { Set } from 'immutable';
import Immutable from 'immutable';


class Ast extends Abt {
  type: string;
  binders: Array<Array<?string>>;

  constructor(type: string,
              children: Array<Abt | string>,
              binders: Array<Array<?string>>) {
    super(Set(), []);

    var abt = mkTm(children, binders);

    this.freevars = abt.freevars;
    this.children = abt.children;
    this.binders = binders;
  }
}


function lam(name: ?string, body: Ast) {
  return mkTm(
    [ body   ],
    [ [name] ]
  );
}

function app(f: Ast, x: Ast) {
  return mkTm(
    [ f,  x  ],
    [ [], [] ]
  );
}

function let_(name: string, here: Ast, there: Ast) {
  return mkTm(
    [ here, there  ],
    [ [],   [name] ]
  );
}

const unit = mkTm(
  [],
  []
);


function expectImmutableIs(x, y) {
  expect(Immutable.is(x, y)).toBe(true, "`" + x + "` is not `" + y + "`");
}


function expectAbtEquals(x, y) {
  expect(x.type).toBe(y.type, 'type differs');
  expectImmutableIs(
    x.freevars,
    y.freevars
  );
  // TODO -- make this more precise
  // expectImmutableIs(
  //   Immutable.fromJS(x.children),
  //   Immutable.fromJS(y.children)
  // );
}


describe('abt', () => {
  const lambda1 = lam('x', mkVar('x'));
  const lambda2 = lam('x', mkVar('y'));

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
    console.log(lambda1.rename('x', 'y'));
    console.log(lam('y', mkVar('y')));
    expectImmutableIs(
      lambda1.rename('x', 'y'),
      lam('y', mkVar('y'))
    );

    expectImmutableIs(
      lambda1.rename('x', 'x'),
      lam('x', mkVar('x'))
    );

    expectImmutableIs(
      lambda1.rename('y', 'y'),
      lam('x', mkVar('x'))
    );
  });

  // x -> y
  it('renames the other lambda', () => {
    expectImmutableIs(
      lambda2.rename('x', 'y'),
      // this is rather implementation-dependent, eh
      lam('y_', mkVar('y'))
    );

    expectImmutableIs(
      lambda2.rename('x', 'x'),
      lam('x', mkVar('y'))
    );

    expectImmutableIs(
      lambda2.rename('y', 'y'),
      lam('x', mkVar('y'))
    );
  });

  it('instantiates', () => {
    expectAbtEquals
  });
});
