import expect from 'expect';
import { List } from 'immutable';

import { Module, Note, Definition, Property, Example } from '../module';

import expectImmutableIs from '../../../test/expectImmutableIs';
import { id } from '../../../test/examples';


const testModule = new Module({
  name: 'test module',
  contents: List([
    new Note({
      name: 'note',
      defn: 'just a note!',
    }),
    new Definition({
      name: 'f',
      defn: id,
    }),
  ]),
});

describe('modules', () => {
  it('is named', () => {
    expect(testModule.name).toBe('test module');
  });

  it('accesses members', () => {
    expect(testModule.contents.get(1).name).toBe('f');
    expectImmutableIs(
      testModule.contents.get(1).defn,
      id
    );
  });
});
