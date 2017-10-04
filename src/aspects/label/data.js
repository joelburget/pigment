// @flow

import { Record } from 'immutable';

import { register } from '../../theory/registry';


// formation

export const LabelShape = Record({
  name: null, // string
}, 'label');


// TODO - decide to drop this or actually build it
const signature = {
  formation: null,
  intros: null,
  elims: null,

  searchAliases: ['label', 'name'],
};

export default signature;


register('label', signature);
