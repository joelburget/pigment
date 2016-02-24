// @flow
import { Record, Set } from 'immutable';
import React, { Component } from 'react';

import { INTRODUCTION } from '../messages';
import Firmament from './Firmament';

import type { Element } from 'react';


const TY = Symbol('TY');


const TyData = Record({});


class TyView extends Component<{}, {}, {}> {
  render(): Element {
    return <span>Ty</span>;
  }
}


export const Ty = {
  name: 'Ty',
  symbol: TY,
  type: INTRODUCTION,
  minLevel: 2,
  handlers: {
  },
  render: TyView,
  data: TyData,
  getNamesInScope(loc: Location): Set<string> {
    throw new Error("can't get names of Ty");
  },
};
