// @flow
import { Record } from 'immutable';
import React, { Component } from 'react';

import { INTRODUCTION } from '../messages';

import type { Element } from 'react';


const TY = Symbol();


const TyData = Record();


class TyView extends Component {
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
};
