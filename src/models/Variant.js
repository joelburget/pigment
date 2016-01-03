// @flow
import { Record, List } from 'immutable';
import React, { Component, PropTypes } from 'react';

import Firmament from './Firmament';

import type { Element } from 'react';

import type { RemoveVariantSignal, AddVariantSignal } from '../messages';

import { INTRODUCTION } from '../messages';

import Rows from '../components/Rows';


const VARIANT = Symbol('VARIANT');
const VARIANT_TY = Symbol('VARIANT_TY');

const VariantData = Record({
  tag: null,
});

const VariantTyData = Record({
  tags: List(),
});

const variantTyHandlers = {
  // SET_TAG(global: Firmament, signal) {
  //   const { path, tag } = signal;
  //   const loc = global.getLocation(path);

  //   const loc_ = loc.set('data', tag);
  //   return global.set(path, loc_);
  // },

  ADD_VARIANT(
    global: Firmament,
    signal: AddVariantSignal
  ): Firmament {
    const { path, tag, type } = signal;
    const pointer = global.followPath(path);
    const loc = global.getLocation(pointer);

    const newLoc = loc
      .updateIn(['data', 'tags'], tags => tags.push(tag))
      .setIn(['locations', tag], type);

    return global.update(pointer, newLoc);
  },

  REMOVE_VARIANT(
    global: Firmament,
    signal: RemoveVariantSignal
  ): Firmament {
    const { path, tag } = signal;
    const pointer = global.followPath(path);
    const loc = global.getLocation(pointer);

    const newLoc = loc
      .updateIn(['data', 'tags'], tags => tags.filter(tag_ => tag_ !== tag))
      .deleteIn(['locations', tag]);

    return global.update(pointer, newLoc);
  },
};

export class VariantView extends Component {

  static propTypes = {
    path: PropTypes.array.isRequired,
  };

  static contextTypes = {
    signal: PropTypes.func.isRequired,
    global: PropTypes.instanceOf(Firmament).isRequired,
  };

  render(): Element {
    const { global } = this.context;
    const { path } = this.props;
    const loc = global.getLocation(path);

    return (
      <div>
        VariantView: {loc.data.tag}
      </div>
    );
  }
}


export class VariantTyView extends Component {

  static propTypes = {
    path: PropTypes.array.isRequired,
  };

  static contextTypes = {
    signal: PropTypes.func.isRequired,
    global: PropTypes.instanceOf(Firmament).isRequired,
  };

  render(): Element {
    const { global } = this.context;
    const { path } = this.props;
    const loc = global.getLocation(path);

    // XXX figure out how to use this handler (different from other row
    // handlers).
    // const clickHandler = () => {
    //   this.context.signal(path, { action: REMOVE_VARIANT, name: key, path });
    // };

    return (
      <div>
        VariantTyView:
          <Rows fields={loc.type.fields} path={path} />
      </div>
    );
  }
}

export const Variant = {
  name: 'Variant',
  symbol: VARIANT,
  type: INTRODUCTION,
  minLevel: 0,
  handlers: {},
  render: VariantView,
  data: VariantData,
};

export const VariantTy = {
  name: 'VariantTy',
  symbol: VARIANT_TY,
  type: INTRODUCTION,
  minLevel: 1,
  handlers: variantTyHandlers,
  render: VariantTyView,
  data: VariantTyData,
};
