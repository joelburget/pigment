// @flow
import { Map } from 'immutable';
import React, { Component, PropTypes } from 'react';

// cycle :(
// import Firmament from './Firmament';
import { UpLevel } from './Firmament';
import { Location } from './Location';
import {
  FILL_HOLE,
  INTRODUCTION,
  POKE_HOLE,
} from '../messages';
import { Module, ModuleTy } from './Module';
import { Record, RecordTy } from './Record';
import { Variant, VariantTy } from './Variant';
import { Ty } from './Ty';

import type { Element, SyntheticEvent } from 'react';

import type Firmament, { Path, WithGlobal } from './Firmament';
import type { Introduction, FillHoleSignal, PokeHoleSignal } from '../messages';


const HOLE = Symbol('HOLE');

const allIntroductions: Array<Introduction> = [
  Module,
  ModuleTy,
  Record,
  RecordTy,
  Variant,
  VariantTy,
  Ty,
];

class HoleView extends Component<{}, { path: Path }, {}> {

  static propTypes = {
    path: PropTypes.shape({
      root: PropTypes.symbol,
      steps: PropTypes.array,
    }).isRequired,
  };

  static contextTypes = {
    signal: PropTypes.func.isRequired,
    // cycle :(
    // global: PropTypes.instanceOf(Firmament).isRequired,
    global: PropTypes.object.isRequired,
  };

  handleSelectChange(event: SyntheticEvent) {
    const selectedType = event.target.value;
    const { path } = this.props;
    const { global, signal } = this.context;

    const path_ = {
      root: path.root,
      steps: path.steps.slice(0, -1),
    };
    const referer = global.followPath(path_);
    const name = path.steps[path.steps.length-1];

    if (selectedType !== '') {
      signal(
        path,
        { action: FILL_HOLE, selectedType, referer, name }
      );
    }
  }

  // TODO - enumerate a list of things this says it can accept
  render(): Element {
    const { path } = this.props;
    const level = path.steps.filter(step => step === UpLevel).length;

    const options = allIntroductions
      .filter(intro => intro.minLevel <= level)
      .map(({ name }) => <option key={name} value={name}>{name}</option>);

    return (
      <div>
        <div>
          level: {level}
          type: <select value='default'
                        onChange={val => this.handleSelectChange(val)}>
                  {options}
                </select>
        </div>
      </div>
    );
  }
}


const holeHandlers = {
  POKE_HOLE(global: Firmament, signal: PokeHoleSignal): Firmament {
    return global;
  },
  FILL_HOLE(
    global: Firmament,
    { referer, name, selectedType }: FillHoleSignal
  ): Firmament {
    // TODO this is really weird: I think we should have referer / name
    const tag: Introduction = allIntroductions.find(intro => intro.name === selectedType);

    if (tag === Record) {

      const { it, global: global_ } = global.newLocation({
        tag: RecordTy,
        locations: new Map([[ UpLevel, global.tyPointer ]]),
        data: new RecordTy.data(),
      });

      const { it: it_, global: global__ } = global_.newLocation({
        tag: Record,
        locations: new Map([[ UpLevel, it ]]),
        data: new Record.data(),
      });

      return global__.setIn(['memory', referer, 'locations', name], it_);
    } else {

      const { it, global: global_ } = global.newLocation({
        tag,
        locations: new Map([[ UpLevel, global.tyPointer ]]),
        data: new tag.data(),
      });

      return global_.setIn(['memory', referer, 'locations', name], it);
    }
  },
  // UNIFY(
  //   global: Firmament,
  //   { primary, other }: UnifySignal): Firmament {
  //   // always take the other side!
  //   const you = global.getLocation(other);
  //   // TODO: introduce sharing? Symbol('REDIRECT') sentinel?
  //   return global.setIn(['memory', primary], you);
  // },
};


export const Hole = {
  name: 'Hole',
  symbol: HOLE,
  type: INTRODUCTION,
  minLevel: 0,
  handlers: holeHandlers,
  render: HoleView,
};
