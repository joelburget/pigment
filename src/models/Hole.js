// @flow
import { Map, Record as ImmRecord } from 'immutable';
import React, { Component, PropTypes } from 'react';
import Autocomplete from 'react-autocomplete';

import { Colon } from './Colon';
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

const HoleData = ImmRecord({});

type Scope = Map<string, Symbol>;

function getInScope(global: Firmament, { root, steps }: Path): Scope {
  let inAllScope: Scope = Map();
  let currentPointer = root;
  let thisLoc = global.getLocation(currentPointer);

  for (let step of steps) {
    const inThisScope: Map<string, Symbol> =
      thisLoc.tag.getNamesInScope(thisLoc);

    // important: to merge in this scope, overwriting shadowed names. even
    // better would be to not allow shadowing
    inAllScope = inAllScope.merge(inThisScope);

    // important: we start off examining root, never actually examine the last
    // step (which can't add anything to its own scope)
    thisLoc = global.getLocation(thisLoc.locations.get(step));
  }

  return inAllScope;
}

class HoleView extends Component<{}, { path: Path }, {}> {

  static contextTypes = {
    signal: PropTypes.func.isRequired,
    // cycle :(
    // global: PropTypes.instanceOf(Firmament).isRequired,
    global: PropTypes.object.isRequired,
  };

  handleSelectChange(action) {
    const { path } = this.props;
    const { global, signal } = this.context;

    const path_ = {
      root: path.root,
      steps: path.steps.slice(0, -1),
    };

    // need to get the holder of the hole so we can modify it
    const referer = global.followPath(path_);
    const holeName = path.steps[path.steps.length-1];

    signal(
      path,
      { ...action, referer, holeName }
    );
  }

  // TODO - enumerate a list of things this says it can accept
  render(): Element {
    const { path } = this.props;
    const { global } = this.context;
    const level = path.steps.filter(step => step === UpLevel).length;

    const namesInScope: Scope = getInScope(global, path);
    let nameOptions: Array<[string, Symbol]> =
      namesInScope.entrySeq().toArray();
    nameOptions = nameOptions.filter(([ _, sym ]) => sym !== global.holePointer);
    nameOptions = nameOptions.map(([ name, sym ]) => ({
      action: FILL_HOLE,
      type: 'REFERENCE',
      name,
      sym,
    }));
    nameOptions = nameOptions.concat([
      { action: FILL_HOLE, type: 'INTRODUCTION', name: 'Record' },
      { action: FILL_HOLE, type: 'INTRODUCTION', name: 'Ty' },
      { action: FILL_HOLE, type: 'INTRODUCTION', name: 'Colon' },
      // RecordTy, Module, ModuleTy, VariantTy
      //
      // how to deal with Variant?
    ]);

    // TODO: put meta info somewhere
    // level: {level}

    return (
      <div>
        <Autocomplete
          items={nameOptions}
          getItemValue={({ name }) => name}
          shouldItemRender={({ name }, str) => {
            const re = new RegExp(str, 'i');
            return re.test(name);
          }}
          renderItem={({ name }, isHighlighted) => (
            <div
              key={name}
              style={isHighlighted ? styles.highlightedItem : styles.item}
            >
              {name}
            </div>
          )}
          onSelect={(_, action) => this.handleSelectChange(action)}
        />
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
    action: FillHoleSignal
  ): Firmament {
    const { type, referer, holeName } = action;

    if (type === 'REFERENCE') {
      throw new Error('REFERENCE not yet implemented');
    } else { // type === 'INTRODUCTION'
      const { name } = action;

      const tagMap = {
        Record,
        Ty,
        Colon,
      };

      const tag = tagMap[name];

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

        return global__.setIn(['memory', referer, 'locations', holeName], it_);
      } else {

        const { it, global: global_ } = global.newLocation({
          tag,
          locations: new Map([[ UpLevel, global.tyPointer ]]),
          data: new tag.data(),
        });

        return global_.setIn(['memory', referer, 'locations', holeName], it);
      }
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


const styles = {
  item: {
  },
  highlightedItem: {
    borderLeft: '2px solid gray',
  },
};


export const Hole = {
  name: 'Hole',
  symbol: HOLE,
  type: INTRODUCTION,
  minLevel: 0,
  handlers: holeHandlers,
  render: HoleView,
  data: HoleData,
};
