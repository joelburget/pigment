// @flow
import { Map, Record as ImmRecord, Set } from 'immutable';
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

import type Firmament, {
  Path,
  WithGlobal,
} from './Firmament';
import type {
  ImmediateFill,
  Reference,
  Introduction,
  FillHoleSignal,
  PokeHoleSignal,
} from '../messages';


const HOLE = Symbol('HOLE');

const HoleData = ImmRecord({});

type Scope = Map<string, Symbol>;

// The information needed to make an autocompletion. How to fill the hole and
// what to call it. We'll additionally send the referer and hole name with the
// fill signal.
type FillCompletion = (ImmediateFill | Reference) & { name: string };

function getInScope(global: Firmament, { root, steps }: Path): Scope {
  let inAllScope: Scope = Map();
  let currentPointer = root;

  for (let step of steps) {
    const currentLoc = global.getLocation(currentPointer);

    const inThisScopeSet: Set<string> = currentLoc.tag
      .getNamesInScope(currentLoc)
      // HACK
      .delete(UpLevel);
    // // CONFUSING: map from name to its parent
    const inThisScope = inThisScopeSet.toMap().map(() => currentPointer);

    // important: to merge in this scope, overwriting shadowed names. even
    // better would be to not allow shadowing
    inAllScope = inAllScope.merge(inThisScope);

    // important: we start off examining root, never actually examine the last
    // step (which can't add anything to its own scope)
    currentPointer = currentLoc.locations.get(step);
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

  handleSelectChange(fill: FillCompletion) {
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
      {
        action: FILL_HOLE,
        referer,
        holeName,
        fill,
      }
    );
  }

  // TODO - enumerate a list of things this says it can accept
  render(): Element {
    const { path } = this.props;
    const { global } = this.context;
    const level = path.steps.filter(step => step === UpLevel).length;

    const namesInScope: Scope = getInScope(global, path);
    let nameOptions: Array<FillCompletion> = namesInScope
      .entrySeq()
      .toArray()
      .map(([ name, parent ]) => ({
        tag: 'REFERENCE',
        name,
        parent,
      }));
    nameOptions = nameOptions.concat([
      { tag: 'IMMEDIATE_FILL', name: 'Record', introduction: Record },
      { tag: 'IMMEDIATE_FILL', name: 'Ty', introduction: Ty },
      { tag: 'IMMEDIATE_FILL', name: 'Colon', introduction: Colon },
      // RecordTy, Module, ModuleTy, VariantTy
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
    const { fill, referer, holeName } = action;

    if (fill.tag === 'REFERENCE') {
      return global.setIn(
        ['memory', referer, 'locations', holeName],
        fill
      );
    } else { // fill.tag === 'IMMEDIATE_FILL'
      const { introduction } = fill;

      if (introduction === Record) {

        const { it, global: global_ } = global.newLocation({
          tag: RecordTy,
          locations: new Map([
            [ UpLevel, { tag: 'IMMEDIATE', location: global.tyPointer } ]
          ]),
          data: new RecordTy.data(),
        });

        const { it: it_, global: global__ } = global_.newLocation({
          tag: Record,
          locations: new Map([
            [ UpLevel, { tag: 'IMMEDIATE', location: it } ]
          ]),
          data: new Record.data(),
        });

        return global__.setIn(
          ['memory', referer, 'locations', holeName],
          { tag: 'IMMEDIATE', location: it_ }
        );
      } else {

        const { it, global: global_ } = global.newLocation({
          tag: introduction,
          locations: new Map([
            [ UpLevel, { tag: 'IMMEDIATE', location: global.tyPointer } ]
          ]),
          data: new introduction.data(),
        });

        return global_.setIn(
          ['memory', referer, 'locations', holeName],
          { tag: 'IMMEDIATE', introduction }
        );
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
