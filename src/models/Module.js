// @flow
import { Record, List } from 'immutable';
import React, { Component, PropTypes } from 'react';

import Firmament, { UpLevel } from './Firmament';
import {
  NEW_FIELD,
  INTRODUCTION,
  REMOVE_FIELD,
} from '../messages';
import { handler as removeField } from '../actions/remove_field';
import { handler as newField } from '../actions/new_field';
import { column } from '../styles/flex';
import Rows from '../components/Rows';

import type { Element } from 'react';
import type { Path } from './Firmament';

import type {
  ImplementationUpdatedSignal,
  ReferenceUpdatedSignal,
  NewFieldSignal,
  RemoveFieldSignal,
} from '../messages';


const MODULE = Symbol('MODULE');
const MODULE_TY = Symbol('MODULE_TY');


const ModuleData = Record({
  fields: List(),
});

const ModuleTyData = Record({
  fields: List(),
});

function moduleTyUpdate(
  global: Firmament,
  signal: ImplementationUpdatedSignal
): Firmament {

  if (signal.signal.action === NEW_FIELD || signal.signal.action === REMOVE_FIELD) {
    const subSignal : NewFieldSignal | RemoveFieldSignal = signal.signal;
    const target: Symbol = signal.target;
    const { action, name, path: { root, steps } } = subSignal;

    const signal_ = {
      // Flow apparently isn't sophisticated enough to understand this could be
      // of either type.
      // $FlowIgnore: I think this is fine...
      action,
      name,
      path: {
        root,
        steps: steps.concat(UpLevel),
      },
    };

    return action === NEW_FIELD ?
      newField(global, signal_) :
      removeField(global, signal_);
  }

  return global;
}

function moduleUpdate(
  global: Firmament,
  signal: ReferenceUpdatedSignal
): Firmament {

  const original = global.getLocation(signal.original);

  if ((signal.signal.action === NEW_FIELD || signal.signal.action === REMOVE_FIELD) && original.tag === ModuleTy) {
    const { referer, original, signal: { action, name, path: { root, steps } } } = signal;

    // XXX need to treat differently depending on what kind of reference this is
    const signal_ = {
      // Flow apparently isn't sophisticated enough to understand this could be
      // of either type.
      // $FlowIgnore: I think this is fine...
      action,
      name,
      path: {
        root: referer, // XXX
        steps: [],
      },
    };

    return action === NEW_FIELD ?
      newField(global, signal_) :
      removeField(global, signal_);
  }

  return global;
}

// Need to figure out how these handlers can really have a different effect for
// Module vs ModuleTy. A module change affects its type and vice-versa. They're
// tied together. Modules are tied upward and ModuleTys are tied downward.
const fieldHandlers = {
  NEW_FIELD: newField,
  REMOVE_FIELD: removeField,
};


const contextTypes = {
  signal: PropTypes.func.isRequired,
  global: PropTypes.instanceOf(Firmament).isRequired,
};


const propTypes = {
  path: PropTypes.shape({
    root: PropTypes.symbol,
    steps: PropTypes.array,
  }).isRequired,
};


class ModuleTyView extends Component<{}, { path: Path }, {}> {

  static propTypes = propTypes;
  static contextTypes = contextTypes;

  render(): Element {
    const { global } = this.context;
    const { path } = this.props;
    const loc = global.getPath(path);

    return (
      <div style={column}>
        ModuleTy:
        <Rows fields={loc.data.fields} path={path} />
        <Controls signal={action => { this.context.signal(path, action); }} />
      </div>
    );
  }
}


export class ModuleView extends Component<{}, { path: Path }, {}> {

  static propTypes = propTypes;
  static contextTypes = contextTypes;

  render(): Element {
    const { global } = this.context;
    const { path } = this.props;
    const loc = global.getPath(path);

    return (
      <div style={styles.module}>
        Module:
        <Rows fields={loc.data.fields} path={path} />
        <Controls signal={action => { this.context.signal(path, action); }} />
      </div>
    );
  }
}


type ControlsProps = {
  signal: (sig: NewFieldSignal) => void;
};


class Controls extends Component<{}, ControlsProps, {nameInput: string}> {

  static propTypes = {
    signal: PropTypes.func.isRequired,
  };

  state = {
    nameInput: '',
  };

  handleChange(nameInput) {
    this.setState({ nameInput });
  }

  handleKeyPress(event) {
    if (event.key === 'Enter') {
      this.props.signal({
        action: NEW_FIELD,
        name: this.state.nameInput,
      });
      this.setState({ nameInput: '' });
    }
  }

  render(): Element {
    const { nameInput } = this.state;

    const valueLink = {
      value: nameInput,
      requestChange: value => this.handleChange(value),
    };

    return (
      <div style={styles.control}>
        <input
          type='text'
          valueLink={valueLink}
          onKeyPress={event => this.handleKeyPress(event)}
        />
      </div>
    );
  }
}


const styles = {
  module: {
    ...column,
    margin: '10px 0',
  },
  control: {
    marginTop: 20,
  }
};


export const Module = {
  name: 'Module',
  symbol: MODULE,
  type: INTRODUCTION,
  minLevel: 0,
  handlers: {
    ...fieldHandlers,
    REFERENCE_UPDATED: moduleUpdate,
  },
  render: ModuleView,
  data: ModuleData,
};

export const ModuleTy = {
  name: 'ModuleTy',
  symbol: MODULE_TY,
  type: INTRODUCTION,
  minLevel: 1,
  handlers: {
    ...fieldHandlers,
    IMPLEMENTATION_UPDATED: moduleTyUpdate,
  },
  render: ModuleTyView,
  data: ModuleTyData,
};
