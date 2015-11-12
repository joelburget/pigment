/* eslint new-cap: 0 */
/* eslint react/no-multi-comp: 0 */
import { Record as ImmRecord, OrderedMap } from 'immutable';
import React, { Component, PropTypes } from 'react';

import { messages } from './Gadget';
import Firmament from './Firmament';
import { holeLoc } from './Hole';

import deleteButton from '../actions/remove_field';
import pokeHoleButton from '../actions/poke_hole';


const {
  MAKE_DEFINITION,
  // XXX dupicated symbol?
  REMOVE_FIELD,
} = messages;


export const Module = ImmRecord({
  definitions: OrderedMap(),
});


export class ModuleTy extends ImmRecord({ definitions: OrderedMap() }) {
  handlers = {
    [MAKE_DEFINITION](global, signal) {
      const { name, typeName } = signal;
      const loc = global.get([]);

      const implementation = new Module({
        definitions: loc.implementation.definitions.set(name, [name]),
      });
      const type = new ModuleTy({
        definitions: loc.type.definitions.set(name, [name]),
      });

      const location_ = loc.merge({ implementation, type });

      return global
        .set([], location_)
        .set([name], holeLoc);
    },

    // TODO - clear up definition / field terminology
    // should we use the same term for both modules and records?
    // they're analogous, but typed differently.
    [REMOVE_FIELD](global, signal) {
      const { name } = signal;
      const loc = global.get([]);
      const implementation = new Module({
        definitions: loc.implementation.definitions.delete(name)
      });
      const type = new ModuleTy({
        definitions: loc.type.definitions.delete(name)
      });
      const location_ = loc.merge({ implementation, type });
      // TODO garbage collect field?
      return global.set([], location_);
    },
  };
}


export class ModuleTyView extends Component {

  static propTypes = {
    path: PropTypes.arrayOf(PropTypes.string).isRequired,
    level: PropTypes.number.isRequired,
  };

  static contextTypes = {
    update: PropTypes.func.isRequired,
    signal: PropTypes.func.isRequired,
    global: PropTypes.instanceOf(Firmament).isRequired,
  };

  render() {
    const { global } = this.context;
    const { path, level } = this.props;
    const loc = global.get(path);
    const type = loc.type;

    const rows = type
      .definitions
      // XXX what *is* the value here, anyway?
      .map((value, key) => {
        const path_ = path.concat(key);
        const rowLoc = global.get(path_);
        const RowComponent = rowLoc.typeView;

        return (
          <div style={rowStyle} key={key}>
            <div style={colStyle}>
              {deleteButton.call(this, path, key)}
              {pokeHoleButton.call(this, path_, level)}
            </div>
            <RowComponent name={key} path={path_} level={level} />
          </div>
        );
      })
      .toArray();

    return (
      <div style={colStyle}>
        {'Module: {'}
        <div style={moduleTyStyle}>
          {rows}
        </div>
        <Controls signal={action => { this.context.signal(path, action); }} />
        {'}'}
      </div>
    );
  }
}


export class ModuleView extends Component {

  static contextTypes = {
    update: PropTypes.func.isRequired,
    signal: PropTypes.func.isRequired,
    global: PropTypes.instanceOf(Firmament).isRequired,
  };

  render() {
    const { global } = this.context;
    const { path, level } = this.props;
    const location = global.get(path);
    const implementation = location.implementation;

    const rows = implementation
      .definitions
      .map((value, key) => {
        const path_ = path.concat(key);
        const rowLoc = global.get(path_);
        const RowComponent = rowLoc.implementationView;

        return (
          <div style={rowStyle} key={key}>
            <div style={colStyle}>
              {deleteButton.call(this, path, key)}
              {pokeHoleButton.call(this, path_, level)}
            </div>
            <RowComponent name={key} path={path_} level={level} />
          </div>
        );
      })
      .toArray();

    return (
      <div style={colStyle}>
        {'Module: {'}
        <div style={rowsStyle}>
          {rows}
        </div>
        <Controls signal={action => { this.context.signal(path, action); }} />
        {'}'}
      </div>
    );
  }
}


class Controls extends Component {

  static propTypes = {
    signal: PropTypes.func.isRequired
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
        action: MAKE_DEFINITION,
        name: this.state.nameInput,
        typeName: this.state.selectedType,
      });
      this.setState({ nameInput: '' });
    }
  }

  render() {
    const { nameInput } = this.state;

    // TODO - can I bundle up both parts of the input with value linking?
    const valueLink = {
      value: nameInput,
      requestChange: value => this.handleChange(value),
    };

    return (
      <div style={controlsStyle}>
        <div>
          New Row
        </div>
        <div>
          label: <input
            type='text'
            valueLink={valueLink}
            onKeyPress={event => this.handleKeyPress(event)} />
        </div>
      </div>
    );
  }
}


const moduleTyStyle = {
  display: 'flex',
  flexDirection: 'column',
};

const controlsStyle = {
  marginTop: 20,
};

const colStyle = {
  display: 'flex',
  flexDirection: 'column',
};

const rowsStyle = {
  marginLeft: 10,
  display: 'flex',
  flexDirection: 'column',
};

const rowStyle = {
  display: 'flex',
  flexDirection: 'row',
};
