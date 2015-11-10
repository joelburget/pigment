/* eslint new-cap: 0 */
/* eslint react/no-multi-comp: 0 */
import { Record as ImmRecord, OrderedMap } from 'immutable';
import React, { Component, PropTypes } from 'react';

import { messages } from './Gadget';
import Firmament from './Firmament';
import { Location } from './Location';
import { Hole, HoleView } from './Hole';

import deleteButtonStyle from '../styles/deleteButtonStyle';


const {
  MAKE_DEFINITION,
  REMOVE_FIELD,
} = messages;


export const Module = ImmRecord({
  definitions: OrderedMap(),
});


export class ModuleTy extends ImmRecord({ definitions: OrderedMap() }) {
  receiveSignal(global, signal) {
    switch (signal.action) {
    case MAKE_DEFINITION: {
      const { name, typeName } = signal;
      const loc = global.get([]);

      const implementation = new Module({
        definitions: loc.implementation.definitions.set(name, [name]),
      });
      const type = new ModuleTy({
        definitions: loc.type.definitions.set(name, [name]),
      });

      const location_ = loc.merge({ implementation, type });

      const newLocation = new Location({
        implementation: new Hole(),
        implementationView: HoleView,
        type: new Hole(),
        typeView: HoleView,
      });

      return global
        .set([], location_)
        .set([name], newLocation);
    }

    // TODO - clear up definition / field terminology
    // should we use the same term for both modules and records?
    // they're analogous, but typed differently.
    case REMOVE_FIELD: {
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
    }

    default:
      console.warn(
        'Warning: Module unhandled signal: ' + signal.action,
        signal
      );
      return global;
    }
  }
}


export class ModuleTyView extends Component {

  static contextTypes = {
    update: PropTypes.func.isRequired,
    signal: PropTypes.func.isRequired,
    global: PropTypes.instanceOf(Firmament).isRequired,
  };

  render() {
    const { global } = this.context;
    const loc = global.get([]);
    const type = loc.type;

    const rows = type
      .definitions
      // XXX what *is* the value here, anyway?
      .map((value, key) => {
        const clickHandler = () => {
          this.context.signal([], { action: REMOVE_FIELD, name: key });
        };

        const rowLoc = global.get([key]);
        const RowComponent = rowLoc.typeView;

        return (
          <div style={rowStyle} key={key}>
            <button onClick={clickHandler} style={deleteButtonStyle}>[delete]</button>
            <RowComponent name={key} path={[key]} />
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
        <div style={controlsStyle}>
          <Controls signal={action => { this.context.signal([], action); }} />
        </div>
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
    const location = global.get([]);
    const implementation = location.implementation;

    const rows = implementation
      .definitions
      .map((value, key) => {
        const clickHandler = () => {
          this.context.signal([], { action: REMOVE_FIELD, name: key });
        };

        const rowLoc = global.get([key]);
        const RowComponent = rowLoc.implementationView;
        if (RowComponent == null) {
          debugger;
        }

        return (
          <div style={rowStyle} key={key}>
            <button onClick={clickHandler} style={deleteButtonStyle}>[delete]</button>
            <RowComponent name={key} path={[key]} />
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
        <div style={controlsStyle}>
          <Controls signal={action => { this.context.signal([], action); }} />
        </div>
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
      <div>
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
