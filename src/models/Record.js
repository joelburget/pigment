import { Record as ImmRecord, OrderedMap } from 'immutable';
import React, { Component, PropTypes } from 'react';

import Firmament from './Firmament';
import { messages } from './Gadget';
import { Hole, HoleView } from './Hole';
import { Location } from './Location';
import Merger from './Merger';

import deleteButtonStyle from '../styles/deleteButtonStyle';

const {
  SET_FIELD,
  REMOVE_FIELD,
  UNIFY,
} = messages;

export const Record = ImmRecord({
  fields: OrderedMap(),
});

export class RecordTy extends ImmRecord({ fields: OrderedMap() }) {
  receiveSignal(global, signal) {
    switch (signal.action) {
      // XXX we don't consider eliminators here --
      // given a type this assumes its term is the matching introduction, but
      // it could be an eliminator.
      //
      // i guess the same is true of term -> type
      //
      // perhaps the most ergonomic way to deal with this is to introduce a
      // normal form -> eliminator refactor.
    case SET_FIELD: {
      const { path, name } = signal;
      const loc = global.get(path);

      const implementation = new Record({
        fields: loc.implementation.fields.set(name, path.concat(name)),
      });
      const type = new RecordTy({
        fields: loc.type.fields.set(name, path.concat(name)),
      });

      const location_ = loc.merge({ implementation, type });

      const newLocation = new Location({
        implementation: new Hole(),
        implementationView: HoleView,
        type: new Hole(),
        typeView: HoleView,
      });

      const namePath = path.concat(name);
      return global
        .set(path, location_)
        .set(namePath, newLocation);
    }

    case REMOVE_FIELD: {
      const { name, path } = signal;
      const loc = global.get(path);
      const implementation = new Record({
        fields: loc.implementation.fields.delete(name)
      });
      const type = new RecordTy({
        fields: loc.type.fields.delete(name)
      });
      const location_ = loc.merge({ implementation, type });
      // TODO garbage collect field?
      return global.set(path, location_);
    }

    case UNIFY: {
      // Unify *implementations* This doesn't touch type or documentation.
      //
      // TODO - what if the type is only partially specified? I suppose that's
      // fine!
      //
      // what guarantees can we expect of the types?
      const { tm1, tm2 } = signal;

      // take the union of left and right keys then unify their values
      // TODO - how to order the keys?
      const result = tm1
        .mergeWith((left, right) => new Merger(left, right), tm2)
        .map(val => {
          return val instanceof Merger ?
            val.x.signal({
              action: UNIFY,
              term: val.y,
            }) :
            val;
        });

      return global;

      // if right is a metavarable, we give all the information we can!
    }

    default:
      console.warn(
        'Warning: unhandled signal: ' + signal.action,
        signal
      );
      return global;
    }
  }
}


export class RecordTyView extends Component {

  static propTypes = {
    path: PropTypes.arrayOf(PropTypes.string).isRequired,
    name: PropTypes.string.isRequired,
  };

  static contextTypes = {
    update: PropTypes.func.isRequired,
    signal: PropTypes.func.isRequired,
    global: PropTypes.instanceOf(Firmament).isRequired,
  };

  render() {
    const { global } = this.context;
    const { name, path } = this.props;
    const location = global.get(path);
    const { type } = location;

    const rows = type
      .fields
      .map((value, key) => {
        // TODO - Locations should align on the left and right sides.
        const clickHandler = () => {
          this.context.signal(path, { action: REMOVE_FIELD, name: key, path });
        };

        const rowLoc = global.get(path.concat(key));
        const RowComponent = rowLoc.typeView;

        return (
          <div style={rowStyle} key={key}>
            <button onClick={clickHandler} style={deleteButtonStyle}>[delete]</button>
            <RowComponent name={key} path={path.concat(key)} />
          </div>
        );
      })
      .toArray();

    return (
      <div style={colStyle}>
        {name + ': {'}
        <div style={recordTyStyle}>
          {rows}
        </div>
        <RowControls signal={action => { this.context.signal(path, action); }} path={path} />
        {'}'}
      </div>
    );
  }
}


export class RecordView extends Component {

  static propTypes = {
    path: PropTypes.arrayOf(PropTypes.string).isRequired,
    name: PropTypes.string.isRequired,
  };

  static contextTypes = {
    update: PropTypes.func.isRequired,
    signal: PropTypes.func.isRequired,
    global: PropTypes.instanceOf(Firmament).isRequired,
  };

  render() {
    const { name, path } = this.props;
    const { global } = this.context;
    const location = global.get(path);
    const { implementation } = location;

    const rows = implementation
      .fields
      .map((value, key) => {
        const clickHandler = () => {
          this.context.signal(path, { action: REMOVE_FIELD, name: key, path });
        };

        const rowLoc = global.get(path.concat(key));
        const RowComponent = rowLoc.implementationView;

        return (
          <div style={rowStyle} key={key}>
            <button onClick={clickHandler} style={deleteButtonStyle}>[delete]</button>
            <RowComponent name={key} path={path.concat(key)} />
          </div>
        );
      })
      .toArray();

    return (
      <div style={colStyle}>
        {name + ': {'}
        <div style={rowsStyle}>
          {rows}
        </div>
        <RowControls signal={action => { this.context.signal(path, action); }} path={path} />
        {'}'}
      </div>
    );
  }
}


class RowControls extends Component {

  static propTypes = {
    path: PropTypes.arrayOf(PropTypes.string).isRequired,
    signal: PropTypes.func.isRequired
  };

  state = {
    nameInput: '',
    selectedType: 'record',
  };

  handleChange(nameInput) {
    this.setState({ nameInput });
  }

  handleSelectChange(event) {
    const selectedType = event.target.value;
    this.setState({ selectedType });
  }

  handleKeyPress(event) {
    if (event.key === 'Enter') {
      this.props.signal({
        action: SET_FIELD,
        name: this.state.nameInput,
        path: this.props.path,
        type: this.state.selectedType,
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
        <div>
          type: <select value={this.state.selectedType}
                        onChange={val => this.handleSelectChange(val)}>
                  <option value='record'>Record</option>
                  <option value='variant'>Variant</option>
                </select>
        </div>
      </div>
    );
  }
}


const recordTyStyle = {
  display: 'flex',
  flexDirection: 'column',
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
