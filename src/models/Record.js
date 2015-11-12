import { Record as ImmRecord, OrderedMap } from 'immutable';
import React, { Component, PropTypes } from 'react';

import Firmament from './Firmament';
import { holeLoc } from './Hole';
import Merger from './Merger';

import { messages } from '../messages';
import deleteButton from '../actions/remove_field';


const INTRODUCTION = Symbol('introduction form');
const ELIMINATION = Symbol('elimination form');
const METAVAR = Symbol('metavariable');


const {
  SET_FIELD,
  UNIFY,
  STEP,
} = messages;

export const Record = ImmRecord({
  fields: OrderedMap(),
});

const ProjectionTyShape = ImmRecord({
  recordTy: METAVAR,
  tag: METAVAR,
  resultTy: METAVAR,
});

// And elimination can require two types to be the same -- if so, it simply has
// two references to the same location. (what about equality?)
export class ProjectionTy extends ProjectionTyShape {
  type = ELIMINATION;

  handlers = {
    // TODO - think about not using global all over the place
    // TODO what's the best name for this? It's not really unification --
    // "take a look at your children and
    [UNIFY](global, path) {
      // record and tag need to agree on a field name
      const loc = global.get(path);
      const { recordTy, tag } = loc;

      let recordTy_ = recordTy;
      let tag_ = tag;

      if (recordTy === METAVAR && tag === METAVAR) {
      } else if (recordTy === METAVAR) {
        // this must must have `tag` in it
      } else if (tag === METAVAR) {
        // this must come from the set of tags in record
      } else {
        // find out if it's possible to unify them! do both of the previous
        // constraints hold?
      }
    },

    [STEP](global, path) {
      const loc = global.get(path);
    },
  };
}

export const Projection = ImmRecord({
  // TODO also point to record location

  // This is tricky -- we need to be able to fill in tag, but it must be
  // limited to the tags this record supports. Need some protocol for queries.
  tag: null,
  record: null,
});

export class RecordTy extends ImmRecord({ fields: OrderedMap() }) {
  type = INTRODUCTION;

  handlers = {
    // XXX - need to distinguish these things between type and value level
    [SET_FIELD](global, signal) {
      const { path, name } = signal;
      const loc = global.get(path);

      const implementation = new Record({
        fields: loc.implementation.fields.set(name, path.concat(name)),
      });
      const type = new RecordTy({
        fields: loc.type.fields.set(name, path.concat(name)),
      });

      const location_ = loc.merge({ implementation, type });
      const namePath = path.concat(name);

      return global
        .set(path, location_)
        .set(namePath, holeLoc);
    },

    [REMOVE_FIELD](global, signal) {
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
    },

    [UNIFY](global, signal) {
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
    },
  };
}


export class ProjectionView extends Component {

  static propTypes = {
    path: PropTypes.arrayOf(PropTypes.string).isRequired,
    name: PropTypes.string.isRequired,
    level: PropTypes.number.isRequired,
  };

  static contextTypes = {
    update: PropTypes.func.isRequired,
    global: PropTypes.instanceOf(Firmament).isRequired,
  };

  render() {
    const { global } = this.context;
    const { path, level } = this.props;
    const location = global.get(path);
    const { tag } = location;

    return (
      <div>
        <RecordView path={path.concat('record')} name={'XXX(name)'} level={level} />.{tag}
      </div>
    );
  }
}


export class RecordTyView extends Component {

  static propTypes = {
    path: PropTypes.arrayOf(PropTypes.string).isRequired,
    name: PropTypes.string.isRequired,
    level: PropTypes.number.isRequired,
  };

  static contextTypes = {
    update: PropTypes.func.isRequired,
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
        const rowLoc = global.get(path.concat(key));
        const RowComponent = rowLoc.typeView;

        return (
          <div style={rowStyle} key={key}>
            {deleteButton.call(this, [], key)}
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
        <RowControls path={path} />
        {'}'}
      </div>
    );
  }
}


export class RecordView extends Component {

  static propTypes = {
    path: PropTypes.arrayOf(PropTypes.string).isRequired,
    name: PropTypes.string.isRequired,
    level: PropTypes.number.isRequired,
  };

  static contextTypes = {
    update: PropTypes.func.isRequired,
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
        const rowLoc = global.get(path.concat(key));
        const RowComponent = rowLoc.implementationView;

        return (
          <div style={rowStyle} key={key}>
            {deleteButton.call(this, [], key)}
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
        <RowControls path={path} />
        {'}'}
      </div>
    );
  }
}


class RowControls extends Component {

  static propTypes = {
    path: PropTypes.arrayOf(PropTypes.string).isRequired,
  };

  static contextTypes = {
    signal: PropTypes.func.isRequired,
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
      this.context.signal(
        this.props.path,
        {
          action: SET_FIELD,
          name: this.state.nameInput,
          path: this.props.path,
          type: this.state.selectedType,
        }
      );
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
