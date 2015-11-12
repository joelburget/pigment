import { Record as ImmRecord, OrderedMap } from 'immutable';
import React, { Component, PropTypes } from 'react';

import { messages } from './Gadget';
import Firmament from './Firmament';

const {
  SET_TAG,
  ADD_VARIANT,
  REMOVE_VARIANT
} = messages;


export const Variant = ImmRecord({
  tag: null,
});

export class VariantTy extends ImmRecord({ tags: OrderedMap() }) {
  handlers = {
    SET_TAG(global, signal) {
      const { path, tag } = signal;
      const loc = global.get(path);

      const location_ = loc.set('implementation', tag);
      return global.set(path, location_);
    },

    ADD_VARIANT(global, signal) {
      const { path, tag, type } = signal;
      const loc = global.get(path);

      loc.type.tags.set(tag, type);
    },

    REMOVE_VARIANT(global, signal) {
      const { path, tag } = signal;
      const loc = global.get(path);

      // XXX how to handle if implementation uses that variant?
      loc.type.tags.delete(tag);
    },
  };
}

export class VariantView extends Component {

  static contextTypes = {
    update: PropTypes.func.isRequired,
    signal: PropTypes.func.isRequired,
    global: PropTypes.instanceOf(Firmament).isRequired,
  };

  render() {
    const { global } = this.context;
    const { name, path } = this.props;
    const location = global.get(path);
    const { implementation } = location;

    return (
      <div>
        VariantView: {implementation.tag}
      </div>
    );
  }
}


export class VariantTyView extends Component {

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
      .tags
      .map((value, key) => {
        const clickHandler = () => {
          this.context.signal(path, { action: REMOVE_VARIANT, name: key, path });
        };

        // XXX hack
        const rowLoc = global.get(path.concat(['_type', key]));
        const RowComponent = rowLoc.typeView;

        return (
          <div style={rowStyle} key={key}>
            <button onClick={clickHandler}>[delete]</button>
            <RowComponent
              name={key}
              path={path.concat(key)} />
          </div>
        );
      })
      .toArray();


    return (
      <div>
        VariantTyView:
          <div style={rowsStyle}>
            {rows}
          </div>
      </div>
    );
  }
}

const rowsStyle = {
  marginLeft: 10,
  display: 'flex',
  flexDirection: 'column',
};

const rowStyle = {
  display: 'flex',
  flexDirection: 'row',
};
