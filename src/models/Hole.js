/* eslint react/no-multi-comp: 0 */
import React, { Component, PropTypes } from 'react';
import { OrderedMap } from 'immutable';

import { messages } from './Gadget';
import Firmament from './Firmament';
import { Location } from './Location';
import { Record, RecordView, RecordTy, RecordTyView } from './Record';
import { Variant, VariantView, VariantTy, VariantTyView } from './Variant';


const {
  FILL_HOLE
} = messages;


export class Hole {
  receiveSignal(global, signal) {
    switch (signal.action) {
    case FILL_HOLE: {
      const { selectedType, path } = signal;
      const loc = global.get(path);

      let implementation, type, implementationView, typeView, global_ = global;
      if (selectedType === 'record') {
        implementation = new Record();
        implementationView = RecordView;
        type = new RecordTy();
        typeView = RecordTyView;
      } else { // 'variant'
        // start this variant off with a single option for now
        const tag = 'A';

        const holeLoc = new Location({
          implementation: new Hole(),
          implementationView: HoleView,
          type: new Hole(),
          typeView: HoleView,
        });

        // XXX hack
        const holePath = path.concat(['_type', tag]);
        global_ = global.set(holePath, holeLoc);

        const tags = OrderedMap({ A: holePath });
        implementation = new Variant({ tag });
        implementationView = VariantView;
        type = new VariantTy({ tags });
        typeView = VariantTyView;
      }
      const location_ = new Location({
        implementation,
        implementationView,
        type,
        typeView,
        documentation: loc.documentation,
      });

      // TODO garbage collect field?
      return global_.set(path, location_);
    }

    default:
      console.warn(
        'Warning: Hole unhandled signal: ' + signal.action,
        signal
      );
      return global;
    }
  }
}


export class HoleView extends Component {

  static propTypes = {
    path: PropTypes.arrayOf(PropTypes.string).isRequired,
  };

  static contextTypes = {
    update: PropTypes.func.isRequired,
    signal: PropTypes.func.isRequired,
    global: PropTypes.instanceOf(Firmament).isRequired,
  };

  handleSelectChange(event) {
    const selectedType = event.target.value;
    const { path } = this.props;

    if (selectedType !== '') {
      this.context.signal(
        path,
        { action: FILL_HOLE, selectedType, path }
      );
    }
  }

  render() {
    return (
      <div>
        <div>
          type: <select value='default' onChange={val => this.handleSelectChange(val)}>
                  <option value='default' disabled></option>
                  <option value='record'>Record</option>
                  <option value='variant'>Variant</option>
                </select>
        </div>
      </div>
    );
  }
}
