/* eslint react/no-multi-comp: 0 */
import React, { Component, PropTypes } from 'react';
import { OrderedMap } from 'immutable';

import Firmament from './Firmament';
import { Location } from './Location';
import { Record, RecordView, RecordTy, RecordTyView, Projection, ProjectionView } from './Record';
import { Variant, VariantView, VariantTy, VariantTyView } from './Variant';

import { messages } from '../messages';

const {
  FILL_HOLE
} = messages;


export class Hole {
  handlers = {
    FILL_HOLE(global, signal) {
      const { selectedType, path } = signal;
      const loc = global.get(path);

      let global_ = global;
      let implementation;
      let type;
      let implementationView = new Hole();
      let typeView = HoleView;

      // TODO use a sentinel to implement all of these
      if (selectedType === 'projection') {
        implementation = new Projection({
          // tag,
          // record,
        });
        implementationView = ProjectionView;
        // leave the type and typeView as holes?
      } else if (selectedType === 'record') {
        implementation = new Record();
        implementationView = RecordView;
        type = new RecordTy();
        typeView = RecordTyView;
      } else { // 'variant'
        // start this variant off with a single option for now
        const tag = 'A';

        // XXX hack
        const holePath = path.concat(['_type', tag]);
        global_ = global.set(holePath, holeLoc);

        const tags = OrderedMap({ A: holePath });
        implementation = new Variant({ tag });
        implementationView = VariantView;
        type = new VariantTy({ tags });
        typeView = VariantTyView;
      }

      const location_ = loc.merge({
        implementation,
        implementationView,
        type,
        typeView,
      });

      // TODO garbage collect field?
      return global_.set(path, location_);
    },
  };
}


export class HoleView extends Component {

  static propTypes = {
    path: PropTypes.arrayOf(PropTypes.string).isRequired,
    level: PropTypes.number.isRequired,
  };

  static contextTypes = {
    update: PropTypes.func.isRequired,
    signal: PropTypes.func.isRequired,
    global: PropTypes.instanceOf(Firmament).isRequired,
  };

  handleSelectChange(event) {
    const selectedType = event.target.value;
    const { path, level } = this.props;

    if (selectedType !== '') {
      this.context.signal(
        path,
        { action: FILL_HOLE, selectedType, path, level }
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
                  <option value='projection'>Projection</option>
                </select>
        </div>
      </div>
    );
  }
}


export const holeLoc = new Location({
  implementation: new Hole(),
  implementationView: HoleView,
  type: new Hole(),
  typeView: HoleView,
});


export const implementationHole = {
  implementation: new Hole(),
  implementationView: HoleView,
};


export const typeHole = {
  type: new Hole(),
  typeView: HoleView,
};
