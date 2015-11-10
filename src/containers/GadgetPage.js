import React, { PropTypes, Component } from 'react';
// import { bindActionCreators } from 'redux';
// import { connect } from 'react-redux';
// import * as GadgetActions from '../actions/gadgets';

import { Module, ModuleTy, ModuleView, ModuleTyView } from '../models/Module';
import { Location } from '../models/Location';
import Firmament, { fromBaseLocation } from '../models/Firmament';


// function mapStateToProps(state) {
//   return {
//     // note plural to singular
//     gadget: state.gadgets,
//     path: [],
//     name: 'base',
//   };
// }


// function mapDispatchToProps(dispatch) {
//   return bindActionCreators(GadgetActions, dispatch);
// }


const initialBaseLocation = new Location({
  implementation: new Module(),
  implementationView: ModuleView,
  type: new ModuleTy(),
  typeView: ModuleTyView,
});


export default class GadgetPage extends Component {

  static childContextTypes = {
    update: PropTypes.func,
    signal: PropTypes.func,
    global: PropTypes.instanceOf(Firmament),
  };

  state = {
    global: fromBaseLocation(initialBaseLocation),
  };

  getChildContext() {
    return {
      signal: (path, action) => this.signal(path, action),
      update: global => this.setState({ global }),
      global: this.state.global,
    };
  }

  signal(path, action) {
    const { global } = this.state;
    const location = global.get(path);
    const newGlobal = location.signal(global, action);
    this.setState({ global: newGlobal });
  }

  render() {
    return (
      <div style={typedTermStyle}>
        <ModuleView
          name='root'
          path={[]}
          focus='implementation' />
        <ModuleTyView
          name='root'
          path={[]}
          focus='type' />
      </div>
    );
  }
}

const typedTermStyle = {
  display: 'flex',
  flexDirection: 'row',
};


// export default connect(mapStateToProps, mapDispatchToProps)(Gadget);
