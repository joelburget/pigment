import React, { PropTypes, Component } from 'react';
import ReactDOM from 'react-dom';

import { Module, ModuleTy, ModuleView, ModuleTyView } from './models/Module';
import { Location } from './models/Location';
import Firmament, { fromBaseLocation } from './models/Firmament';


const initialBaseLocation = new Location({
  implementation: new Module(),
  implementationView: ModuleView,
  type: new ModuleTy(),
  typeView: ModuleTyView,
});


export default class Page extends Component {

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
        <ModuleView path={[]} level={0} />
        <ModuleTyView path={[]} level={1} />
      </div>
    );
  }
}

const typedTermStyle = {
  display: 'flex',
  flexDirection: 'row',
};


ReactDOM.render(<Page />, document.getElementById('root'));
