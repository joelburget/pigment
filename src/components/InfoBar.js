import React, {Component, PropTypes} from 'react';
import {connect} from 'react-redux';
import {requireServerCss} from '../util';

const styles = __CLIENT__ ?
  require('./InfoBar.scss') :
  requireServerCss(require.resolve('./InfoBar.scss'));

class InfoBar extends Component {
  static propTypes = {
    info: PropTypes.object,
  }

  render() {
    // TODO this doesn't currently do anything
    const { info } = this.props;

    return null;
  }
}

@connect(state => ({
  info: state.info.data
}))
export default
class InfoBarContainer {
  static propTypes = {
    info: PropTypes.object,
  };

  render() {
    const { info } = this.props;
    return <InfoBar info={info} />;
  }
}
