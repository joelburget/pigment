// @flow

import React, { Component, PropTypes } from 'react';

export default class App extends Component {
  render() {
    const { func, arg } = this.props.children;
    const { path } = this.props;

    return (
      <div className={styles.app}>
        <Expression path={path.push('func')}>{func}</Expression>
        <Expression path={path.push('arg')}>{arg}</Expression>
      </div>
    );
  }
}
