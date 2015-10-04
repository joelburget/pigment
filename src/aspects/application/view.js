// @flow

import { Component, PropTypes } from 'react';
import styles from './styles.scss';

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
