// @flow

import { List } from 'immutable';
import React, { Component, PropTypes } from 'react';

import { expr } from '../../components/Expression';
import AppData from './data';
import styles from './styles.scss';

export default class App extends Component {
  static propTypes = {
    children: PropTypes.instanceOf(AppData).isRequired,
    path: PropTypes.instanceOf(List).isRequired,
  };

  render() {
    const { path, children: item } = this.props;

    return (
      <div className={styles.app}>
        {expr(item, path, 'func')}
        {expr(item, path, 'arg')}
      </div>
    );
  }
}
