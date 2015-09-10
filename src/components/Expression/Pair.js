// pairs and sigmas

import React, {Component, PropTypes} from 'react';
import childJoin from '../childJoin';

import Expression from '../Expression';
import styles from './Pair.scss';


export class Sigma extends Component {
  render() {
    const pieces = this.props.children
      .map(x => <Expression>{x.value}</Expression>);

    return (
      <div className={styles.pair}>
        {childJoin(pieces, <span>&times;</span>)}
      </div>
    );
  }
}


export class Pair extends Component {
  render() {
    const pieces = this.props.children
      .map(x => <Expression>{x.value}</Expression>);

    return (
      <div className={styles.pair}>
        <span>&lang;</span>
        {childJoin(pieces, <span>,</span>)}
        <span>&rang;</span>
      </div>
    );
  }
}
