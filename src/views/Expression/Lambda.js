// lambda and pi

import React, {Component, PropTypes} from 'react';
import childJoin from '../childJoin';
import Name from './Name';
import Expression from '../Expression';
import { Var } from '../../theory/tm';
import styles from './Lambda.scss';


export class Lambda extends Component {
  static propTypes = {
    // names: PropTypes.array,
  };

  render() {
    // const { names, result } = this.props.children;

    const binder = this.props.children.binder;
    const body = this.props.children.body;
    const { path } = this.props;

    // XXX gross making this var here
        // {names.map(name => <Name>{new Var(name).children}</Name>)}
    return (
      <div className={styles.lambda}>
        { binder }
        <div>
          <span className={styles.arr}>&#8614;</span>
        </div>
        <Expression path={path.push('body')}>{body}</Expression>
      </div>
    );
  }
}


export class Arr extends Component {
  render() {
    const { domain, codomain } = this.props.children;
    const { path } = this.props;

    return (
      <div className={styles.pi}>
        <Expression path={path.push('domain')}>{domain}</Expression>
        <span>&rarr;</span>
        <Expression path={path.push('codomain')}>{codomain}</Expression>
      </div>
    );
  }
}
