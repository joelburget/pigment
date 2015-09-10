// lambda and pi

import React, {Component, PropTypes} from 'react';

import { Var } from '../../theory/tm';
import { Binder as TheoryBinder } from '../../theory/lambda';
import childJoin from '../childJoin';
import Name from './Name';
import Expression from '../Expression';

import styles from './Lambda.scss';


export class Binder extends Component {
  static propTypes = {
    children: PropTypes.instanceOf(TheoryBinder),
  };

  state = {
    expanded: false,
  };

  render() {
    var expanded = this.state.expanded && this.renderExpanded();

    return (
      <span onClick={::this.toggle}>
        <div className={styles.expandContainer}>{expanded}</div>
        {this.props.children.name}
      </span>
    );
  }

  renderExpanded() {
    const { name, type }= this.props.children;
    const path = this.props.path.push('type');

    return (
      <div className={styles.expand}>
        <div>{name}</div>
        <div>:</div>
        <Expression path={path}>{type}</Expression>
      </div>
    );
  }

  toggle() {
    console.log('toggle');
    this.setState({ expanded: !this.state.expanded });
  }
}


export class Lambda extends Component {
  static propTypes = {
    // names: PropTypes.array,
  };

  render() {
    // const { names, result } = this.props.children;

    const { binder, body } = this.props.children;
    const { path } = this.props;

    // XXX gross making this var here
        // {names.map(name => <Name>{new Var(name).children}</Name>)}
    return (
      <div className={styles.lambda}>
        <Binder path={path.push('binder')}>{binder}</Binder>
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
