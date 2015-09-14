// @flow

import React, { Component, PropTypes } from 'react';

import { Var } from '../../theory/tm';
import Name from '../../components/Expression/Name';
import Expression from '../../components/Expression';

import styles from './style.scss';


export class Binder extends Component {
  static propTypes = {
    // path
    name: PropTypes.string.isRequired,
    // type: PropTypes
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
    const { name, type, path }= this.props;

    return (
      <div className={styles.expand}>
        <div>{name}</div>
        <div>:</div>
        <Expression path={path.push('type')}>{type}</Expression>
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
    // children
    // path
  };

  render() {
    // const { names, result } = this.props.children;

    const { name, domain, body } = this.props.children;
    const { path } = this.props;

    // XXX gross making this var here
        // {names.map(name => <Name>{new Var(name).children}</Name>)}
    return (
      <div className={styles.lambda}>
        <Binder path={path.push('binder')} name={name} type={domain} />
        <div>
          <span className={styles.arr}>&#8614;</span>
        </div>
        <Expression path={path.push('body')}>{body}</Expression>
      </div>
    );
  }
}
