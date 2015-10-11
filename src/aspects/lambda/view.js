// @flow

import { List } from 'immutable';
import React, { Component, PropTypes } from 'react';

import Expression, { expr } from '../../components/Expression';

import styles from './style.scss';


export class Binder extends Component {
  static propTypes = {
    path: PropTypes.instanceOf(List).isRequired,
    name: PropTypes.string.isRequired,
    type: PropTypes.object.isRequired,
  };

  state = {
    expanded: false,
  };

  toggle() {
    this.setState({ expanded: !this.state.expanded });
  }

  renderExpanded() {
    const { name, type, path } = this.props;

    return (
      <div className={styles.expand}>
        <div>{name}</div>
        <div>:</div>
        <Expression path={path.push('type')}>{type}</Expression>
      </div>
    );
  }

  render() {
    const expanded = this.state.expanded && this.renderExpanded();

    return (
      <span onClick={::this.toggle}>
        <div className={styles.expandContainer}>{expanded}</div>
        {this.props.name}
      </span>
    );
  }
}


export function Arrow({ children: item, path }) {
  return (
    <div>
      {expr(item, path, 'domain')}
      ->
      {expr(item, path, 'codomain')}
    </div>
  );
}


export function Lambda(props) {
  // const { names, result } = this.props.children;

  const { name, domain, body } = props.children;
  const { path } = props;

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
