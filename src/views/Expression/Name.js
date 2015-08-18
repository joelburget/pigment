// names (that you can click on)

import React, {Component, PropTypes} from 'react';
import childJoin from '../childJoin';
import {requireServerCss} from '../../util';

const styles = __CLIENT__ ?
  require('./Name.scss') :
  requireServerCss(require.resolve('./Name.scss'));


class NameContextMenu extends Component {
  render() {
    return (
      <ul classname={styles.nameContextMenu}>
        <li>TODO</li>
        <li>{this.props.children}</li>
        <li>context</li>
        <li>menu</li>
      </ul>
    );
  }
}


export default class Name extends Component {
  state = { expanded: false };

  render() {
    const [ nameAbt ] = this.props.children;
    const { name } = nameAbt;

    return (
      <div className={styles.name}
           onClick={this.handleClick}>
        {name}
        <div className={styles.nameAbs}>
          {this.state.expanded && <NameContextMenu>{name}</NameContextMenu>}
        </div>
      </div>
    );
  }

  handleClick = () => {
    // this.setState({ expanded: !this.state.expanded });
  };
}
