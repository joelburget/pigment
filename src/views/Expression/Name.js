// names (that you can click on)

import React, {Component, PropTypes} from 'react';

import childJoin from '../childJoin';

const styles = require('./Name.scss');


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


export default class Ref extends Component {
  state = { expanded: false };

  static contextTypes = {
    lookupRef: PropTypes.func.isRequired,
  };

  render() {
    // a ref doesn't know its name or type, but it does know where to find
    // them.
    const nameRef = this.props.children;

    const name = 'xname'; // TODO get from context
    const type = 'type'; // TODO get from context

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
    console.log(this.context.lookupRef(this.props.children));
    // this.setState({ expanded: !this.state.expanded });
  };
}
