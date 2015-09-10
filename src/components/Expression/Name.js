// names (that you can click on)

import React, {Component, PropTypes} from 'react';

import { AbsRef, mkAbs } from '../../theory/ref';
import { Hole } from '../../theory/tm';
import childJoin from '../childJoin';

const styles = require('./Name.scss');


class NameContextMenu extends Component {
  static contextTypes = {
    updateAt: PropTypes.func.isRequired,
  };

  render() {
    return (
      <div className={styles.nameContextMenu}
           onClick={::this.handleUnbind}>
        unbind
      </div>
    );
  }

  // replace this instance of the variable with a hole of the same type
  handleUnbind() {
    const { name, path } = this.props;
    this.context.updateAt(
      new AbsRef({ path }),
      ({ type }) => new Hole({ name, type })
    );
  }
}


export default class Var extends Component {
  state = { expanded: false };

  static contextTypes = {
    lookupRef: PropTypes.func.isRequired,
  };

  render() {
    // a ref doesn't know its name or type, but it does know where to find
    // them.
    const nameRef = this.props.children.ref;
    const path = this.props.path;

    var absRef: AbsRef;
    if (nameRef instanceof AbsRef) {
      absRef = nameRef;
    } else {
      absRef = new AbsRef({ path }).extend(nameRef);
    }
    const binder = this.context.lookupRef(absRef);
    console.log('looking up', absRef.path, binder);
    const { name, type } = binder;

    const ctxMenu = this.state.expanded &&
      <NameContextMenu name={name}
                       path={path} />

    return (
      <div className={styles.name}
           onClick={::this.handleClick}>
        {name}
        <div className={styles.nameAbs}>
          {ctxMenu}
        </div>
      </div>
    );
  }

  handleClick() {
    this.setState({ expanded: !this.state.expanded });
  };
}
