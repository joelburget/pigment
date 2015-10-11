// names (that you can click on)

import React, {Component, PropTypes} from 'react';

import { AbsRef } from '../../theory/ref';
import { Hole } from '../../theory/tm';

const styles = require('./Name.scss');


class NameContextMenu extends Component {
  static contextTypes = {
    updateAt: PropTypes.func.isRequired,
  };

  // replace this instance of the variable with a hole of the same type
  // TODO this logic should not be here!
  handleUnbind() {
    const { name, path } = this.props;
    this.context.updateAt(
      new AbsRef({ path }),
      ({ type }) => new Hole({ name, type })
    );
  }

  render() {
    return (
      <div className={styles.nameContextMenu}
           onClick={::this.handleUnbind}>
        unbind
      </div>
    );
  }
}


export default class Var extends Component {
  static contextTypes = {
    lookupRef: PropTypes.func.isRequired,
  };

  state = { expanded: false };

  handleClick() {
    this.setState({ expanded: !this.state.expanded });
  }

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
    const { name } = this.context.lookupRef(absRef);

    const ctxMenu = this.state.expanded &&
      <NameContextMenu name={name}
                       path={path} />;

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
}
