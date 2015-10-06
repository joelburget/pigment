import React, { Component, PropTypes } from 'react';
import FlatButton from 'material-ui/lib/flat-button';

import Expression from '../../components/Expression';
import style from './style.scss';


export default class Row extends Component {
  render() {
    const children = this.props.children.entries
      .entrySeq()
      .toArray()
      .map(([name, value]) => {
        return (
          <Expression path={this.props.path.push(name)}>
            {value}
          </Expression>
        );
      });

    return (
      <div className={style.row}>
        <div>{'{'}</div>
        <div>
          {children}
        </div>
        <div>{'}'}</div>
      </div>
    );
  }

  handleAdd(event) {
  }
}
