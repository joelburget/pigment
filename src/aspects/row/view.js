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
        // TODO I think you should really be able to click on any of these rows
        // -- right now you can only click on the expression.
        //
        // Maybe it doesn't make sense to select the row, since it's not really
        // an expression, but you need to be able to rename and remove items,
        // at least.
        return (
          <div className={style.rowRow}>
            {name} :
            <Expression path={this.props.path.push('entries').push(name)}>
              {value}
            </Expression>
          </div>
        );
      });

    return (
      <div className={style.row}>
        <div>Row {'{'}</div>
        <div className={style.rowList}>
          {children}
        </div>
        <div>{'}'}</div>
      </div>
    );
  }

  handleAdd(event) {
  }
}
