import React, { Component, PropTypes } from 'react';
import FlatButton from 'material-ui/lib/flat-button';

import Expression from '../../components/Expression';
import style from './style.scss';


export default class Variant extends Component {
  render() {
    const children = this.props.children.values
      .entrySeq()
      .toArray()
      .map(([name, value]) => {
        return (
          <div className={style.variantRow}>
            {name} :
            <Expression path={this.props.path.push('values').push(name)}>
              {value}
            </Expression>
          </div>
        );
      });

    return (
      <div className={style.variant}>
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
