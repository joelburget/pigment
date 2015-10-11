import { List } from 'immutable';
import React, { Component, PropTypes } from 'react';

import Expression from '../../components/Expression';
import VariantData from './data';
import style from './style.scss';


export default class Variant extends Component {
  static propTypes = {
    children: PropTypes.instanceOf(VariantData).isRequired,
    path: PropTypes.instanceOf(List).isRequired,
  };

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
}
