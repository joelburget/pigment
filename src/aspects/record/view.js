import { List } from 'immutable';
import React, { Component, PropTypes } from 'react';

import RecData from './data';
import Expression from '../../components/Expression';
import style from './style.scss';


export default class Rec extends Component {
  static propTypes = {
    children: PropTypes.instanceOf(RecData).isRequired,
    path: PropTypes.instanceOf(List).isRequired,
  };

  render() {
    const children = this.props.children.values
      .entrySeq()
      .toArray()
      .map(([name, value]) => {
        return (
          <div className={style.recRow}>
            {name} :
            <Expression path={this.props.path.push('values').push(name)}>
              {value}
            </Expression>
          </div>
        );
      });

    return (
      <div>
        <div>Record {'{'}</div>
        <div className={style.recList}>
          {children}
        </div>
        <div>{'}'}</div>
      </div>
    );
  }
}
