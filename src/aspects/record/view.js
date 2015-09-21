import { Component, PropTypes } from 'react';
import FlatButton from 'material-ui/lib/flat-button';

import Expression from '../../components/Expression';
import style from './style.scss';


export default class Rec extends Component {
  render() {
    const children = this.props.children.values
      .entrySeq()
      .toArray()
      .map(([name, value]) => {
        return (
          <Expression path={this.props.path.push(name)}>
            {value}
          </Expression>
        );
      });

        // <FlatButton secondary label='add' onClick={::this.handleAdd} />

    return (
      <div className={style.rec}>
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
