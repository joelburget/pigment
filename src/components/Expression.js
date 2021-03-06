import { List } from 'immutable';
import React, { Component, PropTypes } from 'react';

import Var from './Expression/Name';
import Hole from './Expression/Hole';
import { Arrow, Lambda } from '../aspects/lambda/view';
import Application from '../aspects/application/view';
import Label from '../aspects/label/view';
import Row from '../aspects/row/view';
import Rec from '../aspects/record/view';
import Variant from '../aspects/variant/view';

import styles from './Expression.scss';


function Type() {
  return (
    <span>*</span>
  );
}


function Conflict() {
  return (
    <div className={styles.conflict}>
      {this.props.children}
    </div>
  );
}


export function expr(value, path, chunk) {
  const accessor = chunk instanceof Array ?
    chunk :
    [chunk];

  return (
    <Expression path={path.concat(chunk)}>
      {value.getIn(accessor)}
    </Expression>
  );
}


export default class Expression extends Component {
  static propTypes = {
    path: PropTypes.instanceOf(List).isRequired,
    children: PropTypes.object.isRequired, // Tm
  };

  static contextTypes = {
    isPathHighlighted: PropTypes.func.isRequired,
    expressionMouseClick: PropTypes.func.isRequired,
  };

  handleClick(event) {
    this.context.expressionMouseClick(this.props.path);
    event.stopPropagation();
  }

//   handleMouseDown(event) {
//     this.context.expressionMouseDepress(this.props.path);
//     event.stopPropagation();
//   }

//   handleMouseOver(event) {
//     this.context.expressionMouseOver(this.props.path);
//     event.stopPropagation();
//   }

  render() {
    const dispatch = {
      Type,
      Conflict,
      Var,
      Hole,

      App: Application,
      Lam: Lambda,
      Arrow: Arrow,

      Label,
      Rec,
      // rowkind: RowKind,
      Row,
      Variant,

      // selectrow: SelectRow,
      // extendrow: ExtendRow,
      // restrictrow: RestrictRow,
    };

    const { path, children } = this.props;
    const name = children.constructor.name;

    if (dispatch[name] == null) {
      debugger; // eslint-disable-line no-debugger
    }

    const isHighlighted = this.context.isPathHighlighted(path);
    const highlightedStyle = isHighlighted ? styles.highlighted : '';

    return (
      <div className={styles.expression + ' ' + highlightedStyle}
           onClick={::this.handleClick}>
        {React.createElement(dispatch[name], { path, children })}
      </div>
    );
  }
}
