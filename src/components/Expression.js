import React, { Component, PropTypes } from 'react';
import type { List } from 'immutable';

import Var from './Expression/Name';
import Hole from './Expression/Hole';
import Lambda from '../aspects/lambda/view';
import Application from '../aspects/application/view';
// import { Label, Rec, RowKind, Row, SelectRow, ExtendRow, RestrictRow } from

import styles from './Expression.scss';


class Type extends Component {
  render() {
    return (
      <span>*</span>
    );
  }
}


class Row extends Component {
  render() {
    return (
      <div>
        ROW
      </div>
    );
  }
}


export default class Expression extends Component {
  // propTypes = {
  //   path: PropTypes.instanceOf(List<string>)
  // };

  static contextTypes = {
    isPathHighlighted: PropTypes.func.isRequired,
    expressionMouseClick: PropTypes.func.isRequired,
  };

  render() {
    const dispatch = {
      Type: Type,
      "Var": Var,
      Hole: Hole,

      App: Application,
      Lam: Lambda,
      // Arr: Arr,

      // label: Label,
      // rec: Rec,
      // rowkind: RowKind,
      Row: Row,
      // selectrow: SelectRow,
      // extendrow: ExtendRow,
      // restrictrow: RestrictRow,
    };

    // gross -- grabbing the name in this way
    if (this.props.children == undefined) {
      debugger;
    }
    const name = this.props.children.constructor.name;

    const props = {
      children: this.props.children,
      path: this.props.path,
    };

    const isHighlighted = this.context.isPathHighlighted(this.props.path);
    const highlightedStyle = isHighlighted ? styles.highlighted : '';

    return (
      <div className={styles.expression + ' ' + highlightedStyle}
           onClick={::this.handleClick}>
        {React.createElement(dispatch[name], props)}
      </div>
    );
  }

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
}
