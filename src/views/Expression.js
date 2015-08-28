import React, {Component, PropTypes} from 'react';
import type { List } from 'immutable';
import {requireServerCss} from '../util';

import Name from './Expression/Name';
import Hole from './Expression/Hole';
import { Lambda, Arr } from './Expression/Lambda';
// import { Label, Rec, RowKind, Row, SelectRow, ExtendRow, RestrictRow } from

const styles = __CLIENT__ ?
  require('./Expression.scss') :
  requireServerCss(require.resolve('./Expression.scss'));


class Application extends Component {
  render() {
    return (
      <div>
        {this.props.children}
      </div>
    );
  }
}


class Type extends Component {
  render() {
    return '*';
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

  render() {
    const dispatch = {
      type: Type,
      "var": Name,
      hole: Hole,

      app: Application,
      lam: Lambda,
      arr: Arr,

      // label: Label,
      // rec: Rec,
      // rowkind: RowKind,
      row: Row,
      // selectrow: SelectRow,
      // extendrow: ExtendRow,
      // restrictrow: RestrictRow,
    };

    // gross -- we're grabbing the name from Immutable.Record
    const name = this.props.children._name;
    const props = {
      children: this.props.children,
      path: this.props.path,
    };

    return (
      <div className={styles.expression}
           onMouseDown={::this.handleMouseDown}
           onMouseOver={::this.handleMouseOver}>
        {React.createElement(dispatch[name], props)}
      </div>
    );
  }

  handleMouseDown() {
    // TODO figure out how to find path to this expression (same with enter)
    this.props.expressionMouseDepress(this);
  }

  handleMouseOver() {
    this.props.expressionMouseEnter(this);
  }
}
