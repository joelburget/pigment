import React, {Component, PropTypes} from 'react';
import {requireServerCss} from '../util';

import { Pair, Sigma } from './Expression/Pair';
import { Lambda, Pi } from './Expression/Lambda';
import Name from './Expression/Name';
import Hole from './Expression/Hole';

const styles = __CLIENT__ ?
  require('./Expression.scss') :
  requireServerCss(require.resolve('./Expression.scss'));


class App extends Component {
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


export default class Expression extends Component {
  // static propTypes = {
  //   expression: PropTypes.object.isRequired, // instanceOf(
  // };

  render() {
    const dispatch = {
      type: Type,
      "var": Name,
      hole: Hole,

      app: App,
      lam: Lambda,
      pi: Pi,

      sigma: Sigma,
      tuple: Pair, // TODO fix naming
    };

    // kind of tricky destructuring here -- this.props.children looks like:
    // {
    //   constructor: { renderName },
    //   children: ...,
    //   [other stuff]
    // }
    //
    // yep, children has children (it's an Expression (the class)). also we
    // pass in whatever other stuff is in this.props.children.
    const { renderName } = this.props.children.constructor;

    return (
      <div className={styles.expression}
           onMouseDown={::this.handleMouseDown}
           onMouseOver={::this.handleMouseOver}>
        {React.createElement(dispatch[renderName], this.props.children)}
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
