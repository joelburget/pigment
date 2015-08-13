import React, {Component, PropTypes} from 'react';
import {requireServerCss} from '../util';

import { Pair, Sigma } from './Expression/Pair';
import { Lambda, Pi } from './Expression/Lambda';
import Name from './Expression/Name';

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


class Hole extends Component {
  render() {
    const name = this.props.name || '_';

    return (
      <span className={styles.hole}>
        {name}
      </span>
    );
  }
}


export default class Expression extends Component {
  // static propTypes = {
  //   expression: PropTypes.object.isRequired, // instanceOf(
  // };

  render() {
    const dispatch = {
      app: App,
      type: Type,
      "var": Name,
      lam: Lambda,
      pi: Pi,
      tuple: Pair, // TODO fix naming
      sigma: Sigma,
      hole: Hole,
    };

    // kind of tricky destructuring here -- this.props.children looks like:
    // {
    //   type: ...
    //   children: ...
    //   [other stuff]
    // }
    //
    // yep, children has children. also we pass type in as props (not
    // important). also we pass in whatever other stuff is in
    // this.props.children.
    const { type } = this.props.children;


    return (
      <div className={styles.expression}>
        {React.createElement(dispatch[type], this.props.children)}
      </div>
    );
  }
}