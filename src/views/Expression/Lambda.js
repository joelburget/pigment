// lambda and pi

import React, {Component, PropTypes} from 'react';
import childJoin from '../childJoin';
import {requireServerCss} from '../../util';
import Name from './Name';
import Expression from '../Expression';
import { EVar } from '../../theory/tm';

const styles = __CLIENT__ ?
  require('./Lambda.scss') :
  requireServerCss(require.resolve('./Lambda.scss'));


export class Lambda extends Component {
  static propTypes = {
    names: PropTypes.array,
  };

  render() {
    // const { names, result } = this.props.children;

    const { name, body } = this.props.children[0]; // XXX hacky [0]
    const names = [ name ]; // XXX this is really all hacky
    const result = body.value;

    // XXX gross making this var here
    return (
      <div className={styles.lambda}>
        {names.map(name => <Name>{new EVar(name).children}</Name>)}
        <div>
          <span className={styles.arr}>&#8614;</span>
        </div>
        <Expression>{result}</Expression>
      </div>
    );
  }
}


export class Pi extends Component {
  render() {
    const pieces = this.props.children
      .map(x => <Expression>{x.value}</Expression>);

    return (
      <div className={styles.pi}>
        {childJoin(pieces, <span>&rarr;</span>)}
      </div>
    );
  }
}
