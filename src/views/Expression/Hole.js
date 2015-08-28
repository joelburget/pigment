import React, {Component, PropTypes} from 'react';
import {requireServerCss} from '../../util';


const styles = __CLIENT__ ?
  require('./Hole.scss') :
  requireServerCss(require.resolve('./Hole.scss'));


export default class Hole extends Component {
  render() {
    const name = this.props.name || '_';

    return (
      <span className={styles.hole}>
        <input type='text'
               placeholder={name}
               onChange={::this.autocomplete} />
      </span>
    );
  }

  autocomplete() {
  }
}
