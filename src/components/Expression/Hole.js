import { List } from 'immutable';
import React, {Component, PropTypes} from 'react';

import { AbsRef } from '../../theory/ref';
import Expression from '../Expression';
import styles from './Hole.scss';
import Autocomplete from '../Autocomplete';


export default class Hole extends Component {
  state = {
    completions: []
  };

  static contextTypes = {
    findCompletions: PropTypes.func.isRequired,
  };

  render() {
    const name = this.props.name || '_';

//         <input type='text'
//                placeholder={name}
//                onChange={::this.handleAutocomplete} />
        // <div className={styles.completions}>
        //   {this.state.completions.map(::this.renderCompletion)}
        // </div>

    return (
      <div className={styles.hole}>
        <Autocomplete items={this.state.completions}
                      renderItem={::this.renderCompletion}
                      onChange={::this.handleAutocomplete}
                      onSelect={() => {}} />
      </div>
    );
  }

  renderCompletion(binder) {
    // TODO what is the right path here? tricky...
    return (
      <div className={styles.completion}>
        <div>{binder.name}</div>
        <div>:</div>
        <Expression path={List()}>
          {binder.type}
        </Expression>
      </div>
    );
  }

  handleAutocomplete(value) {
    const hole = this.props.children;
    // Need to find values in scope
    // ... of the right type.
    //
    // This is the really important bit -- search is type-directed.
    const completions = this.context.findCompletions(
      hole.type,
      new AbsRef({ path: this.props.path }),
      value
    );

    this.setState({ completions });
  }
}
