import { List } from 'immutable';
import React, {Component, PropTypes} from 'react';

import { AbsRef } from '../../theory/ref';
import { Var, VARIABLE, INTRO, ELIM } from '../../theory/tm';
import Expression from '../Expression';
import Autocomplete from '../Autocomplete';

import styles from './Hole.scss';


export default class Hole extends Component {
  state = {
    completions: {
      variables: [],
      intros: [],
      elims: [],
    },
  };

  static contextTypes = {
    findCompletions: PropTypes.func.isRequired,
    fillHole: PropTypes.func.isRequired,
  };

  render() {
    const { variables, intros, elims } = this.state.completions;
    const { path, children } = this.props
    const { type } = children;

    const completions = [].concat(
      variables.map(item => ({ category: VARIABLE, item })),
      intros.map(item => ({ category: INTRO, item })),
      elims.map(item => ({ category: ELIM, item }))
    );

    return (
      <div className={styles.hole}>
        <Autocomplete items={completions}
                      renderItem={::this.renderCompletion}
                      onChange={::this.handleAutocomplete}
                      onSelect={::this.handleSelect} />

        <div className={styles.ascription}>:</div>

        <Expression path={path.push('type')}>
          {type}
        </Expression>
      </div>
    );
  }

  renderCompletion({ category, item}, isHighlighted) {
    // TODO what is the right path here? tricky...
    const cls = isHighlighted ? styles.completionHl : '';
    return (
      <div className={styles.completion + ' ' + cls}>
        <div className={styles.completionCategory}>{category}</div>
        <div className={styles.completionName}>{item.name}</div>
        { item instanceof Var && (
            <div>
              <div>:</div>
              <Expression path={List()}>
                {item.type}
              </Expression>
            </div>
          )
        }
      </div>
    );
  }

  handleSelect(value, { category, item }) {
    this.context.fillHole(
      this.props.path,
      this.props.children.type,
      category,
      item
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
