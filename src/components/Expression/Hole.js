import { List } from 'immutable';
import React, {Component, PropTypes} from 'react';

import { FreeVar } from '../../theory/ref';
import { Var, Hole as HoleData, VARIABLE, INTRO } from '../../theory/tm';
import Expression from '../Expression';
import Autocomplete from '../Autocomplete';

import styles from './Hole.scss';


export default class Hole extends Component {
  static propTypes = {
    children: PropTypes.instanceOf(HoleData).isRequired,
    path: PropTypes.instanceOf(List).isRequired,
  };

  static contextTypes = {
    findCompletions: PropTypes.func.isRequired,
    fillHole: PropTypes.func.isRequired,
  };

  state = {
    completions: {
      variables: [],
      intros: [],
      elims: [],
    },
  };

  componentWillMount() {
    const completions = this.fetchCompletions('');
    this.setState({ completions });
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
    const completions = this.fetchCompletions(value);
    this.setState({ completions });
  }

  fetchCompletions(value) {
    const { children: hole, path } = this.props;
    // Need to find values in scope
    // ... of the right type.
    //
    // This is the really important bit -- search is type-directed.
    return this.context.findCompletions(
      hole.type,
      new FreeVar({ path }),
      value
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

  render() {
    const { variables, intros } = this.state.completions;

    const completions = [].concat(
      variables.map(item => ({ category: VARIABLE, item })),
      intros.map(item => ({ category: INTRO, item }))
      // elims.map(item => ({ category: ELIM, item }))
    );

    return (
      <div className={styles.hole}>
        <Autocomplete items={completions}
                      renderItem={::this.renderCompletion}
                      onChange={::this.handleAutocomplete}
                      onSelect={::this.handleSelect} />
      </div>
    );
  }
}
