import React from 'react';
import {FontIcon, Styles} from 'material-ui';
import Radium from 'radium';

// material icon library
// https://www.google.com/design/icons/

let styles = {
  commandLine: {
    display: 'flex'
  },
  completions: {
    flex: '1'
  },
  miniHelp: {
  }
};

@Radium
export class CommandLine extends React.Component {

  render() {
    let [textArea, completions] = this.props.children;

    // <FontIcon className="chevron-right" />
    return <div style={styles.commandLine}>
      <i className='material-icons'>chevron_right</i>
      {textArea}
      {completions}
    </div>
  }
}


@Radium
export class TacticCompletion extends React.Component {
  render() {
    let [above, selected, below] = this.props.children;
    return <div style={styles.completions}>
      {above}
      <i>{selected}</i>
      {below}
    </div>;
  }

  /*
  innerAutocomplete({early, focus, late}) {
    let early_ = early.map(this.describe);

    let focus_ = <div className='autocomplete-focus'>
      <div>{focus.name}</div>
      <div><Minihelp tactic={focus} /></div>
    </div>;

    let late_ = late.map(this.describe);

    return [].concat(early_, [focus], late_);
  }

  describeTactic(tactic) {
    return <div>
      {tactic.name}
    </div>;
  }
  */
}

class MiniHelp extends React.Component {
  render() {
    let {tactic} = this.props;
  }
}

export class AutocompleteLayout extends React.Component {
  render () {
    return <div>
      {this.props.children}
    </div>;
  }
}
