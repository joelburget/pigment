// @flow
import React, { Component } from 'react';

import {
  NEW_FIELD,
  NewFieldSignal
} from '../messages';

type ControlsProps = {
  signal: (sig: NewFieldSignal) => void;
};

type State = {
  nameInput: string;
};


export default class NewFieldInput
  extends Component<{}, ControlsProps, State> {

  state: State = {
    nameInput: '',
  };

  handleChange(nameInput: string) {
    this.setState({ nameInput });
  }

  handleKeyPress(event: SyntheticKeyboardEvent) {
    if (event.key === 'Enter') {
      this.props.signal({
        action: NEW_FIELD,
        name: this.state.nameInput,
      });
      this.setState({ nameInput: '' });
    }
  }

  render(): Element {
    const { nameInput } = this.state;

    const valueLink = {
      value: nameInput,
      requestChange: value => this.handleChange(value),
    };

    return (
      <div style={styles.control}>
        <input
          type='text'
          valueLink={valueLink}
          onKeyPress={event => this.handleKeyPress(event)}
        />
      </div>
    );
  }
}


const styles = {
  control: {
    marginTop: 20,
  }
};
