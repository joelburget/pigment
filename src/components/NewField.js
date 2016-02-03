// @flow
import React, { Component } from 'react';

import { NEW_FIELD } from '../messages';

type ControlsProps = {
  signal: (sig: NewFieldSignal) => void;
};


export default class NewFieldInput
  extends Component<{}, ControlsProps, {nameInput: string}> {

  state = {
    nameInput: '',
  };

  handleChange(nameInput) {
    this.setState({ nameInput });
  }

  handleKeyPress(event) {
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
