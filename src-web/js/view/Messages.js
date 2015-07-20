import React from 'react';
import Radium from 'radium';
import * as MaterialUI from 'material-ui';

let { Styles: { Colors } } = MaterialUI;

const styles = {
  messages: {
    margin: 10,
  },
};

const messagePart = {
  padding: 5,
  color: 'white',
  fontWeight: 400,
}

const colors = {
  Green: {
    backgroundColor: Colors.lightGreen900,
    ...messagePart,
  },
  Orange: {
    backgroundColor: Colors.orange900,
    ...messagePart,
  },
  Red: {
    backgroundColor: Colors.red900,
    ...messagePart,
  },
};

@Radium
export class MessagesLayout extends React.Component {
  render() {
    return (
      <div style={styles.messages}>
        {this.props.children}
      </div>
    );
  }
}

@Radium
export class MessageLayout extends React.Component {
  render() {
    return (
      <div>
        {this.props.children}
      </div>
    );
  }
}

@Radium
export class MessagePartLayout extends React.Component {
  render() {
    return (
      <div style={colors[this.props.severity]}>
        {this.props.text}
      </div>
    );
  }

}
