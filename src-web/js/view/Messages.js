import React from 'react';
import Radium from 'radium';
import * as MaterialUI from 'material-ui';

let { Styles: { Colors } } = MaterialUI;

var styles = {
  green: { color: Colors.green500 },
  orange: { color: Colors.orange500 },
  red: { color: Colors.red500 },
}

@Radium
export class MessagesLayout extends React.Component {
  render() {
    return <div>
      {this.props.children}
    </div>;
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
      <div style={this.severity(this.props.severity)}>
        {this.props.message}
      </div>
    );
  }

  severity(str) {
    const selector = {
      Green: styles.green,
      Orange: styles.orange,
      Red: styles.red,
    }
  }
}
