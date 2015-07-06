import React from 'react';
import Radium from 'radium';

@Radium
export class MessagesLayout extends React.Component {
  render() {
    return <div>
      {this.props.children}
    </div>;
  }
}
