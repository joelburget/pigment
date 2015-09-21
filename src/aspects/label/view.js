import { Component, PropTypes } from 'react';


export default class Label extends Component {
  render() {
    return (
      <div>
        {this.props.children.name}
      </div>
    );
  }
}
