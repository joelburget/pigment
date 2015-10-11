import React, { Component, PropTypes } from 'react';

import LabelData from './data';


export default class Label extends Component {
  static propTypes = {
    children: PropTypes.instanceOf(LabelData).isRequired,
  };

  render() {
    return (
      <div>
        {this.props.children.name}
      </div>
    );
  }
}
