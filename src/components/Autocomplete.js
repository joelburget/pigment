import React, { Component, PropTypes } from 'react';
import Rackt from 'react-autocomplete';

import styles from './Autocomplete.scss';

// Synchronous loading component -- no "loading..."
export default class Autocomplete extends Component {
  static propTypes = {
    items: PropTypes.arrayOf(
      PropTypes.shape({
        category: PropTypes.string.isRequired,
        item: PropTypes.object.isRequired,
      })
    ),
    renderItem: PropTypes.func.isRequired,
    onSelect: PropTypes.func.isRequired,
  };

  render() {
    return (
      <Rackt
        items={this.props.items}
        getItemValue={item => item.item.name}
        onChange={(event, value) => this.props.onChange(value)}
        onSelect={this.props.onSelect}
        renderItem={this.props.renderItem} />
    );
  }
}
