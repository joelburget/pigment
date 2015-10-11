import React, { Component, PropTypes } from 'react';
import Rackt from 'react-autocomplete';

// TODO - should this be removed? I can't remember where styles come from
// import styles from './Autocomplete.scss';

// Synchronous loading component -- no "loading..."
export default class Autocomplete extends Component {
  static propTypes = {
    items: PropTypes.arrayOf(
      PropTypes.shape({
        category: PropTypes.string.isRequired,

        // really, an instance of Tm, which isn't a real class
        item: PropTypes.func.isRequired,
      })
    ),
    renderItem: PropTypes.func.isRequired,
    onSelect: PropTypes.func.isRequired,
    onChange: PropTypes.func.isRequired,
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
