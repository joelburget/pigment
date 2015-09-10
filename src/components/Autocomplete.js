import React, { Component, PropTypes } from 'react';
import Rackt from 'autocomplete';

// Synchronous loading component -- no "loading..."
export default class Autocomplete extends Component {
  static propTypes = {
    items: PropTypes.arrayOf(PropTypes.object).isRequired,
    onSelect: PropTypes.func.isRequired,
  };

  render() {
    return (
      <Autocomplete
        items={this.state.items}
        getItemValue={(item) => item.name}
        onSelect={this.props.onSelect}
        onChange={(event, value) => {
          this.props.getUpdated(value);
          this.setState({loading: true})
          fakeRequest(value, (items) => {
            this.setState({ unitedStates: items, loading: false })
          })
        }}
        renderItem={(item, isHighlighted) => (
          <div
            style={isHighlighted ? styles.highlightedItem : styles.item}
            key={item.abbr}
            id={item.abbr}
          >{item.name}</div>
        )}
        renderMenu={(items, value, style) => (
          <div style={{...styles.menu, ...style}}>
            {value === '' ? (
              <div style={{padding: 6}}>Type of the name of a United State</div>
            ) : items.length === 0 ? (
              <div style={{padding: 6}}>No matches for {value}</div>
            ) : this.renderItems(items)}
          </div>
        )}
      />
    );
  }
}
