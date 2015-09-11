import React, { Component, PropTypes } from 'react';
import Rackt from 'react-autocomplete';

import styles from './Autocomplete.scss';

// Synchronous loading component -- no "loading..."
export default class Autocomplete extends Component {
  static propTypes = {
    items: PropTypes.arrayOf(PropTypes.object).isRequired,
    renderItem: PropTypes.func.isRequired,
    onSelect: PropTypes.func.isRequired,
  };

//         onChange={(event, value) => {
//           this.props.getUpdated(value);
//           this.setState({loading: true})
//           fakeRequest(value, (items) => {
//             this.setState({ unitedStates: items, loading: false })
//           })
//         }}
        // renderItem={(item, isHighlighted) => (
        //   <div
        //     style={isHighlighted ? styles.highlightedItem : styles.item}
        //     key={item.abbr}
        //     id={item.abbr}
        //   >{item.name}</div>
        // )}

  render() {
    return (
      <Rackt
        items={this.props.items}
        getItemValue={item => item.name}
        onChange={(event, value) => this.props.onChange(value)}
        onSelect={this.props.onSelect}
        renderItem={this.props.renderItem}
        renderMenu={(items, value, style) => (
          <div style={{...styles.menu, ...style}}>
            { items.length === 0 ? (
              <div style={{padding: 6}}>No matches for {value}</div>
            ) : items}
          </div>
        )}
      />
    );
  }
}
