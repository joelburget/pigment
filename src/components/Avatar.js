import React, { Component, PropTypes } from 'react';

export default class Avatar extends Component {
  static propTypes = {
    size: PropTypes.number,
    round: PropTypes.bool,
    // fbId: PropTypes.string.isRequired,
  };

  render() {
    const size = this.props.size || 50;
    const width = size;
    const height = size;
    const style = {
      borderRadius: this.props.round ? size : 0,
      marginTop: -10,
      marginRight: 20,
      boxSizing: 'border-box',
      border: '1px solid #ddd',
    };
    // const fbId = this.props.fbId;
    const src = 'http://joelburget.com/media/img/profile.jpg';

    return (
      <img src={src}
           width={width}
           height={height}
           style={style} />
    );
  }
}
