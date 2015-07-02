import React from 'react';
import View from 'react-flexbox'

export default class PageLayout extends React.Component {
  render() {
    let [editView, commandLine] = this.props.children;

    return <View row>
      <View>{editView}</View>
      <View>{commandLine}</View>
    </View>;
  }
}
