import React from 'react';
import {FontIcon, Styles} from 'material-ui';
import Radium from 'radium';

let ThemeManager = new Styles.ThemeManager();

let styles = {
  page: {},
  editView: {
    padding: '10px 10px 100px 10px'
  },
};

@Radium
export default class Page extends React.Component {
  render() {
      let [ editView, commandLine, messages ] = ['foo', 'bar', 'baz']; //this.props.children;

    return <div style={styles.page}>
      <div style={styles.editView}>{editView}</div>
      <div>{commandLine}</div>
      <div>{messages}</div>
    </div>;
  }
}
