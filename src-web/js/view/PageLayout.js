import React from 'react';
import {FontIcon, Styles} from 'material-ui';
import Radium from 'radium';

let ThemeManager = new Styles.ThemeManager();

let styles = {
  page: {
    display: 'flex',
    flexDirection: 'column',
  },
  commandLine: {
    flex: '1'
  }
};

@Radium
export default class PageLayout extends React.Component {
  render() {
    let [editView, commandLine, messages] = this.props.children;

    return <div style={styles.page}>
      <div>{editView}</div>
      <div styles={[styles.commandLine]}>{commandLine}</div>
      <div>{messages}</div>
    </div>;
  }

  getChildContext() {
    return {
      muiTheme: ThemeManager.getCurrentTheme()
    };
  }

}

PageLayout.childContextTypes = {
  muiTheme: React.PropTypes.object
};
