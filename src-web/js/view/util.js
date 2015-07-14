import React from 'react';
import { Styles } from 'material-ui';

const ThemeManager = new Styles.ThemeManager();

export function getChildren(children) {
  let arr = [];
  React.Children.forEach(children, child => arr.push(child));
  return arr;
}

export function reactJoin(arr, glue) {
  let ret = [];
  arr.forEach(item => {
    ret.push(item);
    ret.push(glue);
  });
  ret.pop();
  return ret;
}

const muiTheme = ThemeManager.getCurrentTheme();

export const childContextTypes = {
  muiTheme: React.PropTypes.object
};

export function getChildContext() {
  return { muiTheme };
}

export class MuiComponent {

  getChildContext() {
    return { muiTheme };
  }

  static childContextTypes = {
    muiTheme: React.PropTypes.object
  };

}
