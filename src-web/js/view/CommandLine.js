import React from 'react';
import { FontIcon, Styles, List, ListItem, Card, CardTitle, CardText, Paper, TextField } from 'material-ui';
import * as MaterialUI from 'material-ui';
import Radium from 'radium';
import { TransitionSpring } from 'react-motion';

import { getChildren, reactJoin, MuiComponent } from './util';

// material icon library
// https://www.google.com/design/icons/

const theme = MaterialUI.Styles.ThemeManager().getCurrentTheme();
const Colors = MaterialUI.Styles.Colors;

const positionAndSize = {
  position: 'absolute',
  left: 30,
  bottom: 75,
  height: 300,
  width: 500,
};

let styles = {

  commandLine: {
    position: 'fixed',
    bottom: 0,
    width: '100%',
    backgroundColor: 'white',
    minHeight: 50,
  },

  completions: {
    display: 'flex',
    flexDirection: 'row',

    padding: 0,
    ...positionAndSize,
  },

  autocompleteWelcome: {
    ...positionAndSize
  },

  tacticLayout: {
  },

  paramLayout: {
    overflow: 'scroll',
    ...positionAndSize,
  },

  tacticName: {
    color: 'white',
    backgroundColor: theme.palette.accent2Color,
    padding: theme.spacing.desktopGutterLess,
  },

  tacticFormatLayout: {
  },

};

@Radium
export class CommandLine extends MuiComponent {

  render() {
    let [ textArea, completions ] = this.props.children;

    // HACK!
    textArea.props.style = {
      border: '0',
      resize: 'none',
      outline: 'none',
      width: '100%',
      height: '100%',
      margin: 10,
      fontSize: 18,
      fontFamily: 'monospace',
    };

    // <FontIcon className="chevron-right" />
    return <Paper style={styles.commandLine}>
      {textArea}
      {completions}
    </Paper>
  }
}

const ON = 'ON';
const ABOVE = 'ABOVE';
const BELOW = 'BELOW';
const SIDE = 'SIDE';


// @Radium
export class TacticCompletion extends MuiComponent {

  render() {
    const [ preview, above, selected, below ] = getChildren(this.props.children);
    const { name } = this.props;

    // Cache components here because react-motion won't abide them in its
    // config. We need to keep around multiple components at a time, not just
    // the currently rendered one.
    if (!this._cache) {
      this._cache = {};
    }

    this._cache[name] = preview;

    const aboveListChildren = React.Children.map(above, child => (
      <ListItem>{child}</ListItem>
    ), this);

    const belowListChildren = React.Children.map(below, child => (
      <ListItem>{child}</ListItem>
    ), this);

    const border = '1px solid #ddd';

    const aboveList = (
      <div style={{borderRight: border, marginTop: 0}}>
        {aboveListChildren}
      </div>
    );

    const belowList = (
      <div style={{borderRight: border, height: '100%'}}>
        {belowListChildren}
      </div>
    );

    return (
      <Paper style={styles.completions}>
        <List style={{width: 150}}>
          {aboveList}
          <div style={{borderTop: border, borderBottom: border}}><ListItem>{selected}</ListItem></div>
          {belowList}
        </List>

        <div style={{position: 'relative', overflow: 'hidden', width: '100%', height: '100%'}}>
          <TransitionSpring
            endValue={this.getEndValue}
            willEnter={this.willEnter}
            willLeave={this.willLeave}>
            {currentValue => Object.keys(currentValue).map(key => (
              <div key={key} style={{ position: 'absolute', top: currentValue[key].top.val }}>
                {this._cache[key]}
              </div>
            ))}
          </TransitionSpring>
        </div>
      </Paper>
    );
  }

  getEndValue = () => {
    const { name } = this.props;

    return {
      [name]: {
        top: { val: 0 },
      }
    };
  };

  willEnter = (key, endValue, currentValue, currentSpeed) => {
    return {
      top: { val: -400 },
    };
  };

  willLeave = (key, endValue, currentValue, currentSpeed) => {
    return {
      top: { val: 400 },
    };
  };

  // Find the direction of the queried name from the currentName
  // ON:
  getDirection(queriedName, currentName, list) {
    const queriedIx = list.indexOf(queriedName);
    const currentIx = list.indexOf(currentName);

    if (queriedIx === -1) {
      return SIDE;
    } else if (queriedIx === currentIx) {
      return ON;
    } else if (queriedIx < currentIx) {
      return ABOVE;
    } else { // queriedIx > currentIx
      return BELOW;
    }
  }

}


export class AutocompleteLayout extends MuiComponent {
  render () {
    return (
      <div>
        {this.props.children}
      </div>
    );
  }
}

export class AutocompleteWelcome extends MuiComponent {
  render () {
    return (
      <Paper style={styles.autocompleteWelcome}>
        <p style={{margin: 20}}>Get started by writing the name of a tactic.</p>
        <p style={{margin: 20}}>A few useful ones to get you started:</p>
        <List>
          <ListItem><code>let</code></ListItem>
          <ListItem><code>data</code></ListItem>
          <ListItem><code>define</code></ListItem>
        </List>
      </Paper>
    );
  }
}


@Radium
export class TacticLayout extends MuiComponent {
  render () {
    const { name, children: [ desc, format ] } = this.props;

    return (
      <div style={styles.tacticLayout}>
        <CardTitle title={name} />
        <CardText>
          {format}
        </CardText>
      </div>
    );
    // return <div style={}>
    //   <div style={styles.tacticName}>{this.props.name}</div>
    //   <div>{this.props.children}</div>
    // </div>;
  }
}


// @Radium
export class ParamLayout extends MuiComponent {
  render () {
    const { name, children } = this.props;
    const [ desc, format ] = getChildren(children);

    return (
      <Card style={styles.paramLayout}>
        <CardTitle title={name} subtitle={desc} />
        <CardText>
          <div>
            {format}
          </div>
        </CardText>
      </Card>
    );
  }
}


@Radium
export class TacticFormatLayout extends React.Component {
  render () {
    const { tag, children } = this.props;

    return <div style={styles.tacticFormatLayout}>
      {TacticFormatLayout.tags[tag](getChildren(children))}
    </div>;
  }
}

const layoutStyle = {
  fontFamily: 'monospace',
  display: 'inline-block',
  marginTop: 5,
  marginBottom: 5,
};

const userItemStyle = {
  backgroundColor: Colors.yellow100,
  ...layoutStyle,
};

const kwStyle = {
  backgroundColor: Colors.purple100,
  ...layoutStyle,
};

const sequenceStyle = {
  borderLeft: '2px solid #ddd',
  paddingLeft: 8,
  display: 'flex',
};

TacticFormatLayout.tags = {
  name: name => (
    <div style={userItemStyle}>
      {name}
    </div>
  ),
  keyword: kw => (
    <div>
      &nbsp;
      <div style={kwStyle}>
        {kw}
      </div>
      &nbsp;
    </div>
  ),
  inarg: ([text, explain]) => (
    <div>
      <div style={userItemStyle}>
        {text}
      </div>
      : {explain}
    </div>
  ),
  exarg: ([text, explain]) => (
    <div>
      <div style={userItemStyle}>
        {text}
      </div>
      : {explain}
    </div>
  ),
  scheme: ([name, explain]) => (
    <div>
      <div style={userItemStyle}>
        {name}
      </div>
      : {explain}
    </div>
  ),
  alternative: ([l, r]) => (
    <div>
      Either
      {l}
      or
      {r}
    </div>
  ),
  option: fmt => (
    <div>
      Optionally
      <div style={userItemStyle}>
        {fmt}?
      </div>
    </div>
  ),
  repeatzero: x => x,
  blocksequence: children => (
    <div style={{...sequenceStyle, flexDirection: 'column'}}>
      {children}
    </div>
  ),
  inlinesequence: children => (
    <div style={{...sequenceStyle, flexDirection: 'row'}}>
      {children}
    </div>
  ),
  bracketed: x => (
    <div>
      [{x}]
    </div>
  ),
  sep: ([fmt, kwd]) => (
    <div>
      Repeat
      {fmt}
      ... separated by <span style={kwStyle}>{kwd}</span>
    </div>
  ),
}
