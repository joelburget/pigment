import React from 'react';
import Radium from 'radium';
import * as MaterialUI from 'material-ui';
import { getChildren, reactJoin } from './util';

let { Styles: { Colors } } = MaterialUI;
let theme = MaterialUI.Styles.ThemeManager().getCurrentTheme();

const headerStyle = {
  //borderLeft: '4px solid gray',
  borderBottom: '2px dashed #aaa',
  padding: '0 0 10px',
};

const blockStyle = color => ({
    borderLeft: `4px solid ${color}`,
    borderTop: `1px solid ${Colors.grey200}`,
    borderBottom: `1px solid ${Colors.grey200}`,
    margin: '10px 0',
    padding: '10px 0 10px 10px',
});

let styles = {
  refLayout: {
    display: 'flex',
    flexDirection: 'row',
  },

  devLayout: {
    marginTop: 10,
    display: 'flex',
    flexDirection: 'column',
    // ...blockStyle(Colors.deepPurple200),
  },

  parameterLayout: {
    marginTop: 10,
    // ...blockStyle(Colors.orange500)
  },

  moduleLayout: {...blockStyle(Colors.cyan500)},

  entryEntityLayout: {...blockStyle(Colors.red200)},

  definitionLayout: {...blockStyle(Colors.amber500)},

  purposeLet: {
    color: Colors.indigo900
  },
  purposeProg: {
    color: Colors.indigo900, display: 'flex'
  },

  entriesLayout: {
    marginTop: 10,
  },

  entriesLayoutHeader: {
    fontWeight: 400,
  },

  entryHeaderLayout: {...headerStyle},
  moduleHeaderLayout: {...headerStyle},
  nameExplainLayout: {},

  suspendedStyle: { color: Colors.blue900 },
  unstableStyle: { color: Colors.deepOrange500 },
  stableStyle: { color: Colors.green700 },

  dInTmRN: {
    backgroundColor: Colors.blue100,
    margin: '0 2px',
    padding: '0 4px'
  },

  name: {
    display: 'flex',
    backgroundColor: Colors.orange100,
    margin: '0 2px',
    padding: '0 4px'
  },

  scheme: {
    backgroundColor: Colors.teal100,
    display: 'flex',
    flexDirection: 'row',
    padding: 4,
    border: '4px solid white'
  },

  pair: {
    display: 'inline-flex',
    flexDirection: 'row',
    borderStyle: 'solid',
    borderColor: Colors.teal100,
    borderWidth: '1px 1px 1px 4px',
    margin: '2px',
    alignItems: 'center',
  },

  err: { backgroundColor: Colors.orange700 },
};

@Radium
export class RefLayout extends React.Component {
  render () {
    const [name, ty] = getChildren(this.props.children);

    return <div style={styles.refLayout}>
      defining {name} as {ty}
    </div>;
  }
}

@Radium
export class ParameterLayout extends React.Component {
  render () {
    const [ tag ] = getChildren(this.props.children);

    return <div style={styles.parameterLayout}>
      (this definition is a {this.getParamDescription(tag)})
    </div>;
  }

  getParamDescription(tag) {
    switch (tag) {
      case 'ParamLam':
        return 'lambda';
      case 'ParamAll':
        return 'for all';
      case 'ParamPi':
        return 'pi';
    }
  }
}

const bracketedBorder = '1px solid #bbb';

class Bracketed extends React.Component {
  render() {
    return (
      <div style={{borderLeft: bracketedBorder, display: 'flex', flexDirection: 'column'}}>
        <div style={{display: 'flex', flexDirection: 'row'}}>
          <div style={{width: 20, height: '50%', borderTop: bracketedBorder, borderLeft: bracketedBorder}} />
          <div>{this.props.title}</div>
        </div>
        <div>
          {this.props.children}
        </div>
        <div style={{width: 20, height: '50%', borderBottom: bracketedBorder, borderLeft: bracketedBorder}} />
      </div>
    );
  }
}

@Radium
export class DefinitionLayout extends React.Component {
  render () {
    const [ dev, kindTag, kindInfo ] = getChildren(this.props.children);

    return dev;
    // return (
    //   <div style={styles.definitionLayout}>
    //     <PurposeLayout purpose={kindTag} info={kindInfo} />
    //     {dev}
    //   </div>
    // );
  }
}

@Radium
export class EntryModuleLayout extends React.Component {
  render () {
    const [header, dev] = getChildren(this.props.children);

    return <div style={styles.entryModuleLayout}>
      {header}
      {dev}
    </div>;
  }
}

@Radium
export class DevLayout extends React.Component {
  render () {
    const [suspendState, entries] = getChildren(this.props.children);

    return <div style={styles.devLayout}>
      {this.showSuspend(suspendState)}
      {entries}
    </div>;
  }

  showSuspend(str) {
    switch(str) {
      case 'SuspendNone':
        return (
          <div style={styles.suspendedStyle}>
            Not Suspended
          </div>
        );
      case 'SuspendUnstable':
        return (
          <div style={styles.unstableStyle}>
            Unstable
          </div>
        );
      case 'SuspendStable':
        return (
          <div style={styles.stableStyle}>
            Stable
          </div>
        );
    }
  }
}

@Radium
export class EntriesLayout extends React.Component {
  render () {
    const entries = getChildren(this.props.children);

    return <div style={styles.entriesLayout}>
      <div style={styles.entriesLayoutHeader}>ENTRIES</div>
      {entries}
    </div>;
  }
}

@Radium
export class EntryHeaderLayout extends React.Component {
  render () {
    const [ref, metadata, ty] = getChildren(this.props.children);

    return <div style={styles.entryHeaderLayout}>
      {ref}
    </div>;
  }
}

@Radium
export class ModuleHeaderLayout extends React.Component {
  render () {
    const [name, purpose, metadata] = getChildren(this.props.children);

    return <div style={styles.moduleHeaderLayout}>
      {name}
      <PurposeLayout purpose={purpose} />
    </div>;
  }
}

@Radium
export class PurposeLayout extends React.Component {
  render() {
    switch(this.props.purpose) {
      case "LETG":
        return (
          <div style={styles.purposeLet}>
            defining
          </div>
        );
      case "PROGERR":
        return (
          <div style={styles.err}>
            ERROR distilling scheme
          </div>
        );
      case "PROG":
        return (
          <div style={styles.purposeProg}>
            programming scheme {this.props.info}
          </div>
        );
    }
  }
}

@Radium
export class NameExplainLayout extends React.Component {
  render () {
    const [name, purpose, metadata] = getChildren(this.props.children);

    return <div style={styles.nameExplainLayout}>
      {name}
      {purpose}
      {metadata}
    </div>;
  }
}

@Radium
export class NameLayout extends React.Component {
  render () {
    const pieces = getChildren(this.props.children);

    return <div style={styles.name}>
      {reactJoin(pieces, ".")}
    </div>;
  }
}

@Radium
export class NamePieceLayout extends React.Component {
  render () {
    const { str, n } = this.props;

    const sub = n === '0' ? "" : <sub style={{verticalAlign: 'sub'}}>{n}</sub>;

    return <div style={{}}>
      {str}
      {sub}
    </div>;
  }
}

@Radium
export class EntryEntityLayout extends React.Component {
  render () {
    const [header, entity] = getChildren(this.props.children);

    return <div style={styles.entryEntityLayout}>
      {header}
      {entity}
    </div>;
  }
}

const flexRow = {
  display: 'flex',
  flexDirection: 'row'
};

const sigmaTags = {

  dunit: () => "*",

  bind: ([s, x, t]) => (
    <div style={flexRow}>
      ( {s} , \ {x} -> {t} )
    </div>
  ),

  const: ([s, t]) => (
    <div style={flexRow}>
      ({s}, {t})
    </div>
  ),

  other: ([s, t]) => (
    <div style={flexRow}>
      Other({s}, {t})
    </div>
  ),

}

@Radium
export class SigmaLayout extends React.Component {
  render() {
    return (
      <div style={{}}>
        {sigmaTags[this.props.tag](this.props.children)}
      </div>
    );
  }
}

@Radium
export class SchemeLayout extends React.Component {
  render() {
    return (
      <div style={styles.scheme}>
        {this.props.tag}
        {this.props.children}
      </div>
    );
  }
}

@Radium
export class PairLayout extends React.Component {
  render() {
    return (
      <div style={styles.pair}>
        &lang;{reactJoin(getChildren(this.props.children), ",")}&rang;
      </div>
    );
  }
}

@Radium
export class DHeadLayout extends React.Component {
  render() {
    return (
      <div style={{}}>
        {this.props.children}
      </div>
    );
  }
}

DHeadLayout.tags = {
  // param:
  // annotation:
  // embedding:
};


@Radium
export class CanLayout extends React.Component {
  render() {
    return (
      <div style={{}}>
        {this.selectTag(this.props.tag, getChildren(this.props.children))}
      </div>
    );
  }

  selectTag(tagName, children) {
    return this.constructor.tags[tagName](children);
  }
}

CanLayout.tags = {
  set: () => "SET",
  pi: p => p,
  con: tm => <div>Con({tm})</div>,

  // desc
  mujust: tm => <div>Mu({tm})</div>,
  munothing: tm => <div>Mu({tm})</div>,

  // idesc
  imujust: (tm, i) => <div>IMu({tm}, {i})</div>,
  imunothing: (ii, d, i) => <div>Mu({ii}, {d}, {i})</div>,

  // enum
  enumt: tm => tm,
  ze: () => "ze",
  su: tm => tm,

  // definitional equality
  // TODO - hover / click behavior to describe what this means
  eqblue: (pp, qq) => (
    <div>
      {pp} = {qq}
    </div>
  ),

  // free monad
  monad: (d, x) => <div>monad({d}, {x})</div>,
  "return": tm => <div>return {tm}</div>,
  composite: tm => <div>composite {tm}</div>,

  // labelled types
  label: ([l, t]) => <div style={{display: 'flex', flexDirection: 'row'}}>{l} := {t}</div>,
  lret: tm => <div>lret {tm}</div>,

  // nu
  nujust: tm => <div>nujust({tm})</div>,
  nunothing: tm => <div>nunothing({tm})</div>,
  coit: (d, sty, f, s) => <div>coit({d}, {sty}, {f}, {s})</div>,

  // TODO prop, etc
  sigma: s => s,
  pair: p => p,

  unit: () => "1",
  void: () => "0",
};


@Radium
export class PiLayout extends React.Component {
  render() {
    // const [ s, t ] = getChildren(this.props.children);
    const childs = reactJoin(getChildren(this.props.children), "->")

    return (
      <div style={{display: 'flex'}}>
        {childs}
      </div>
    );
  }
}


@Radium
export class JustPiLayout extends React.Component {
  render() {
    const [ s, t ] = getChildren(this.props.children);

    return (
      <div style={{display: 'flex'}}>
        Pi({s}, {t})
      </div>
    );
  }
}


@Radium
export class DependentParamLayout extends React.Component {
  render() {
    const { name } = this.props;
    const [ s ] = getChildren(this.props.children);

    return (
      <div style={{display: 'flex'}}>
        {name} : {s}
      </div>
    );
  }
}


@Radium
export class DScopeLayout extends React.Component {
  render() {
    const bindings = getChildren(this.props.children);

    return (
      <div style={{display: 'flex'}}>
        {reactJoin(bindings, ". ")}.
      </div>
    );
  }
}

@Radium
export class DInTmRNLayout extends React.Component {
  render() {
    return (
      <div className="dintmrn" style={{}}>
        {this.props.children}
      </div>
    );
  }
}

DInTmRNLayout.tags = {
  // neutral
  // dn:

  // canonical
  // dc:

  // lambda
  // dl:
};


@Radium
export class DExTmRNLayout extends React.Component {
  render() {
    return (
      <div style={{}}>
        {this.props.children}
      </div>
    );
  }
}

@Radium
export class DSpineLayout extends React.Component {
  render() {
    return (
      <div style={{}}>
        {this.props.children}
      </div>
    );
  }
}

@Radium
export class RelNameLayout extends React.Component {
  render() {
    return (
      <div style={{}}>
        {this.props.children}
      </div>
    );
  }
}

@Radium
export class RelNamePieceLayout extends React.Component {
  render() {
    const { str, tag, n } = this.props;

    return (
      <div style={{}}>
        {str}{this.constructor.tags[tag](n)}
      </div>
    );
  }
}

RelNamePieceLayout.tags = {
  rel: n => {
    if (n === '0') {
      return "";
    } else {
      return <sup style={{verticalAlign: 'super'}}>{n}</sup>;
    }
  },

  abs: n => {
    if (n === '0') {
      return "";
    } else {
      return <sub style={{verticalAlign: 'sub'}}>{n}</sub>;
    }
  }
}
