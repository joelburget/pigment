import React from 'react';
import Radium from 'radium';

function getChildren(children) {
  let arr = [];
  React.Children.forEach(children, child => arr.push(child));
  return arr;
}

let styles = {
  refLayout: {},
  parameterLayout: {},
  definitionLayout: {},
  entryModuleLayout: {},
  devLayout: {},
  entriesLayout: {},
  entryHeaderLayout: {},
  moduleHeaderLayout: {},
  nameExplainLayout: {},
  entryEntityLayout: {},
};

@Radium
export class RefLayout extends React.Component {
  render () {
    const [name, ty] = getChildren(this.props.children);

    return <div style={styles.refLayout}>
      {name} : {ty}
    </div>;
  }
}

@Radium
export class ParameterLayout extends React.Component {
  render () {
    const [pKind] = getChildren(this.props.children);

    return <div style={styles.parameterLayout}>
      {pKind}
    </div>;
  }
}

@Radium
export class DefinitionLayout extends React.Component {
  render () {
    const [dKind, dev] = getChildren(this.props.children);

    return <div style={styles.definitionLayout}>
      {dKind}
      {dev}
    </div>;
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
      {suspendState}
      {entries}
    </div>;
  }
}

@Radium
export class EntriesLayout extends React.Component {
  render () {
    const entries = getChildren(this.props.children);

    return <div style={styles.entriesLayout}>
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
      {metadata}
      {ty}
    </div>;
  }
}

@Radium
export class ModuleHeaderLayout extends React.Component {
  render () {
    const [name, purpose, metadata] = getChildren(this.props.children);

    return <div style={styles.moduleHeaderLayout}>
      {name}
      {purpose}
      {metadata}
    </div>;
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
export class EntryEntityLayout extends React.Component {
  render () {
    const [header, entity] = getChildren(this.props.children);

    return <div style={styles.entryEntityLayout}>
      {header}
      {entity}
    </div>;
  }
}
