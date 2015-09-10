import React, {Component, PropTypes} from 'react';
import {bindActionCreators} from 'redux';
import {connect} from 'react-redux';
import { List } from 'immutable';
import { Menu, MenuItem, MenuDivider } from 'material-ui';

import { isPathHighlighted,
         isLoaded,
         lookupRef,
         updateAt,
         expressionMouseClick,
         load as loadWidgets,
         findCompletions } from '../ducks/module';
import { Definition as DuckDefinition,
         Note as DuckNote,
         Property as DuckProperty,
         Example as DuckExample } from '../theory/module';

import ThemeManager from './ThemeManager';
import Expression from './Expression';
import styles from './Widgets.scss';

const widgetActions = { expressionMouseClick, updateAt };


// give an example of the thing in use -- what is the return type of this?
class Example extends Component {
  render() {
    return (
      <tr className={styles.definitionRow}>
        <td className={styles.definitionType}>EXAMPLE</td>
        <td>(example title)</td>
        <td>(this is an example)</td>
      </tr>
    );
  }
}


// a law that must hold. ie a test.
class Property extends Component {
  render() {
    return (
      <tr className={styles.definitionRow}>
        <td className={styles.definitionType}>PROPERTY</td>
        <td>(property title)</td>
        <td>(this is a property)</td>
      </tr>
    );
  }
}


class Note extends Component {
  render() {
    const { name, defn } = this.props;

    return (
      <tr className={styles.definitionRow}>
        <td className={styles.definitionType}>NOTE</td>
        <td>{name}</td>
        <td>{defn}</td>
      </tr>
    );
  }
}


class Definition extends Component {
  state = {
    editing: false,
  };

  render() {
    const { name, defn, index } = this.props;

    const nameCell = this.state.editing ?
      <input defaultValue={name}
             onKeyPress={::this.handleKeyPress}
             ref="input" /> :
      <span onClick={::this.toggleEditing}>{name}</span>;

    return (
      <tr className={styles.definitionRow}>
        <td className={styles.definitionType}>DEFINITION</td>
        <td>{nameCell}</td>
        <td>
          <Expression path={List(['module', 'contents', index, 'defn'])}>
            {defn}
          </Expression>
        </td>
      </tr>
    );
  }

  toggleEditing() {
    this.setState({ editing: !this.state.editing });
  }

  handleKeyPress(event) {
    if (event.key === "Enter") {
      this.props.renameDefinition(this.props.index, this.refs.input.getDOMNode().value);
      this.toggleEditing();
    }
  }
}

class ContextualMenu extends Component {
  static childContextTypes = {
    muiTheme: React.PropTypes.object
  };

  getChildContext() {
    return {
      muiTheme: ThemeManager.getCurrentTheme()
    };
  }

  render() {
    const menuItems = [
      { text: 'maps' },
      { text: 'books' },
      { text: 'flights' },
      { text: 'apps' },
    ];
    return <Menu menuItems={menuItems} />;
  }
}

class Module extends Component {
  static propTypes = {
    contents: PropTypes.object.isRequired,
    renameDefinition: PropTypes.func.isRequired,
  };

  // TODO rename away from definitions.
  // items? too generic
  itemDispatch(item, index) {
    const { name, defn } = item;
    const { renameDefinition, expressionMouseClick } = this.props;
    const props = { renameDefinition, name, defn, index, expressionMouseClick };

    var cls;
    if (item instanceof DuckDefinition) {
      cls = Definition;
    } else if (item instanceof DuckExample) {
      cls = Example;
    } else if (item instanceof DuckProperty) {
      cls = Property;
    } else if (item instanceof DuckNote) {
      cls = Note;
    }

    return React.createElement(cls, props);
  }

  render() {
    const { contents, name, renameDefinition } = this.props;

    return (
      <div className={styles.module}>
        <h6>MODULE {name}</h6>
        <table>
          { contents.map(::this.itemDispatch) }
        </table>
      </div>
    );
  }
}


@connect(state => ({
  // TODO redundant!
  state: state.widgets,
  contents: state.widgets.module.contents,
  name: state.widgets.module.name,
  mouseSelection: state.widgets.mouseSelection,
}))
export default class ModuleContainer {
  static propTypes = {
    dispatch: PropTypes.func.isRequired,
  };

  static childContextTypes = {
    isPathHighlighted: PropTypes.func.isRequired,
    lookupRef: PropTypes.func.isRequired,
    updateAt: PropTypes.func.isRequired,
    expressionMouseClick: PropTypes.func.isRequired,
    findCompletions: PropTypes.func.isRequired,
  };

  getChildContext() {
    return {
      isPathHighlighted: path => isPathHighlighted(this.props.mouseSelection, path),
      lookupRef: ref => lookupRef(this.props.state, ref),
      updateAt: (ref, update) => this.props.dispatch(updateAt(ref, update)),
      expressionMouseClick: path => this.props.dispatch(expressionMouseClick(path)),
      findCompletions: (type, ref, prefix) => this.props.dispatch(findCompletions(this.props.state, type, ref, prefix)),
    };
  }

  static fetchData(store) {
    if (!isLoaded(store.getState())) {
      return store.dispatch(loadWidgets());
    }
  }

  render() {
    const { dispatch, contents, name } = this.props;
    return <Module {...bindActionCreators(widgetActions, dispatch)}
                   contents={contents}
                   name={name} />;
  }
}
