import React, { Component, PropTypes } from 'react';
import { bindActionCreators } from 'redux';
import { connect } from 'react-redux';
import { List } from 'immutable';
import Menu from 'material-ui/lib/menu/menu';
import { DragSource, DropTarget } from 'react-dnd';
import { DragDropContext } from 'react-dnd';
import HTML5Backend from 'react-dnd/modules/backends/HTML5';

import { isPathHighlighted,
         isLoaded,
         lookupRef,
         updateAt,
         expressionMouseClick,
         load as loadWidgets,
         findCompletions,
         moveItem } from '../ducks/module';
import { Definition as DuckDefinition,
         Note as DuckNote,
         Property as DuckProperty,
         Example as DuckExample } from '../theory/module';

import ThemeManager from '../ThemeManager';
import Expression from '../components/Expression';
import styles from './Module.scss';


const ITEM_TYPE = 'ITEM_TYPE';
const widgetActions = { expressionMouseClick, updateAt };


const itemSource = {
  beginDrag(props) {
    console.log(props);
    return { index: props.index };
  }
};


const itemTarget = {
  hover(props, monitor) {
    const draggedIx = monitor.getItem().index;

    if (draggedIx !== props.index) {
      props.moveItem(draggedIx, props.index);
    }
  }
};


// give an example of the thing in use -- what is the return type of this?
@DropTarget(ITEM_TYPE, itemTarget, connect => ({
  connectDropTarget: connect.dropTarget(),
}))
@DragSource(ITEM_TYPE, itemSource, (connect, monitor) => ({
  connectDragSource: connect.dragSource(),
  isDragging: monitor.isDragging()
}))
class Draggable {
  static propTypes = {
    connectDragSource: PropTypes.func.isRequired,
    connectDropTarget: PropTypes.func.isRequired,
    isDragging: PropTypes.bool.isRequired,
    // children:
  };

  render() {
    const { isDragging, connectDragSource, connectDropTarget } = this.props;
    const opacity = isDragging ? 0 : 1;

    return connectDragSource(connectDropTarget(
      <tr className={styles.definitionRow} style={{ opacity }}>
        {this.props.children}
      </tr>
    ));
  }
}

class Example extends Component {
  render() {
    const { moveItem, index } = this.props;

    return (
      <Draggable moveItem={moveItem} index={index}>
        <td className={styles.definitionType}>EXAMPLE</td>
        <td>(example title)</td>
        <td>(this is an example)</td>
      </Draggable>
    );
  }
}


// a law that must hold. ie a test.
class Property extends Component {
  render() {
    const { moveItem, index } = this.props;

    return (
      <Draggable moveItem={moveItem} index={index}>
        <td className={styles.definitionType}>PROPERTY</td>
        <td>(property title)</td>
        <td>(this is a property)</td>
      </Draggable>
    );
  }
}


class Note extends Component {
  render() {
    const { name, defn, moveItem, index } = this.props;

    return (
      <Draggable moveItem={moveItem} index={index}>
        <td className={styles.definitionType}>NOTE</td>
        <td>{name}</td>
        <td>{defn}</td>
      </Draggable>
    );
  }
}


class Definition extends Component {
  state = {
    editing: false,
  };

  render() {
    const { name, defn, index, moveItem } = this.props;

    const nameCell = this.state.editing ?
      <input defaultValue={name}
             onKeyPress={::this.handleKeyPress}
             ref="input" /> :
      <span onClick={::this.toggleEditing}>{name}</span>;

    return (
      <Draggable moveItem={moveItem} index={index}>
        <td className={styles.definitionType}>DEFINITION</td>
        <td>{nameCell}</td>
        <td>
          <Expression path={List(['module', 'contents', index, 'defn'])}>
            {defn}
          </Expression>
        </td>
      </Draggable>
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
  static childContextTypes = {
    muiTheme: React.PropTypes.object
  };

  getChildContext() {
    return {
      muiTheme: ThemeManager.getCurrentTheme()
    };
  }

  static contextTypes = {
    moveItem: PropTypes.func.isRequired,
  };

  static propTypes = {
    contents: PropTypes.object.isRequired,
    renameDefinition: PropTypes.func.isRequired,
  };

  // TODO rename away from definitions.
  // items? too generic
  itemDispatch(item, index) {
    const { name, defn } = item;
    const { renameDefinition, expressionMouseClick } = this.props;
    const { moveItem } = this.context;
    const props = {
      renameDefinition, name, defn, index, expressionMouseClick, moveItem
    };

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
          <tbody>
            { contents.map(::this.itemDispatch) }
            <tr className={styles.definitionRow}>
              <td><button className="mdl-button" style={{ padding: 0 }}>Add New</button></td>
            </tr>
          </tbody>
        </table>
      </div>
    );
  }
}


@connect(state => ({
  // TODO redundant!
  state: state.module,
  contents: state.module.module.contents,
  name: state.module.module.name,
  mouseSelection: state.module.mouseSelection,
}))
@DragDropContext(HTML5Backend)
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
    moveItem: PropTypes.func.isRequired,
  };

  getChildContext() {
    return {
      isPathHighlighted: path => isPathHighlighted(this.props.mouseSelection, path),
      lookupRef: ref => lookupRef(this.props.state, ref),
      updateAt: (ref, update) => this.props.dispatch(
        updateAt(ref, update)
      ),
      expressionMouseClick: path => this.props.dispatch(
        expressionMouseClick(path)
      ),
      findCompletions: (type, ref, prefix) => this.props.dispatch(
        findCompletions(this.props.state, type, ref, prefix)
      ),
      moveItem: (beforeIx, afterIx) => this.props.dispatch(
        moveItem(beforeIx, afterIx)
      ),
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
