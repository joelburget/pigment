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
         moveItem,
         renameDefinition } from '../ducks/module';
import { Definition as DuckDefinition,
         Note as DuckNote,
         Property as DuckProperty,
         Example as DuckExample,
         MODULE_PUBLIC,
         MODULE_PRIVATE } from '../theory/module';

import ThemeManager from '../ThemeManager';
import Expression from '../components/Expression';
import styles from './Module.scss';


const ITEM_TYPE = 'ITEM_TYPE';
const widgetActions = { expressionMouseClick, updateAt };


const itemSource = {
  beginDrag(props) {
    // console.log('source', props.index);
    return { index: props.index };
  }
};


const itemTarget = {
  hover(props, monitor) {
    const draggedIx = monitor.getItem().index;

    // console.log('target', props.index, draggedIx);
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
  isDragging: monitor.isDragging(),
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

    return (( //connectDragSource(connectDropTarget(
      <div className={styles.definitionRow} style={{ opacity }}>
        {this.props.children}
      </div>
    ));
  }
}

class Example extends Component {
  render() {
    const { item, index, moveItem } = this.props;
    const { name, defn } = item;

    return (
      <Draggable moveItem={moveItem} index={index}>
        <div className={styles.itemLabel}>
          <div className={styles.itemType}>EXAMPLE</div>
          <ItemTitle value={name} index={index} />
        </div>
        <div className={styles.itemContent}>
          <Expression path={List(['module', 'contents', index, 'defn'])}>
            {defn}
          </Expression>
        </div>
      </Draggable>
    );
  }
}


// a law that must hold. ie a test.
//
// for now this is exactly the same as example, but will most certainly be
// customized in the future.
class Property extends Component {
  render() {
    const { item, index, moveItem } = this.props;
    const { name, defn } = item;

    return (
      <Draggable moveItem={moveItem} index={index}>
        <div className={styles.itemLabel}>
          <div className={styles.itemType}>EXAMPLE</div>
          <ItemTitle value={name} index={index} />
        </div>
        <div className={styles.itemContent}>
          <Expression path={List(['module', 'contents', index, 'defn'])}>
            {defn}
          </Expression>
        </div>
      </Draggable>
    );
  }
}


class Note extends Component {
  render() {
    const { item, index, moveItem } = this.props;
    const { name, defn } = item;

    return (
      <Draggable moveItem={moveItem} index={index}>
        <div className={styles.itemLabel}>
          <div className={styles.itemType}>NOTE</div>
          <ItemTitle value={name} index={index} />
        </div>
        <div className={styles.itemContent}>{defn}</div>
      </Draggable>
    );
  }
}


class ItemTitle extends Component {
  static propTypes = {
    value: PropTypes.string.isRequired,
    index: PropTypes.number.isRequired,
  };

  static contextTypes = {
    renameDefinition: PropTypes.func.isRequired,
  };

  state = {
    editing: false,
  };

  render() {
    const { value } = this.props;
    const { editing } = this.state;

    const inner = editing ?
      <input defaultValue={value}
             onKeyPress={::this.handleKeyPress}
             onBlur={::this.returnToStatic}
             ref="input" /> :
      <span onClick={() => {this.setState({ editing: true });}}>
        {value}
      </span>;

    return (
      <div>
        {inner}
      </div>
    );
  }

  // focus and move cursor to the end when the input exists
  componentDidUpdate() {
    const { input } = this.refs;
    if (input) {
      const node = React.findDOMNode(input);
      node.focus();
      node.selectionStart = node.selectionEnd = node.value.length;
    }
  }

  returnToStatic() {
    this.context.renameDefinition(
      this.props.index,
      React.findDOMNode(this.refs.input).value,
    );
    this.setState({ editing: false });
  }

  handleKeyPress(event) {
    if (event.key === "Enter") {
      this.returnToStatic();
    }
  }
}


class Definition extends Component {
  render() {
    const { item, index, moveItem } = this.props;
    const { name, defn, visibility } = item;

    // TODO put this somewhere useful
    const visibilityElem = visibility === MODULE_PUBLIC ?
      'public' :
      'private';

    return (
      <Draggable moveItem={moveItem} index={index}>
        <div className={styles.itemLabel}>
          <div className={styles.itemType}>DEFINITION</div>
          <ItemTitle value={name} index={index} />
          <div>{visibilityElem}</div>
        </div>
        <div className={styles.itemContent}>
          <Expression path={List(['module', 'contents', index, 'defn'])}>
            {defn}
          </Expression>
        </div>
      </Draggable>
    );
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
  };

  // TODO rename away from definitions.
  // items? too generic
  itemDispatch(item, index) {
    const { expressionMouseClick } = this.props;
    const { moveItem, renameDefinition } = this.context;
    const props = {
      item, renameDefinition, index, expressionMouseClick, moveItem
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
    const { contents, name } = this.props;

    return (
      <div className={styles.module}>
        <h6>MODULE {name}</h6>
        <div className={styles.moduleTable}>
          { contents.map(::this.itemDispatch).toJS() }
        </div>
        <div>
          <button className="mdl-button" style={{ padding: 0 }}>Add New</button>
        </div>
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
    renameDefinition: PropTypes.func.isRequired,
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
      renameDefinition: (index, value) => this.props.dispatch(
        renameDefinition(index, value)
      ),
      // dispatch is, for whatever reason, hella slow. async also?
      moveItem: () => {},
      // moveItem: (beforeIx, afterIx) => this.props.dispatch(
      //   moveItem(beforeIx, afterIx)
      // ),
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
