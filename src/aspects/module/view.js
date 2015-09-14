import React, { Component, PropTypes } from 'react';
import { List } from 'immutable';
import { DragSource, DropTarget } from 'react-dnd';

import ThemeManager from '../../ThemeManager';
import Expression from '../../components/Expression';

import { Definition as DuckDefinition,
         Note as DuckNote,
         Property as DuckProperty,
         Example as DuckExample,
         MODULE_PUBLIC,
         MODULE_PRIVATE } from './data';
import styles from './style.scss';


const ITEM_TYPE = 'ITEM_TYPE';


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


export default class Module extends Component {
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
    addNew: PropTypes.func.isRequired,
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
          <button onClick={this.context.addNew}
                  className="mdl-button"
                  style={{ padding: 0 }}>
            Add New
          </button>
        </div>
      </div>
    );
  }
}
