import React, { Component, PropTypes } from 'react';
import Immutable, { List } from 'immutable';
import { DragSource, DropTarget } from 'react-dnd';
import RadioButtonGroup from 'material-ui/lib/radio-button-group';
import RadioButton from 'material-ui/lib/radio-button';
// temporarily removed for DropDownMenu
// import SelectField from 'material-ui/lib/select-field';
import DropDownMenu from 'material-ui/lib/drop-down-menu';
import TextField from 'material-ui/lib/text-field';

import MuiList from 'material-ui/lib/lists/list';
import ListItem from 'material-ui/lib/lists/list-item';
import ListDivider from 'material-ui/lib/lists/list-divider';

import ThemeManager from '../../ThemeManager';
import Expression from '../../components/Expression';
import { Type, Hole } from '../../theory/tm';

import * as data from './data';
import { MODULE_PUBLIC, MODULE_PRIVATE } from './data';
import styles from './style.scss';


const ITEM_TYPE = 'ITEM_TYPE';


const itemSource = {
  beginDrag(props) {
    // console.log('source', props.path);
    return { path: props.path };
  }
};


const itemTarget = {
  hover(props, monitor) {
    const draggedIx = monitor.getItem().path;

    // console.log('target', props.path, draggedIx);
    if (!Immutable.is(draggedIx, props.path)) {
      props.moveItem(draggedIx, props.path);
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
        <div>
          {this.props.children}
        </div>
        <div className={styles.rowSpacer} />
      </div>
    ));
  }
}

class Example extends Component {
  render() {
    const { item, path, moveItem } = this.props;
    const { name, defn } = item;

    return (
      <Draggable moveItem={moveItem} path={path}>
        <div className={styles.itemLabel}>
          <div className={styles.itemType}>EXAMPLE</div>
          <ItemTitle value={name} path={path} />
        </div>
        <div className={styles.itemContent}>
          <Expression path={path.push('defn')}>
            {defn}
          </Expression>
          <div>
            <div className={styles.itemType}>OUTPUT</div>
          </div>
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
    const { item, path, moveItem } = this.props;
    const { name, defn } = item;

    return (
      <Draggable moveItem={moveItem} path={path}>
        <div className={styles.itemLabel}>
          <div className={styles.itemType}>EXAMPLE</div>
          <ItemTitle value={name} path={path} />
        </div>
        <div className={styles.itemContent}>
          <Expression path={path.push('defn')}>
            {defn}
          </Expression>
          <div>
            <div className={styles.itemType}>RESULT</div>
          </div>
        </div>
      </Draggable>
    );
  }
}


class Note extends Component {
  render() {
    const { item, path, moveItem } = this.props;
    const { name, defn } = item;

    return (
      <Draggable moveItem={moveItem} path={path}>
        <div className={styles.itemLabel}>
          <div className={styles.itemType}>NOTE</div>
          <ItemTitle value={name} path={path} />
        </div>
        <div className={styles.itemContent}>{defn}</div>
      </Draggable>
    );
  }
}


class ItemTitle extends Component {
  static propTypes = {
    value: PropTypes.string.isRequired,
    // path: PropTypes.number.isRequired,
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
      this.props.path,
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
  static contextTypes = {
    dispatchAction: PropTypes.func.isRequired,
  };

  render() {
    const { item, path, moveItem } = this.props;
    const { name, defn, visibility } = item;

    // TODO put this somewhere useful
    const visibilityElem = visibility === MODULE_PUBLIC ?
      'public' :
      'private';

    const dispatchAction = action =>
      this.context.dispatchAction(path.push('defn'), action());

    const menuItems = item.defn.actions().map(({ name, action }) =>
      <ListItem primaryText={name} onClick={() => dispatchAction(action)} />
    );

    return (
      <Draggable moveItem={moveItem} path={path}>
        <div className={styles.itemRow}>

          <div // display row
            className={styles.rowContent}
            >
            <div className={styles.itemLabel}>
              <div className={styles.itemType}>DEFINITION</div>
              <ItemTitle value={name} path={path} />
              <div>{visibilityElem}</div>
            </div>
            <div className={styles.itemContent}>
              <Expression path={path.push('defn')}>
                {defn}
              </Expression>
            </div>
            <div className={styles.itemNotes}>
              <div className={styles.itemType}>NOTES</div>
              <TextField multiLine />
            </div>
          </div>

          <div // edit row
            >
            <div className={styles.itemType}>EDIT</div>
            {/*
            <Expression path={path.push('type')}>
            </Expression>
            */}
            <MuiList>
              {menuItems}
            </MuiList>
          </div>

        </div>
      </Draggable>
    );
  }
}


export default class Module extends Component {
  static childContextTypes = {
    muiTheme: React.PropTypes.object,
  };

  getChildContext() {
    return {
      muiTheme: ThemeManager.getCurrentTheme(),
    };
  }

  static propTypes = {
    contents: PropTypes.object.isRequired,
    name: PropTypes.string.isRequired,
    scratch: PropTypes.object.isRequired,
  };

  render() {
    const { contents, name, scratch } = this.props;
    const renderedItems = contents
      .map((item, index) =>
           <Item item={item}
                 path={List(['module', 'contents', index])} />
      )
      .toJS();

    return (
      <div className={styles.module}>
        <h6>MODULE {name}</h6>
        <div className={styles.moduleTable}>
          {renderedItems}
        </div>
        <div>
          <NewItem scratch={scratch} />
        </div>
      </div>
    );
  }
}


class Item extends Component {
  static contextTypes = {
    moveItem: PropTypes.func.isRequired,
    renameDefinition: PropTypes.func.isRequired,
    expressionMouseClick: PropTypes.func.isRequired,
  };

  render() {
    const { item, path } = this.props;
    const { moveItem, renameDefinition, expressionMouseClick } = this.context;
    const props = {
      item, renameDefinition, path, expressionMouseClick, moveItem
    };

    var cls;
    if (item instanceof data.Definition) {
      cls = Definition;
    } else if (item instanceof data.Example) {
      cls = Example;
    } else if (item instanceof data.Property) {
      cls = Property;
    } else if (item instanceof data.Note) {
      cls = Note;
    }

    return React.createElement(cls, props);
  }
}


class NewItem extends Component {
  static contextTypes = {
    addNew: PropTypes.func.isRequired,
  };

  // bleh:
  // * definition
  //   - visibility
  //   - defn: Tm
  // * note, property, example
  //   - defn: string
  state = {
    type: 'definition',
    visibility: 'public',
  };

  render() {
    const itemTypes = [
      { text: 'Definition', payload: 'definition' },
      { text: 'Note',       payload: 'note', disabled: true },
      { text: 'Property',   payload: 'property', disabled: true },
      { text: 'Example',    payload: 'example', disabled: true },
    ];

    const visibilities = [
      { text: 'public', payload: MODULE_PUBLIC },
      { text: 'private', payload: MODULE_PRIVATE },
    ];

    return (
      <div className={styles.newItem}>

        <div>
          New
          <DropDownMenu menuItems={itemTypes}
                        value={this.state.type}
                        style={{ top: 16 }}
                        onChange={::this.handleSelectType} />
        </div>

        <div>
          Name: <TextField defaultValue='new item' ref='name' />
        </div>

        <div>
          Visibility: <DropDownMenu menuItems={visibilities}
                                    value={this.state.visibility}
                                    style={{ top: 16 }}
                                    onChange={::this.handleSelectVisibility} />
        </div>

        <hr />

        <div>
          <Item item={this.props.scratch}
                path={List(['module', 'scratch'])} />
          {/*<textarea className='mdl-textfield__input' />*/}
        </div>

        <div>
          <button onClick={::this.handleCreate}
                  className='mdl-button'
                  style={{ padding: 0 }}>
            CREATE
          </button>
        </div>

      </div>
    );
  }

  handleSelectType(event) {
    this.setState({ type: event.target.value });
  }

  handleSelectVisibility(event) {
    this.setState({ visibility: event.target.value });
  }

  handleCreate() {
    const name = this.refs.name.getValue();
    const { type, visibility } = this.state;

    this.context.addNew({
      type,
      name,
      visibility,
    });
    // this.context.addNew(...);
  }
}
