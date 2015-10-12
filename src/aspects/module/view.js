/* eslint no-unused-vars: 0 */
/* eslint react/no-multi-comp: 0 */
import React, { Component, PropTypes } from 'react';
import { List, is } from 'immutable';
import { DragSource, DropTarget } from 'react-dnd';

import isPrefix from '../../util/isPrefix';
import { expr } from '../../components/Expression';
import { Type, Hole } from '../../theory/tm';
import { PropTypesPath } from '../../theory/ref';

import * as data from './data';
import {
  MODULE_PUBLIC,
  MODULE_PRIVATE,
  Module as ModuleData,
  Note as NoteData,
  Definition as DefinitionData,
  Property as PropertyData,
  Example as ExampleData
} from './data';
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
    if (!is(draggedIx, props.path)) {
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
class Draggable extends Component {
  static propTypes = {
    connectDragSource: PropTypes.func.isRequired,
    connectDropTarget: PropTypes.func.isRequired,
    isDragging: PropTypes.bool.isRequired,
    children: React.PropTypes.node.isRequired,
  };

  render() {
    const { isDragging, connectDragSource, connectDropTarget } = this.props;
    const opacity = isDragging ? 0 : 1;

    return (( // connectDragSource(connectDropTarget(
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
  static propTypes = {
    item: PropTypes.instanceOf(ExampleData).isRequired,
    path: PropTypesPath.isRequired,
    moveItem: PropTypes.func.isRequired,
  };

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
          {expr(item, path, 'defn')}
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
  static propTypes = {
    item: PropTypes.instanceOf(PropertyData).isRequired,
    path: PropTypesPath.isRequired,
    moveItem: PropTypes.func.isRequired,
  };

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
          {expr(item, path, 'defn')}
          <div>
            <div className={styles.itemType}>RESULT</div>
          </div>
        </div>
      </Draggable>
    );
  }
}


class Note extends Component {
  static propTypes = {
    item: PropTypes.instanceOf(NoteData).isRequired,
    path: PropTypesPath.isRequired,
    moveItem: PropTypes.func.isRequired,
  };

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
    path: PropTypesPath.isRequired,
  };

  static contextTypes = {
    renameDefinition: PropTypes.func.isRequired,
  };

  state = {
    editing: false,
  };

  // focus and move cursor to the end when the input exists
  componentDidUpdate() {
    const { input } = this.refs;
    if (input) {
      input.focus();
      input.selectionStart = input.selectionEnd = input.value.length;
    }
  }

  returnToStatic() {
    this.context.renameDefinition(
      this.props.path,
      this.refs.input.value,
    );
    this.setState({ editing: false });
  }

  handleKeyPress(event) {
    if (event.key === 'Enter') {
      this.returnToStatic();
    }
  }

  render() {
    const { value } = this.props;
    const { editing } = this.state;

    const inner = editing ?
      <input defaultValue={value}
             onKeyPress={::this.handleKeyPress}
             onBlur={::this.returnToStatic}
             ref='input' /> :
      <span onClick={() => {this.setState({ editing: true });}}>
        {value}
      </span>;

    return (
      <div>
        {inner}
      </div>
    );
  }
}


function ListItem({ primaryText, onClick }) {
  // TODO figure out why opacity is 0 from mdl-menu__item
  return (
    <li className='mdl-menu__item'
        style={{opacity: 1}}
        onClick={onClick}>
      {primaryText}
    </li>
  );
}


function UiList({ children }) {
  return (
    <div>
      {children}
    </div>
  );
}


class Definition extends Component {
  static propTypes = {
    item: PropTypes.instanceOf(DefinitionData).isRequired,
    path: PropTypes.instanceOf(List).isRequired,
    moveItem: PropTypes.func.isRequired,
  };

  static contextTypes = {
    focusPath: PropTypes.object,

    dispatchEdit: PropTypes.func.isRequired,
    getActions: PropTypes.func.isRequired,
  };

  render() {
    const { focusPath } = this.context;
    const { item, path, moveItem } = this.props;
    const { name, defn, visibility } = item;

    // TODO put this somewhere useful
    const visibilityElem = visibility === MODULE_PUBLIC ?
      'public' :
      'private';

    const dispatchEdit = action =>
      this.context.dispatchEdit(focusPath, action);

    const menuItems = focusPath && isPrefix(path, focusPath) ?
      this.context.getActions(focusPath)
        .map(({ title, id }) =>
          <ListItem key={id}
                    primaryText={title}
                    onClick={() => dispatchEdit(id)} />
        ).toArray() :
      [];

    return (
      <Draggable moveItem={moveItem} path={path}>

        <div // display row
          className={styles.rowContent}
          >

          <div className={styles.itemLabel} // header column
            >
            <div className={styles.itemType}>DEFINITION</div>
            <ItemTitle value={name} path={path} />
            <div>{visibilityElem}</div>
          </div>

          <div className={styles.itemContent} // term column
            >
            <div className={styles.itemType}>TERM</div>

            {expr(item, path, 'defn')}
          </div>

          <div className={styles.itemContent} // type column
            >
            <div className={styles.itemType}>TYPE</div>
            {expr(item, path, ['defn', 'type'])}
          </div>
        </div>

        {!!menuItems.length &&
          <div // edit row
            >
            <div className={styles.itemType}>EDIT</div>
            <UiList>
              {menuItems}
            </UiList>
          </div>
        }

      </Draggable>
    );
  }
}


class TextField extends Component {
  static propTypes = {
    multiLine: PropTypes.bool,
    defaultValue: PropTypes.string,
  };

  getValue() {
    return this.refs.iput.value;
  }

  render() {
    const { multiLine, defaultValue } = this.props;
    const field = multiLine ?
      <textarea className='mdl-textfield__input' type='text' ref='iput' ></textarea> :
      <input className='mdl-textfield__input' type='text' defaultValue={defaultValue} ref='iput' />;

    return (
      <div className='mdl-textfield mdl-js-textfield'>
        {field}
      </div>
    );
  }
}


export default class Module extends Component {
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
        <h6><span className={styles.moduleHeader}>MODULE</span> {name}</h6>
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
  static propTypes = {
    item: PropTypes.oneOfType([
      PropTypes.instanceOf(NoteData),
      PropTypes.instanceOf(DefinitionData),
      PropTypes.instanceOf(PropertyData),
      PropTypes.instanceOf(ExampleData),
    ]).isRequired,
    path: PropTypes.instanceOf(List).isRequired,
  };

  static contextTypes = {
    moveItem: PropTypes.func.isRequired,
    renameDefinition: PropTypes.func.isRequired,
    expressionMouseClick: PropTypes.func.isRequired,
  };

  render() {
    const { item, path } = this.props;
    const { renameDefinition, expressionMouseClick, moveItem } = this.context;

    const props = {
      item, renameDefinition, path, expressionMouseClick, moveItem
    };

    let cls;
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


class DropDownMenu extends Component {
  static propTypes = {
    menuItems: PropTypes.array.isRequired,
    value: PropTypes.string.isRequired,
    style: PropTypes.object,
    onChange: PropTypes.func.isRequired,
  };

  render() {
    const { menuItems, value, style, onChange } = this.props;

    return (
      <select value={value} onChange={onChange} style={style}>
        {menuItems.map(({ text, payload }) => (
          <option key={payload} value={payload}>
            {text}
          </option>
        ))}
      </select>
    );
  }
}


class NewItem extends Component {
  static propTypes = {
    scratch: PropTypes.instanceOf(DefinitionData).isRequired,
  };

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

  render() {
    const itemTypes = [
      { text: 'Definition', payload: 'definition' },
      { text: 'Note', payload: 'note', disabled: true },
      { text: 'Property', payload: 'property', disabled: true },
      { text: 'Example', payload: 'example', disabled: true },
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
          Visibility:
            <DropDownMenu menuItems={visibilities}
                                    value={this.state.visibility}
                                    style={{ top: 16 }}
                                    onChange={::this.handleSelectVisibility} />
        </div>

        <hr />

        <div>
          <Item item={this.props.scratch}
                path={List(['module', 'scratch'])} />
          {/* <textarea className='mdl-textfield__input' /> */}
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
}
