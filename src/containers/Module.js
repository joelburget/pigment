import { List } from 'immutable';
import React, { Component, PropTypes } from 'react';
import { bindActionCreators } from 'redux';
import { connect } from 'react-redux';
import { DragDropContext } from 'react-dnd';
import HTML5Backend from 'react-dnd/modules/backends/HTML5';

import ModuleData, { Definition } from '../aspects/module/data';
import Module from '../aspects/module/view';

import { isPathHighlighted,
         isLoaded,
         lookupRef,
         updateAt,
         expressionMouseClick,
         load as loadWidgets,
         findCompletions,
         // moveItem,
         addNew,
         fillHole,
         dispatchUserEdit,
         renameDefinition,
         getActions } from '../ducks/module';


const widgetActions = { expressionMouseClick, updateAt };


@connect(state => ({
  // TODO redundant!
  state: state.module,
  contents: state.module.module.contents,
  name: state.module.module.name,
  scratch: state.module.module.scratch,
  mouseSelection: state.module.mouseSelection,
}))
@DragDropContext(HTML5Backend)
export default class ModuleContainer extends Component {
  static propTypes = {
    dispatch: PropTypes.func.isRequired,
    state: PropTypes.instanceOf(ModuleData).isRequired,
    contents: PropTypes.instanceOf(List).isRequired,
    name: PropTypes.string.isRequired,
    scratch: PropTypes.instanceOf(Definition).isRequired,
    mouseSelection: PropTypes.instanceOf(List).isRequired,
  };

  static childContextTypes = {
    focusPath: PropTypes.object,

    isPathHighlighted: PropTypes.func.isRequired,
    lookupRef: PropTypes.func.isRequired,
    updateAt: PropTypes.func.isRequired,
    expressionMouseClick: PropTypes.func.isRequired,
    findCompletions: PropTypes.func.isRequired,
    renameDefinition: PropTypes.func.isRequired,
    // moveItem: PropTypes.func.isRequired,
    addNew: PropTypes.func.isRequired,
    fillHole: PropTypes.func.isRequired,
    dispatchEdit: PropTypes.func.isRequired,
    getActions: PropTypes.func.isRequired,
  };

  getChildContext() {
    return {
      focusPath: this.props.mouseSelection,

      isPathHighlighted: path => isPathHighlighted(this.props.mouseSelection, path),
      lookupRef: ref => lookupRef(this.props.state, ref),
      updateAt: (ref, update) => this.props.dispatch(
        updateAt(ref, update)
      ),
      expressionMouseClick: path => this.props.dispatch(
        expressionMouseClick(path)
      ),
      findCompletions: (type, ref, prefix) =>
        findCompletions(this.props.state, type, ref, prefix),
      renameDefinition: (index, value) => this.props.dispatch(
        renameDefinition(index, value)
      ),
      // dispatch is, for whatever reason, hella slow. async also?
      moveItem: () => {},
      // moveItem: (beforeIx, afterIx) => this.props.dispatch(
      //   moveItem(beforeIx, afterIx)
      // ),
      addNew: payload => this.props.dispatch(addNew(payload)),
      fillHole: (path, type, category, item) => this.props.dispatch(
        fillHole(path, type, category, item)
      ),
      dispatchEdit: (path, action) => this.props.dispatch(
        dispatchUserEdit(path, action)
      ),
      getActions: path => getActions(this.props.state, path),
    };
  }

  static fetchData(store) {
    if (!isLoaded(store.getState())) {
      return store.dispatch(loadWidgets());
    }
  }

  render() {
    const { dispatch, contents, name, scratch } = this.props;
    return (
      <Module {...bindActionCreators(widgetActions, dispatch)}
              contents={contents}
              name={name}
              scratch={scratch} />
    );
  }
}
