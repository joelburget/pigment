import React, { Component, PropTypes } from 'react';
import { bindActionCreators } from 'redux';
import { connect } from 'react-redux';
import { DragDropContext } from 'react-dnd';
import HTML5Backend from 'react-dnd/modules/backends/HTML5';

import Module from '../aspects/module/view';

import { isPathHighlighted,
         isLoaded,
         lookupRef,
         updateAt,
         expressionMouseClick,
         load as loadWidgets,
         findCompletions,
         moveItem,
         renameDefinition } from '../ducks/module';


const widgetActions = { expressionMouseClick, updateAt };


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
