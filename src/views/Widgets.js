import React, {Component, PropTypes} from 'react';
import {bindActionCreators} from 'redux';
import {isLoaded} from '../reducers/widgets';
import {connect} from 'react-redux';
import * as widgetActions from '../actions/widgetActions';
import {load as loadWidgets} from '../actions/widgetActions';
import {requireServerCss} from '../util';

import Expression from './Expression';


const styles = __CLIENT__ ?
  require('./Widgets.scss') :
  requireServerCss(require.resolve('./Widgets.scss'));


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
    const { name, defn } = this.props;
    const nameCell = this.state.editing ?
      <input defaultValue={name}
             onKeyPress={::this.handleKeyPress}
             ref="input" /> :
      <span onClick={::this.toggleEditing}>{name}</span>;

    return (
      <tr className={styles.definitionRow}>
        <td className={styles.definitionType}>DEFINITION</td>
        <td>{nameCell}</td>
        <td><Expression>{defn}</Expression></td>
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

class Workspace extends Component {
  static propTypes = {
    goal: PropTypes.object.isRequired,
    definitions: PropTypes.array.isRequired,
    renameDefinition: PropTypes.func.isRequired,
  };

  // TODO rename away from definitions.
  // items? too generic
  definitionDispatch({ name, defn, type }, index) {
    const { renameDefinition } = this.props;
    const props = { renameDefinition, name, defn, index };
    const dispatch = {
      definition: Definition,
      example: Example,
      property: Property,
      note: Note,
    };

    return React.createElement(dispatch[type], props);
  }

  render() {
    const { goal, definitions, renameDefinition } = this.props;

    return (
      <div className={styles.workspace}>

        <div>
          <h6>GOAL</h6>
          <Expression>{goal}</Expression>
        </div>

        <div>
          <h6>WORKSPACE</h6>
          <table>
            { definitions.map(::this.definitionDispatch) }
          </table>
        </div>

      </div>
    );
  }
}


@connect(state => ({
  goal: state.widgets.goal,
  definitions: state.widgets.definitions,
}))
export default class WidgetsContainer {
  static propTypes = {
    dispatch: PropTypes.func.isRequired
  };

  static fetchData(store) {
    if (!isLoaded(store.getState())) {
      return store.dispatch(loadWidgets());
    }
  }

  render() {
    const { dispatch, goal, definitions } = this.props;
    return <Workspace {...bindActionCreators(widgetActions, dispatch)}
                      {...{ goal, definitions }} />;
  }
}
