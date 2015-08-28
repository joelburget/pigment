import React, {Component} from 'react';
import {connect} from 'react-redux';
import {requireServerCss, requireServerImage} from '../util';

const styles = __CLIENT__ ? require('./Home.scss') : requireServerCss(require.resolve('./Home.scss'));


class Name extends Component {
  constructor(props) {
    super(props);
    this.state = { expanded: false };
  }

  render () {
    return (
      <div className={styles.name} onClick={this.handleClick}>
        {this.props.children}
        {this.state.expanded && this.renderContextual()}
      </div>
    );
  }

  handleClick() {
    this.setState({ expanded: !this.state.expanded });
  }

  renderContextual() {
    return (
      <ul className="mdl-menu mdl-menu--bottom-left mdl-js-menu mdl-js-ripple-effect"
          htmlFor="demo-menu-lower-left">
        <li className="mdl-menu__item">Some Action</li>
        <li className="mdl-menu__item">Another Action</li>
        <li disabled className="mdl-menu__item">Disabled Action</li>
        <li className="mdl-menu__item">Yet Another Action</li>
      </ul>
    );
  }
}


class Hole extends Component {
  render() {
    return (
      <div className={styles.hole}>
      ?
      </div>
    );
  }
}


class Implementation extends Component {
  render() {
    return (
      <div className={styles.implementation}>
        <Name>simple http</Name>
        <Hole />
        <Name>{'>>='}</Name>
        <Name>to success or failure</Name>
      </div>
    );
  }
}


class Signature extends Component {
  render() {
    const styles = require('./Home.scss');
    // require the logo image both from client and server
    const logoImage = require('./logo.png');
    return (
      <div>
        <div className={styles.signatureRow}>
          <Name>download image</Name> :
        </div>

        <div>
          <div className={styles.signatureRow}>
            (<Name>name</Name> : <Name>String</Name>)
          </div>
          <div className={styles.signatureRow}>
            (<Name>uri</Name> : <Name>URI</Name>)
          </div>
          <div>
            &darr;
          </div>
          <div className={styles.signatureRow}>
            <Name>IO</Name> <Name>success or failure</Name>
          </div>
        </div>
      </div>
    );
  }
}


export default class Development extends Component {
  render() {
    return (
      <div className={styles.development}>

        <div style={{width: 100, height: 50}} />

        <div className={styles.toolbox}>
          <div className={styles.header}>
            TOOLBOX
          </div>

          <div className="mdl-textfield mdl-js-textfield textfield-demo">
            <input className="mdl-textfield__input" type="text" id="sample1" />
            <label className="mdl-textfield__label" htmlFor="sample1">SEARCH</label>
          </div>

          <div className="mdl-textfield mdl-js-textfield mdl-textfield--expandable textfield-demo">
            <label className="mdl-button mdl-js-button mdl-button--icon" htmlFor="sample6">
              <i className="material-icons">search</i>
            </label>
            <div className="mdl-textfield__expandable-holder">
              <input className="mdl-textfield__input" type="text" />
              <label className="mdl-textfield__label" htmlFor="sample-expandable">Expandable Input</label>
            </div>
          </div>

          <div className={styles.toolboxItem}>
            foo
          </div>
          <div className={styles.toolboxItem}>
            bar
          </div>

        </div>

        <div className={styles.goal}>
          <div className={styles.header}>
            GOAL
          </div>
          <Signature />
          <div>
            =
          </div>
          <Implementation />
        </div>

      </div>
    );
  }
}


// @connect(state => ({
//   development: state.development,
// }))
// export default class WidgetsContainer {
//   static propTypes = {
//     development: PropTypes.object,
//     dispatch: PropTypes.func.isRequired
//   }

//   static fetchData(store) {
//     if (!isLoaded(store.getState())) {
//       return store.dispatch(loadWidgets());
//     }
//   }

//   render() {
//     const { widgets, error, loading, dispatch } = this.props;
//     return <Widgets widgets={widgets} error={error}
//                     loading={loading} {...bindActionCreators(widgetActions, dispatch)}/>;
//   }
// }
