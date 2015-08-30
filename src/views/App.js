import React, {Component, PropTypes} from 'react';
import {Link} from 'react-router';
import {bindActionCreators} from 'redux';
import {connect} from 'react-redux';
import DocumentMeta from 'react-document-meta';
import {isLoaded as isInfoLoaded, load as loadInfo} from '../ducks/info';
import {isLoaded as isAuthLoaded, load as loadAuth, logout} from '../ducks/auth';
import {createTransitionHook} from '../universalRouter';

const title = 'Pigment';
const description = 'Cooperative Programming';
const image = 'TODO';

const meta = {
  title,
  description,
  meta: {
    charSet: 'utf-8',
    property: {
      'og:site_name': title,
      'og:image': image,
      'og:locale': 'en_US',
      'og:title': title,
      'og:description': description,
      'twitter:card': 'summary',
      'twitter:site': '@erikras',
      'twitter:creator': '@erikras',
      'twitter:title': title,
      'twitter:description': description,
      'twitter:image': image,
      'twitter:image:width': '200',
      'twitter:image:height': '200'
    }
  }
};

@connect(
    state => ({user: state.auth.user}),
    dispatch => bindActionCreators({logout}, dispatch))
export default class App extends Component {
  static propTypes = {
    children: PropTypes.object.isRequired,
    user: PropTypes.object,
    logout: PropTypes.func.isRequired
  }

  static contextTypes = {
    router: PropTypes.object.isRequired,
    store: PropTypes.object.isRequired,
  };

  componentWillMount() {
    const {router, store} = this.context;
    this.transitionHook = createTransitionHook(store);
    router.addTransitionHook(this.transitionHook);
  }

  componentWillReceiveProps(nextProps) {
    if (!this.props.user && nextProps.user) {
      // login
      this.context.router.transitionTo('/loginSuccess');
    } else if (this.props.user && !nextProps.user) {
      // logout
      this.context.router.transitionTo('/');
    }
  }

  componentWillUnmount() {
    const {router} = this.context;
    router.removeTransitionHook(this.transitionHook);
  }

  render() {
    const {user} = this.props;
    const styles = require('./App.scss');
    return (
      <div className={styles.app + " mdl-layout mdl-js-layout mdl-layout--fixed-header"}>
        <nav className="mdl-layout__header">
          <div className="mdl-layout__header-row">
            <Link to="/" className="mdl-layout-title mdl-navigation__link">
              Pigment
            </Link>

            <div className="mdl-layout-spacer" />

            <ul className="mdl-navigation mdl-layout--large-screen-only">
              <li><Link className="mdl-navigation__link" to="/widgets">WIDGETS</Link></li>
              <li><Link className="mdl-navigation__link" to="/survey">SURVEY</Link></li>
              <li><Link className="mdl-navigation__link" to="/about">ABOUT</Link></li>
              <li><Link className="mdl-navigation__link" to="/redirect">REDIRECT</Link></li>
              {!user && <li><Link className="mdl-navigation__link" to="/login">LOGIN</Link></li>}
              {user && <li className="logout-link"><a className="mdl-navigation__link" href="/logout" onClick={::this.handleLogout}>LOGOUT</a></li>}
            </ul>
            {user &&
            <p className={styles.loggedInMessage + ' navbar-text'}>Logged in as <strong>{user.name}</strong>.</p>}
          </div>
        </nav>

        <main className="mdl-layout__content">
          <div className={styles.appContent}>
            {this.props.children}
          </div>
        </main>

      </div>
    );
  }

  handleLogout(event) {
    event.preventDefault();
    this.props.logout();
  }

  static fetchData(store) {
    const promises = [];
    if (!isAuthLoaded(store.getState())) {
      promises.push(store.dispatch(loadAuth()));
    }
    return Promise.all(promises);
  }
}

