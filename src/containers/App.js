import React, {Component, PropTypes} from 'react';
import {Link} from 'react-router';
import {bindActionCreators} from 'redux';
import {connect} from 'react-redux';
import DocumentMeta from 'react-document-meta';
import EventPluginHub from 'react/lib/EventPluginHub';
import TapEventPlugin from 'react/lib/TapEventPlugin';

import Avatar from '../components/Avatar';
import {isLoaded as isAuthLoaded, load as loadAuth, logout} from '../ducks/auth';
import styles from './App.scss';

EventPluginHub.injection.injectEventPluginsByName({ TapEventPlugin });

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
      'twitter:site': '@pigmentio',
      'twitter:creator': '@pigmentio',
      'twitter:title': title,
      'twitter:description': description,
      'twitter:image': image,
      'twitter:image:width': '200',
      'twitter:image:height': '200',
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
    logout: PropTypes.func.isRequired,
    history: PropTypes.object,
  }

  static contextTypes = {
    store: PropTypes.object.isRequired,
  };

  componentWillReceiveProps(nextProps) {
    if (!this.props.user && nextProps.user) {
      // login
      this.props.history.pushState(null, '/loginSuccess');
    } else if (this.props.user && !nextProps.user) {
      // logout
      this.props.history.pushState(null, '/');
    }
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

  render() {
    const {user} = this.props;
    return (
      <div className={styles.app}>
        <DocumentMeta {...meta} />
        <nav>
          <div>
            <Link to='/' className={styles.title}>
              Pigment
            </Link>
          </div>

          <div className={styles.login}>
            {user &&
            /* <p className={styles.loggedInMessage + ' navbar-text'}>Logged in as <strong>{user.name}</strong>.</p> */
            <Avatar fbId='joelburget' round='true' size={40} />}
            <div>
              {!user && <Link to='/login'>LOGIN</Link>}
              {user && <a href='/logout' onClick={::this.handleLogout}>LOGOUT</a>}
            </div>
          </div>

          <div className={styles.module}>
            MODULE
              <ul className={styles.subModule}>
                <li className={styles.hole}>2 holes remaining</li>
                <li className={styles.conflict}>3 conflicts remaining</li>
                <li className={styles.history}>history</li>
              </ul>
          </div>
        </nav>

        <main>
          <div className={styles.appContent}>
            {this.props.children}
          </div>
        </main>

      </div>
    );
  }
}

