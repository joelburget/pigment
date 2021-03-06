// import Auth0LockPasswordless from 'auth0-lock-passwordless';

const LOAD = 'pigment/auth/LOAD';
const LOAD_SUCCESS = 'pigment/auth/LOAD_SUCCESS';
const LOAD_FAIL = 'pigment/auth/LOAD_FAIL';
const LOGIN = 'pigment/auth/LOGIN';
const LOGIN_SUCCESS = 'pigment/auth/LOGIN_SUCCESS';
const LOGIN_FAIL = 'pigment/auth/LOGIN_FAIL';
const LOGOUT = 'pigment/auth/LOGOUT';
const LOGOUT_SUCCESS = 'pigment/auth/LOGOUT_SUCCESS';
const LOGOUT_FAIL = 'pigment/auth/LOGOUT_FAIL';

// const clientId = '0jfYz9zpjXZ4W0b5HMwiTnWVRrUkPkRJ';
// const authDomain = 'joel.auth0.com';
// const lock = new Auth0LockPasswordless(clientId, authDomain);

// const linkOptions = {
//   responseType: 'token',
// };

// // popup mode. relevant detail is we pass in a callback and get the jwt back as
// // id_token.
// lock.magiclink(linkOptions, (err, profile, id_token) => {
//   if (err) {
//     console.log("There was an error :/", err);
//     return;
//   }

//   console.log("Hey dude", profile);
// });

const initialState = {
  loaded: false,
  loading: false,
  loggingIn: false,
  loggingOut: false,

  user: null,
  jwt: null,

  loginError: null,
  logoutError: null,
};

export default function reducer(state = initialState, action = {}) {
  switch (action.type) {
    case LOAD:
      return {
        ...state,
        loading: true
      };
    case LOAD_SUCCESS:
      return {
        ...state,
        loading: false,
        loaded: true,
        user: action.result
      };
    case LOAD_FAIL:
      return {
        ...state,
        loading: false,
        loaded: false,
        error: action.error
      };
    case LOGIN:
      return {
        ...state,
        loggingIn: true
      };
    case LOGIN_SUCCESS:
      return {
        ...state,
        loggingIn: false,
        user: action.result
      };
    case LOGIN_FAIL:
      return {
        ...state,
        loggingIn: false,
        user: null,
        loginError: action.error
      };
    case LOGOUT:
      return {
        ...state,
        loggingOut: true
      };
    case LOGOUT_SUCCESS:
      return {
        ...state,
        loggingOut: false,
        user: null
      };
    case LOGOUT_FAIL:
      return {
        ...state,
        loggingOut: false,
        logoutError: action.error
      };
    default:
      return state;
  }
}

export function isLoaded(globalState) {
  return globalState.auth && globalState.auth.loaded;
}

export function load() {
  return {
    types: [LOAD, LOAD_SUCCESS, LOAD_FAIL],
    promise: (client) => client.get('/loadAuth')
  };
}

export function login(name) {
  return {
    types: [LOGIN, LOGIN_SUCCESS, LOGIN_FAIL],
    promise: (client) => client.post('/login', {
      data: {
        name: name
      }
    })
  };
}

export function logout() {
  return {
    types: [LOGOUT, LOGOUT_SUCCESS, LOGOUT_FAIL],
    promise: (client) => client.get('/logout')
  };
}
