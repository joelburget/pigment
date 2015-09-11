import Immutable from 'immutable';
import { createStore, applyMiddleware, compose } from 'redux';

import { reader, decoder } from './transit';
import createMiddleware from './clientMiddleware';

export default function createApiClientStore(client, data) {
  const middleware = createMiddleware(client);
  let finalCreateStore;
  if (__DEVELOPMENT__ && __CLIENT__ && __DEVTOOLS__) {
    const { devTools, persistState } = require('redux-devtools');
    finalCreateStore = compose(
      applyMiddleware(middleware),
      devTools(),
      persistState(window.location.href.match(/[?&]debug_session=([^&]+)\b/)),
      createStore
    );
  } else {
    finalCreateStore = applyMiddleware(middleware)(createStore);
  }

  // data is undefined on the server,
  // encoded transit on the client
  //
  // ... that's the idea, anyway.
  // HACK HACK HACK
  var hydrated;
  if (data == null) {
    hydrated = undefined;
  } else {
    hydrated = Object.assign({}, data);
    hydrated.module = decoder.decode(hydrated.module);
  }
  const reducer = require('../ducks/reducer');
  const store = finalCreateStore(reducer, hydrated);
  store.client = client;

  if (__DEVELOPMENT__ && module.hot) {
    module.hot.accept('../ducks/reducer', () => {
      store.replaceReducer(require('../ducks/reducer'));
    });
  }

  return store;
}
