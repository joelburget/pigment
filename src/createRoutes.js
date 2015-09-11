import React from 'react';
import {Route} from 'react-router';

import { App, Module, Home, RequireLogin, Login, LoginSuccess, NotFound } from './containers';

export default function(store) {
  return (
    <Route component={App}>
      <Route path="/" component={Module}/>
      <Route path="/login" component={Login}/>
      <Route component={RequireLogin} onEnter={RequireLogin.onEnter(store)}>
        <Route path="/loginSuccess" component={LoginSuccess}/>
      </Route>
      <Route path="*" component={NotFound}/>
    </Route>
  );
}
