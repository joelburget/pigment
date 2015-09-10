import React from 'react';
import {Route} from 'react-router';

import { App, Home, Login, LoginSuccess, NotFound } from 'containers';
// import Home from 'views/Home';
// import Module from 'views/Module';
// import Login from 'views/Login';
// import RequireLogin from 'views/RequireLogin';
// import LoginSuccess from 'views/LoginSuccess';
// import NotFound from 'views/NotFound';

export default function(store) {
  return (
    <Route component={App}>
      <Route path="/" component={Home}/>
      <Route path="/login" component={Login}/>
      <Route component={RequireLogin} onEnter={RequireLogin.onEnter(store)}>
        <Route path="/loginSuccess" component={LoginSuccess}/>
      </Route>
      <Route path="*" component={NotFound}/>
    </Route>
  );
}
