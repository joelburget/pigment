import { combineReducers } from 'redux';

import auth from './auth';

// XXX this should not be a reducer!
import module from '../aspects/module';

export default combineReducers({
  auth,
  module,
});
