import { combineReducers } from 'redux';

import auth from './auth';
import module from './module';

export default combineReducers({
  auth,
  module,
});
