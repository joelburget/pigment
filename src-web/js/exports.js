import React from 'react';

import PageLayout from './view/PageLayout';
import * as editor from './view/Editor';
import * as messages from './view/Messages';
import * as history from './view/History';
import * as data from './view/Data';

// ghcjs can only access this as a global
window.React = React;

module.exports = {
  PageLayout,
  ...editor,
  ...messages,
  ...history,
  ...data,
};
