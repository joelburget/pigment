import React from 'react';

import PageLayout from './view/PageLayout';
import * as commandLine from './view/CommandLine';
import * as editor from './view/Editor';
import * as messages from './view/Messages';
import * as history from './view/History';

// ghcjs can only access this as a global
window.React = React;

module.exports = {
  PageLayout,
  ...commandLine,
  ...editor,
  ...messages,
  ...history,
};
