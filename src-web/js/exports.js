import PageLayout from './view/PageLayout';
import * as commandLine from './view/CommandLine';
import * as editor from './view/Editor';
import * as messages from './view/Messages';
import * as history from './view/History';

module.exports = {
  PageLayout,
  ...commandLine,
  ...editor,
  ...messages,
  ...history,
};
