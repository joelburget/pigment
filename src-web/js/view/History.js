import React from 'react';

export default class HistoryView extends React.Component {
  render() {
    return <div>
      <HistoryViewHeader />

    </div>;
  }
}

class HistoryViewHeader extends React.Component {
  render() {
    return <span>HISTORY VIEW</span>;
  }
}
