import Radium from 'radium';
import React from 'react';
import * as MaterialUI from 'material-ui';
import { getChildren, reactJoin } from './util';


const styles = {
  dataConstructor: {
    ':hover': {
      backgroundColor: '#ddd',
    },
  },

  data: {
    display: 'flex',
    flexDirection: 'column',
  },

  infoRow: {
    display: 'flex',
    flexDirection: 'column',
  },

  infoHeader: {
    fontWeight: 'bold',
  },

  infoSubHeader: {
    marginLeft: 10,
  },

  infoTable: {
    borderCollapse: 'collapse',
    marginLeft: 10,
  },

  tableRow: {
    borderBottom: '2px solid #bbb',
  },

  tableItem: {
    paddingLeft: 10,
  },
};


@Radium
export class DataConstructorLayout extends React.Component {
  render() {
    const { name, scheme, result } = this.props;

    return (
      <tr style={styles.tableRow}>
        <td>{name}</td>
        <td style={styles.tableItem}>:</td>
        <td style={styles.tableItem}>{scheme}</td>
        <td style={styles.tableItem}>-></td>
        <td style={styles.tableItem}>{result}</td>
      </tr>
    );
  }
}


export class DataLayout extends React.Component {
  render() {
    // TODO replace by term
    const ty = "Either a b";

    return (
      <div style={styles.data}>
        <div style={styles.infoRow}>
          <div style={styles.infoHeader}>type</div>
          <div style={styles.infoSubHeader}>
            {ty}
          </div>
        </div>
        <div style={styles.infoRow}>
          <div style={styles.infoHeader}>constructors</div>
          <table style={styles.infoTable}>
            <tbody>
              <DataConstructorLayout name="Left" scheme="a" result={ty} />
              <DataConstructorLayout name="Right" scheme="b" result={ty} />
            </tbody>
          </table>
        </div>
      </div>
    );
  }
}
