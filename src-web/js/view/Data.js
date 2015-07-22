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


// TODO:
// * button to add (/remove) a type parameter
//   - this should allow them to be annotated with their kind
//     (or inferred as Set) if it's left off?
// * button to add (/remove) a constructor (or modifying?)
//   - this should autocomplete from the type parameters and types in scope:
//
//       a_
//     -----------------------
//     | a      type parameter
//     | arrow  in scope
//     | align  in scope
//     | ...
//
// * A big thing to think about is how breaking changes are handled. Sure,
// we're fine if this thing isn't yet used. Punting on this for now, but I picture it opening a mode where you can resolve all the issues. Would be nice if you could bundle all changes to a data type, for instance:
//   - "unlock"
//   - make your changes - adding and removing params / ctors
//   - "finish"
//   - resolve (I imagine something like
//     http://unisonweb.org/2015-06-12/editing.html#post-start)
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
