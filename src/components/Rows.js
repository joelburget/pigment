import React, { PropTypes } from 'react';

// import PokeHoleButton from '../actions/poke_hole';
// import { DeleteButton } from '../actions/remove_field';

import Firmament from '../models/Firmament';

import { row, column } from '../styles/flex';
import { borderGray } from '../styles/color';

export default function Rows({ fields, path }, { global, signal }) {
  const rows = fields
    .map(key => {
      // TODO - Locations should align on the left and right sides.
      const path_ = {
        root: path.root,
        steps: path.steps.concat(key),
      };
      const rowLoc = global.getPath(path_);
      const RowComponent = rowLoc.tag.render;

      return (
        <div style={styles.row} key={key}>
          <div style={styles.header}>
            {key}:
          </div>
          <div style={styles.belowHeader}>
            {/*
            <div style={styles.controls}>
              <div style={styles.controlHeader}>
                controls
              </div>
              <div style={styles.controlBody}>
                <DeleteButton path={path} name={key} />
                <PokeHoleButton path={path_} />
              </div>
            </div>
            */}
            <div style={styles.body}>
              <RowComponent path={path_} />
            </div>
          </div>
        </div>
      );
    })
    .toArray();

  return (
    <div style={styles.rows}>
      {rows}
    </div>
  );
}


Rows.contextTypes = {
  global: PropTypes.instanceOf(Firmament).isRequired,
};


const styles = {
  rows: {
    ...column,
    marginLeft: 10,
  },
  row: {
    ...column,
  },
  header: {
    borderBottom: `1px solid ${borderGray}`,
    padding: '5px 0',
    marginBottom: 5,
  },
  belowHeader: {
    ...row,
  },
  controls: {
    ...column,
    borderRight: `1px solid ${borderGray}`,
  },
  controlHeader: {
    // margin: '0 auto',
  },
  controlBody: {
    ...row,
  },
  body: {
    padding: 5,
  },
};
