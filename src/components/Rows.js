// @flow
import React, { PropTypes } from 'react';

// import PokeHoleButton from '../actions/poke_hole';
// import { DeleteButton } from '../actions/remove_field';

import Firmament from '../models/Firmament';

import { row, column } from '../styles/flex';
import { borderGray } from '../styles/color';

import type { Element } from 'react';
import type Immutable from 'immutable';

import type { SubLocation } from '../messages';
import type { Path, Step } from '../models/Firmament';

type Props = {
  fields: Immutable.List<string>;
  locations: Immutable.Map<Step, SubLocation>;
  path: Path;
};

// TODO - Locations should align on the left and right sides.
export default function Rows(
  { fields, locations, path }: Props,
  { global }: { global: Firmament }
): Element {
  const rows = fields
    .map(key => {
      const subLoc: SubLocation = locations.get(key);

      let subRender: ?Element = null;
      if (subLoc.tag === 'IMMEDIATE') {
        const path_ = {
          root: path.root,
          steps: path.steps.concat(key),
        };
        const rowLoc = global.getPath(path_);
        const RowComponent = rowLoc.tag.render;
        subRender = <RowComponent path={path_} />;
      } else { // 'REFERENCE'
        subRender = (
          <div>{subLoc.name}</div>
        );
      }

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
              {subRender}
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
