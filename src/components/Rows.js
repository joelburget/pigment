import React, { PropTypes } from 'react';

import PokeHoleButton from '../actions/poke_hole';
import { DeleteButton } from '../actions/remove_field';
import { NewField } from '../actions/new_field';

import Firmament from '../models/Firmament';

import { row, column } from '../styles/flex';

export default function Rows({ fields, path }, { global }) {
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
        <div style={row} key={key}>
          <DeleteButton path={path} name={key} />
          <PokeHoleButton path={path_} />
          <div>
            {key}:
            <RowComponent path={path_} />
          </div>
        </div>
      );
    })
    .toArray();

  return (
    <div style={column}>
      {'{'}
      <div style={rowsStyle}>
        {rows}
      </div>
      <NewField path={path} />
      {'}'}
    </div>
  );
}


Rows.contextTypes = {
  global: PropTypes.instanceOf(Firmament).isRequired,
};


const rowsStyle = {
  ...column,
  marginLeft: 10,
};
