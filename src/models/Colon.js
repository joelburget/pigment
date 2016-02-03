// @flow
import React, { Component } from 'react';
import { Record } from 'immutable';

import { INTRODUCTION } from '../messages';

import type { Path } from './Firmament';


const COLON = Symbol('COLON');


const ColonData = Record();


class ColonView extends Component<{}, {path: Path}, {}> {
  render(): Element {
    const { global } = this.context;
    const { path } = this.props;

    // This is a little weird. We shouldn't have to add any locations for a
    // colon, but since we want its type and term children's paths to remain
    // intact, we need to add them to locations.
    const { locations } = global.getPath(path);
    const term = locations.get('term');
    const type = locations.get('type');

    const TermComponent = term.tag.render;
    const TypeComponent = type.tag.render;

    const termPath = {
      root: path.root,
      steps: path.steps.concat('term'),
    };

    const typePath = {
      root: path.root,
      steps: path.steps.concat('type'),
    };

    return (
      <div>
        <TermComponent path={termPath} />
        <div>:</div>
        <TypeComponent path={typePath} />
      </div>
    );
  }
}


export const Colon = {
  name: 'Colon',
  symbol: COLON,
  type: INTRODUCTION,

  // is this right? the colon spans levels.
  minLevel: 0,
  handlers: {
  },
  render: ColonView,
  data: ColonData,
};
