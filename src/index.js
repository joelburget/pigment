// @flow
import { is, Map } from 'immutable';
import React, { PropTypes, Component } from 'react';
import ReactDOM from 'react-dom';

import { IMPLEMENTATION_UPDATED, REFERENCE_UPDATED } from './messages';
import { Module, ModuleTy } from './models/Module';
import { Hole } from './models/Hole';
import Firmament, { UpLevel } from './models/Firmament';
import { Ty } from './models/Ty';
import { row, column } from './styles/flex';
import Memory from './components/Memory';
import Undo from './components/Undo';

import type { Element } from 'react';

import type {
  GlobalContext,
  AnySignal,
  ImplementationUpdatedSignal,
  ReferenceUpdatedSignal,
} from './messages';
import type { Path } from './models/Firmament';


const global0 = new Firmament(Ty, Hole);

const { global: global1, it: rootTyPointer } = global0.newLocation({
  tag: ModuleTy,
  data: new ModuleTy.data(),
  locations: new Map([
    [ UpLevel, { tag: 'IMMEDIATE', location: global0.tyPointer } ]
  ]),
});

const { global: global2, it: rootPointer } = global1.newLocation({
  tag: Module,
  data: new Module.data(),
  locations: new Map([
    [ UpLevel, { tag: 'IMMEDIATE', location: rootTyPointer } ]
  ]),
});


type PageState = {
  globalHistory: Array<Firmament>;
  historyIndex: number;
};


export default class Page extends Component<{}, {}, PageState> {

  constructor() {
    super();
    this.state = {
      globalHistory: [global2],
      historyIndex: 0,
    };
  }

  static childContextTypes = {
    signal: PropTypes.func,
    global: PropTypes.instanceOf(Firmament),
  };

  getChildContext(): GlobalContext<AnySignal> {
    const { globalHistory, historyIndex } = this.state;
    return {
      signal: (path, action) => this.signal(path, action),
      global: globalHistory[historyIndex],
    };
  }

  getGlobal(): Firmament {
    const { globalHistory, historyIndex } = this.state;
    return globalHistory[historyIndex];
  }

  setGlobal(global: Firmament): void {
    const { globalHistory, historyIndex } = this.state;
    const newGlobal = globalHistory.slice(0, historyIndex + 1).concat(global);
    this.setState({
      globalHistory: newGlobal,
      historyIndex: newGlobal.length - 1,
    });
  }

  handleUndo(): void {
    const { historyIndex } = this.state;
    const newIndex = Math.max(0, historyIndex - 1);
    this.setState({ historyIndex: newIndex });
  }

  handleRedo(): void {
    const { globalHistory, historyIndex } = this.state;
    const newIndex = Math.min(globalHistory.length, historyIndex + 1);
    this.setState({ historyIndex: newIndex });
  }

  signal(path: Path, initialAction: AnySignal): void {
    let global = this.getGlobal();

    // set of signals to send before setting state
    let toSignal = [
      [global.followPath(path), { ...initialAction, path }],
    ];

    let p = { root: rootPointer, steps: [UpLevel] };

    while (toSignal.length > 0) {
      const [ [ pointer, signal ], ...toSignal_ ] = toSignal;
      toSignal = toSignal_;
      const loc = global.getLocation(pointer);

      global = loc.signal(global, signal);
      this.setGlobal(global);
      const newVal = global.getLocation(pointer);

      // * check if loc has changed:
      //   - if so, signal every location watching it
      //   - if not, keep updating other locations
      if (!is(newVal, loc)) {
        // step 1
        // update the type of this thing
        const target = global.followPath({
          root: pointer,
          steps: [UpLevel],
        });

        const sig: ImplementationUpdatedSignal = {
          action: IMPLEMENTATION_UPDATED,
          target,
          signal,
        };
        const x = UpLevel;
        // debugger;

        toSignal.push([target, sig]);

        // step 2:
        // find all referers to the updated location
        // XXX target and pointer refer to container and contained respectively
        // I think this should be a different type of signal
        const referers = global.getReferers(pointer);
        Array.prototype.push.apply(
          toSignal,
          referers.map(([ target, name ]) => {
            const sig: ReferenceUpdatedSignal = {
              action: REFERENCE_UPDATED,
              referer: target,
              original: pointer,
              name,
              signal,
            };
            return [target, sig];
          })
        );
      } else {
        console.warn(signal, "doesn't result in update");
      }
    }
  }

  render(): Element {
    const { globalHistory, historyIndex } = this.state;
    const global = this.getGlobal();
    const modPath = { root: rootPointer, steps: [] };

    const ModuleView = global.getPath(modPath).tag.render;

    return (
      <div style={column}>
        <Undo
          globalHistory={globalHistory}
          historyIndex={historyIndex}
          onUndo={() => this.handleUndo()}
          onRedo={() => this.handleRedo()}
        />
        <div style={row}>
          <ModuleView path={modPath} />
        </div>
        <Memory global={global} />
      </div>
    );
  }
}


ReactDOM.render(<Page />, document.getElementById('root'));
