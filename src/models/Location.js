// @flow
import { Map, Record } from 'immutable';

import type Firmament from './Firmament';
import type { AnySignal } from '../messages';


export class Location extends Record({
  tag: null,
  locations: new Map(),
  data: null,
}) {

  signal(global: Firmament, sig: AnySignal): Location {
    const handler = this.tag.handlers[sig.action];
    const tyName = this.tag.symbol.toString();

    if (sig.action === 'POKE_HOLE') {
      // TODO: what is path used for? is it redundant in the presence of loc?
      // Isn't global.getLocation(sym) always this?
      // const { path } = sig;
      // const sym = global.getPath(path);

      // hole data is empty
      // XXX this needs updated
      // return global.getLocation(sym).merge({ tag: Hole });
      return global;

    } else if (handler) {
      return handler(global, sig);

    } else { // eslint-disable-line no-else-return
      console.warn( // eslint-disable-line no-console
        `Warning: unhandled signal: ${tyName}: ${sig.action.toString()}`,
        sig,
        this.toJS()
      );

      // just return the same old thing
      return global;
    }
  }

  // need to add watching / event bubbling
}
