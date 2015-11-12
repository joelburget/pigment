import { Record } from 'immutable';


import { implementationHole, typeHole } from './Hole';


export const Documentation = Record({
  docs: ''
});


export class Location extends Record({
  implementation: null,
  implementationView: null,
  type: null,
  typeView: null,
  documentation: new Documentation(),
}) {

  signal(global, sig) {
    const handler = this.type.handlers[sig.action];
    const tyName = this.type.constructor.name;

    if (sig.action === 'POKE_HOLE') {
      const { path } = sig;
      const hole = sig.level === 0 ? implementationHole : typeHole;

      const loc = global.get(path);
      const loc_ = loc.merge(hole);

      return global.set(sig.path, loc_);

    } else if (handler) {
      return handler(global, sig);

    } else { // eslint-disable-line no-else-return
      console.warn( // eslint-disable-line no-console
        `Warning: unhandled signal: ${tyName}: ${sig.action}`,
        sig
      );
      return global;
    }
  }
}
