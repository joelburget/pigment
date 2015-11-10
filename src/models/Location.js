import { Record } from 'immutable';

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

  signal(global, action) {
    return this.type.receiveSignal(global, action);
  }
}
