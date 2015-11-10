import { List, Map } from 'immutable';

export default class Firmament<A> {
  map: Map<A>;

  constructor(map: Map<List<string>, A>): void {
    this.map = map;
  }

  get(path: Array<string>): ?A {
    return this.map.get(List(path));
  }

  set(path: Array<string>, value: A): void {
    const newMap = this.map.set(List(path), value);
    return new Firmament(newMap);
  }

  // TODO we should also build in garbage collection
}

export function fromBaseLocation<A>(baseLocation: A): Firmament<A> {
  const map = Map([
    [List([]), baseLocation]
  ]);
  return new Firmament(map);
}
