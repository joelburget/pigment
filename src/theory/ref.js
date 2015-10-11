// @flow
//
// global reference

import { List, Record, is } from 'immutable';

// TODO come to terms with the fact that these '..'s are de bruijn indices
export class RelRef extends Record({ path: null }) {
  normalize(): RelRef {
    const stack = [];
    let last = '..';

    this.path.forEach(piece => {
      if (piece === '..' && last !== '..') {
        stack.pop();
      } else {
        stack.push(piece);
      }
      last = piece;
    });

    const path = List(stack);
    return new RelRef({ path });
  }

  extend(ref: RelRef): RelRef {
    const path = this.path.concat(ref.path);
    return new RelRef({ path }).normalize();
  }

  is(ref: Ref, root: AbsRef): boolean {
    return is(
      ref instanceof RelRef ?
        this.normalize().path :
        root.extend(this).normalize().path,
      ref.normalize().path
    );
  }

  goIn(): RelRef {
    return new RelRef({ path: '..' }).extend(this);
  }
}


export class AbsRef extends Record({ path: null }) {
  normalize(): AbsRef {
    const relNormalized = new RelRef({ path: this.path }).normalize();
    const path = relNormalized.path;

    if (path.get(0) === '..') {
      throw new Error('AbsRef.normalize went below root');
    } else {
      return new AbsRef({ path });
    }
  }

  relativize(root: RelRef): RelRef {
    const path = root.path.concat(this.path);
    return new RelRef({ path }).normalize();
  }

  extend(ref: RelRef): AbsRef {
    const path = this.path.concat(ref.path);
    return new AbsRef({ path }).normalize();
  }

  is(ref: Ref, root: AbsRef): boolean {
    return is(
      ref instanceof AbsRef ?
        this.normalize().path :
        root.extend(this).normalize().path,
      ref.normalize().path
    );
  }

  goIn(): AbsRef {
    return this;
  }
}


export type Ref = RelRef | AbsRef;


// export function mkRel(...parts: Array<string>): RelRef {
//   const path = List(parts);
export function mkRel(): RelRef {
  const path = List(arguments);
  return new RelRef({ path });
}


// export function mkAbs(...parts: Array<string>): AbsRef {
//   const path = List(parts);
export function mkAbs(): AbsRef {
  const path = List(arguments);
  return new AbsRef({ path });
}
