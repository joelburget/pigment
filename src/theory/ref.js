// @flow
//
// global reference

import { List, Record, is } from 'immutable';

export class RelRef extends Record({ path: null }) {
  normalize(): RelRef {
    var stack = [];
    var last = '..';

    this.path.forEach(piece => {
      if (piece === '..' && last !== '..') {
        stack.pop();
      } else {
        stack.push(piece);
      }
      last = piece;
    });

    var path = List(stack);
    return new RelRef({ path });
  }

  extend(ref: RelRef): RelRef {
    var path = this.path.concat(ref.path);
    return new RelRef({ path }).normalize();
  }

  is(ref: Ref, root: AbsRef): boolean {
    if (ref instanceof RelRef) {
      return is(this.normalize().path, ref.normalize().path);
    } else {
      return is(
        root.extend(this).normalize().path,
        ref.normalize().path
      );
    }
  }

  goIn(): RelRef {
    return mkRel('..').extend(this);
  }
}


export class AbsRef extends Record({ path: null }) {
  normalize(): AbsRef {
    var relNormalized = new RelRef({ path: this.path }).normalize();
    var path = relNormalized.path;

    if (path.get(0) === '..') {
      throw new Error('AbsRef.normalize went below root');
    } else {
      return new AbsRef({ path });
    }
  }

  relativize(root: RelRef): RelRef {
    var path = root.path.concat(this.path);
    return new RelRef({ path }).normalize();
  }

  extend(ref: RelRef): AbsRef {
    var path = this.path.concat(ref.path);
    return new AbsRef({ path }).normalize();
  }

  is(ref: Ref, root: AbsRef): boolean {
    if (ref instanceof AbsRef) {
      return is(this.normalize().path, ref.normalize().path);
    } else {
      return is(
        root.extend(ref).normalize().path,
        this.normalize().path
      );
    }
  }

  goIn(): AbsRef {
    return this;
  }
}

export type Ref = RelRef | AbsRef;


export function mkRel(...parts: Array<string>): RelRef {
  var path = List(parts);
  return new RelRef({ path });
}


export function mkAbs(...parts: Array<string>): AbsRef {
  var path = List(parts);
  return new AbsRef({ path });
}
