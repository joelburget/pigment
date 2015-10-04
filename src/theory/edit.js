// @flow
//
// An edit ideally documents the intention of an edit, or at least some
// approximation to that.
//
// Storing:
// * The original state of the world (!)
//   - Would be nice if this pointed to some persisted point (ie on a server)
//   - Lacking that we're earnestly pointing to the immutable state of the
//     world
// * The original edit command
// * Resulting edits
//
// What if the resulting edits aren't yet resolved?

import { List, Record } from 'immutable';

import type { AbsRef } from './ref';


export type Action = {
  id: string;
  title: string;
  value?: any;
}


export var OPEN = 'OPEN';
export var CLOSED = 'CLOSED';


// An edit describes some user-initiated change (the catalyst), and all the
// conflicts that resulted from that change (along with their solutions).
var EditShape = Record({
  status:   null, // OPEN | CLOSED

  // Where did this take place and what was the intent of the command.
  // Catalyzes a chain of edits (closure).
  catalyst: null, // string (action id)

  before: null, // Tm
  after: null, // Tm

  // solutions to resulting problems
  //
  // Question:
  //   Why is this recursive? IE why do we build a tree of edits rather than
  //   flattening all transitive conflicts into a list?
  //
  // Answer:
  //   Because the transitive edits don't yet exist when this structure is
  //   first created. We're talking about conflicts that come into existence,
  //   then leave existence over the course of this edit being built. We need
  //   more structure so we can talk about the edits that exist at a given
  //   time / frontier.
  closure:  null, // List<Edit>
});


export default class Edit extends EditShape {
  resolved(): boolean {
    return this.status === CLOSED ||
           this.closure.size() === 0 ||
           this.closure.every(edit => edit.resolved());
  }

  // resolve(
}


export function openNewEdit(catalyst: string,
                            before: Tm,
                            after: Tm,
                            closure: List<Edit>): Edit {

  var status = closure.count() === 0 ? CLOSED : OPEN;

  return new Edit({
    status,
    catalyst,
    before,
    after,
    closure,
  });
}


export function attemptCloseEdit(edit: Edit): Edit {
  return edit.resolved ?
    edit.set('status', CLOSED) :
    edit;
}
