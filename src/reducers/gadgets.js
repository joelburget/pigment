/* eslint new-cap: 0 */
import { Record, RecordTy, Documentation, Location } from '../models/Gadget';
import { NEW_GADGET, NEW_SLOT, REMOVE_SLOT } from '../actions/gadgets';
import findName from '../utils/findName';

// metaobject protocol: track metadata like:
// * type
// * documentation
// * performance characteristics
// * test coverage
// * effects
//
// and open them up to inform the term.
//
// question: it seems clear how types can constrain terms. how do terms
// constrain types.
//
// question: why is the term somehow elevated? why not do
//
// {
//   implementation:
//   type:
//   documentation:
//   performance:
//   coverage:
//   effects:
//   tests:
// }
//
// all colocated?

const initialState = undefined;

export default function gadgets(state = initialState, action) {
  switch (action.type) {

    // these next three are really Gadget.implementation messages!
  case NEW_GADGET: {
    // XXX how is this different than NEW_SLOT?
    const { name } = action;
    // XXX give it a type
    return state.set(findName(state, name), new Location());
  }

  case NEW_SLOT: {
    // XXX give it a type
    const { path, name } = action;
    const newName = findName(state.getIn(path), name);
    const newPath = path.concat('implementation', 'fields', newName);
    return state.setIn(newPath, new Location());
  }
  case REMOVE_SLOT: {
    const { path } = action;
    return state.deleteIn(path);
  }

  // TODO
  case 'MESSAGE': {
    // what messages can be sent?
    // * governed by the type!
    // can ask advice up or down, right?
    const { path, message } = action;
    const termPieces = state.getIn(path);

    // we don't allow receipt of a message to cause a new message
    // * this is to prevent runaway message chains
    // * in other words, only human action causes messages
    state.setIn(
      path,
      termPieces.map(termPiece => termPiece.receiveMessage(message))
    );
  }
  default:
    return state;
  }
}
