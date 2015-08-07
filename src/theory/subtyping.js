// Define two subtyping relations -- leq+, leq- -- as well as leq+- for when
// both types are neither positive nor negative.
//
// functions and guarded types are negative
// sums, products, and assertions are positive

const plus = {};
const minus = {};
const plusminus = {};

function nonneg(t) {
}

function nonpos(t) {
}

const Subtype = Record({ type: null, l: null, r: null });

// leq Refl +-
function leqReflIntro(A, pf1, pf2, pf3) {
  return new Subtype({ type: "+-", l: A, r: A });
}

// leq -+
function leqMPIntro(A, B, pf1, pf2, pf3) {
  return new Subtype({ type: "+", l: A, r: B });
}

// leq +-
function leqPMIntro(A, B, pf1, pf2, pf3) {
  return new Subtype({ type: "-", l: A, r: B });
}

// leq forall L
// function leqForallLIntro(A, B, tau, pf) {
//   return new Subtype({ type: "-", forall(
// }

// leq forall R

// leq exists L

// leq exists R

