// record subtyping

// r1 <=? r2
export function isSubtype(r1: Row, r2: Row) {
  const d1 = r1.description;
  const d2 = r2.description;

  return d1.every((tagTy, tag) => {
    // XXX equals doesn't exist
    return d2.has(k) && d2.get(k).equals(tagTy);
  });
}
