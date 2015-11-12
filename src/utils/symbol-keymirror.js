export default function symbolKeymirror(obj) {
  const ret = {};
  Object.keys(obj, key => {
    const desc = obj[key];
    const symbol = Symbol(desc);
    ret[key] = symbol;
  });
  return ret;
}
