export default function symbolKeymirror(obj) {
  const ret = {};
  Object.keys(obj).map(key => {
    ret[key] = Symbol(key);
  });
  return ret;
}
