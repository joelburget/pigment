export default function upcast(x, cls) {
  if (x instanceof cls) {
    return (x: cls);
  } else {
    throw new Error('failed upcast!');
  }
}
