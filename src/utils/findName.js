export default function findName(list, advice) {
  for (let i = 1;; i++) {
    const name = advice + Array(i).join("'");
    if (!list.includes(name)) {
      return name;
    }
  }
}
