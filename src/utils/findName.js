export default function findName(container, advice) {
  for (let i = 1;; i++) {
    const name = advice + Array(i).join("'");
    if (!container.has(name)) {
      return name;
    }
  }
}
