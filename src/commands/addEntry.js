export const ADD_ENTRY = 'ADD_ENTRY';

export const addEntry = {
  id: ADD_ENTRY,
  title: 'add entry',
};

export function makeLabel(values) {
  const labelPrefix = 'new entry';
  let label = labelPrefix;
  let ix = 0;
  while (values.has(label)) {
    ix += 1;
    label = labelPrefix + ' ' + ix;
  }

  return label;
}
