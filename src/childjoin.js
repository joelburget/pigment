import React from 'react';

export default function childJoin(xs, joiner) {
  let result = [];
  React.Children.map(xs, x => {
    result.push(x);
    result.push(React.cloneElement(joiner));
  });
  result.pop();
  return result;
}
