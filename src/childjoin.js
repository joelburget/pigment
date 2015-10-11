import React from 'react';

export default function childJoin(children, joiner) {
  const result = [];
  React.Children.map(children, child => {
    result.push(child);
    result.push(React.cloneElement(joiner));
  });
  result.pop();
  return result;
}
