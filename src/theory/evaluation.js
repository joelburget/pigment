// @flow

import { Record } from 'immutable';


export class EvaluationResult extends Record({
  type: null,  // string
  value: null, // X
}, 'evaluationresult') {}


export function mkSuccess(value: any): EvaluationResult {
  return new EvaluationResult({
    type: 'success',
    value,
  });
}


export function mkStuck(value: any): EvaluationResult {
  return new EvaluationResult({
    type: 'stuck',
    value,
  });
}


export function bind(
  result: EvaluationResult,
  fun: (value: any) => EvaluationResult): EvaluationResult {
  return result.type === 'success' ? fun(result.value) : result;
}
