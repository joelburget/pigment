// @flow

import { Record } from 'immutable';

import type { Context } from './context';


var shape = Record({ type: null, value: null }, 'evaluationresult');

export class EvaluationResult extends shape {}

export function mkSuccess(e: any): EvaluationResult {
  return new EvaluationResult({
    type: 'success',
    value: e,
  });
}


export function mkStuck(e: any): EvaluationResult {
  return new EvaluationResult({
    type: 'stuck',
    value: e,
  });
}


export function bind(
  e: EvaluationResult,
  f: (value: any) => EvaluationResult): EvaluationResult {
// export function bind(e, f) {
  return e.type === 'success' ? f(e.value) : e;
}
