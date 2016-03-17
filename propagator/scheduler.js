export default class Scheduler {
  constructor() {
    this.alertedPropagators = {};
    this.alertedPropagatorList = [];
    // abortProcess, lastValueOfRun, propagatorsEverAlerted / *List
  }

  alertPropagators(jobs) {
    for (let propagator of jobs) {
      propagator();
    }
  }

  run() {
  }

  // abortProcess
}
