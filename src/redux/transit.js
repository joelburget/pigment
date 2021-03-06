import transit from 'transit-js';

import { writeHandlers as writeHandlers1,
         readHandlers as readHandlers1 } from '../transit-immutable-js';
import { writeHandlers as writeHandlers2,
         readHandlers as readHandlers2 } from '../theory/transit';
import { writeHandlers as writeHandlers3,
         readHandlers as readHandlers3 } from '../aspects/transit';
import { writeHandlers as writeHandlers4,
         readHandlers as readHandlers4 } from '../ducks/module';

const FORMAT = 'json-verbose';

const writeHandlers = transit.map(
  [].concat(
    writeHandlers1,
    writeHandlers2,
    writeHandlers3,
    writeHandlers4
  )
);

const readHandlers = {
  ...readHandlers1,
  ...readHandlers2,
  ...readHandlers3,
  ...readHandlers4,
};

export const writer = transit.writer(FORMAT, { handlers: writeHandlers });

export const reader = transit.reader(FORMAT, { handlers: readHandlers });

export const decoder = transit.decoder({ handlers: readHandlers });
