import transit from 'transit-js';

import { writeHandlers as theoryWriteHandlers,
         readHandlers as theoryReadHandlers } from '../theory/transit';
import { writeHandlers as immutableWriteHandlers,
         readHandlers as immutableReadHandlers } from '../transit-immutable-js';
import { writeHandlers as widgetWriteHandlers,
         readHandlers as widgetReadHandlers } from '../ducks/module';

const FORMAT = 'json-verbose';

const writeHandlers = transit.map(
  [].concat(
    theoryWriteHandlers,
    immutableWriteHandlers,
    widgetWriteHandlers
  )
);

const readHandlers = {
  ...theoryReadHandlers,
  ...immutableReadHandlers,
  ...widgetReadHandlers,
};

export const writer = transit.writer(FORMAT, { handlers: writeHandlers });

export const reader = transit.reader(FORMAT, { handlers: readHandlers });

export const decoder = transit.decoder({ handlers: readHandlers });
