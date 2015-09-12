import transit from 'transit-js';

import { writeHandlers as theoryWriteHandlers,
         readHandlers as theoryReadHandlers } from '../theory/transit';
import { writeHandlers as immutableWriteHandlers,
         readHandlers as immutableReadHandlers } from '../transit-immutable-js';
import { writeHandlers as moduleWriteHandlers,
         readHandlers as moduleReadHandlers } from '../aspects/module';

const FORMAT = 'json-verbose';

const writeHandlers = transit.map(
  [].concat(
    theoryWriteHandlers,
    immutableWriteHandlers,
    moduleWriteHandlers
  )
);

const readHandlers = {
  ...theoryReadHandlers,
  ...immutableReadHandlers,
  ...moduleReadHandlers,
};

export const writer = transit.writer(FORMAT, { handlers: writeHandlers });

export const reader = transit.reader(FORMAT, { handlers: readHandlers });

export const decoder = transit.decoder({ handlers: readHandlers });
