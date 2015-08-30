var NAME_KEY = '_name';

export type TmRecordEntry = { _name: string }

var registry = {};

export function register(name: string, cls: any): void {
  registry[name] = cls;
}

export function deserialize(obj: TmRecordEntry): any {
  var name = obj[NAME_KEY];

  var withoutName = {};
  Object.keys(obj).forEach(key => {
    if (key !== NAME_KEY) {
      var value = obj[key];

      withoutName[key] = value.has(NAME_KEY) ? deserialize(value) : value;
    }
  });
  delete withoutName[NAME_KEY];

  return new registry[name](withoutName);
}
