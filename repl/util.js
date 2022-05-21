import * as we from "text-encoding";

export var TextEncoder = we.TextEncoder;
export var TextDecoder = we.TextDecoder;
export var isString = function(s) { return typeof(s) === 'string'; }
