module Keyboard where

data Key = Enter | Tab | ArrowUp | Arrowdown

data KeyboardEvent
    { key :: Key
    }
