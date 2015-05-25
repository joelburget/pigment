+++
date = "2015-05-25T14:54:46+08:00"
draft = true
title = "navigation"

+++

show up please?

```
[
  A [
    I : S
    \ e : S
    \ f : S
  ] : S
  \ u : S
  \ v : S
  B [
    D := ? : S
    \ x : S
    E [
      \ a : S
      F := ? : S
      \ b : S
    ] : S
    \ y : S
    -= Cursor here =-
    \ z : S
  ] : S
  \ w : S
  C [
    \ g : S
    H := ? : S
    \ h : S
  ] : S
  G := ? : S
]
```

Example

```
[
  A [
    I : S
    \ e : S
    \ f : S
  ] : S
  \ u : S
  \ v : S
  B [
    D := ? : S
    \ x : S
    E [
      \ a : S
      F := ? : S
      \ b : S
    ] : S
    -= Cursor here =-
    \ y : S
    \ z : S
  ] : S
  \ w : S
  C [
    \ g : S
    H := ? : S
    \ h : S
  ] : S
  G := ? : S
]
```

After cursorUp

```
[
  A [
    I : S
    \ e : S
    \ f : S
  ] : S
  \ u : S
  \ v : S
  B [
    D := ? : S
    \ x : S
    E [
      \ a : S
      F := ? : S
      \ b : S
    ] : S
    \ y : S
    \ z : S
    -= Cursor here =-
  ] : S
  \ w : S
  C [
    \ g : S
    H := ? : S
    \ h : S
  ] : S
  G := ? : S
]
```

After cursorDown

```
[
  A [
    I : S
    \ e : S
    \ f : S
  ] : S
  \ u : S
  \ v : S
  B [
    D := ? : S
    \ x : S
    E [
      \ a : S
      F := ? : S
      \ b : S
      -= Cursor here =-
    ] : S
    \ y : S
    \ z : S
  ] : S
  \ w : S
  C [
    \ g : S
    H := ? : S
    \ h : S
  ] : S
  G := ? : S
]
```

After goIn

```
[
  A [
    I : S
    \ e : S
    \ f : S
  ] : S
  \ u : S
  \ v : S
  B [
    D := ? : S
    \ x : S
    E [
      \ a : S
      F := ? : S
      \ b : S
    ] : S
    \ y : S
    \ z : S
  ] : S
  \ w : S
  C [
    \ g : S
    H := ? : S
    \ h : S
  ] : S
  G := ? : S
  -= Cursor here =-
]
```

After goOut

```
[
  A [
    I : S
    \ e : S
    \ f : S
  ] : S
  \ u : S
  \ v : S
  B [
    D := ? : S
    \ x : S
    E [
      \ a : S
      F := ? : S
      \ b : S
    ] : S
    \ y : S
    \ z : S
  ] : S
  -= Cursor here =-
  \ w : S
  C [
    \ g : S
    H := ? : S
    \ h : S
  ] : S
  G := ? : S
]
```

After goOutBelow

```
[
  A [
    I : S
    \ e : S
    \ f : S
    -= Cursor here =-
  ] : S
  \ u : S
  \ v : S
  B [
    D := ? : S
    \ x : S
    E [
      \ a : S
      F := ? : S
      \ b : S
    ] : S
    \ y : S
    \ z : S
  ] : S
  \ w : S
  C [
    \ g : S
    H := ? : S
    \ h : S
  ] : S
  G := ? : S
]
```

After goUp

```
[
  A [
    I : S
    \ e : S
    \ f : S
  ] : S
  \ u : S
  \ v : S
  B [
    D := ? : S
    \ x : S
    E [
      \ a : S
      F := ? : S
      \ b : S
    ] : S
    \ y : S
    \ z : S
  ] : S
  \ w : S
  C [
    \ g : S
    H := ? : S
    \ h : S
    -= Cursor here =-
  ] : S
  G := ? : S
]
```

After goDown
