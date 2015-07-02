{-# LANGUAGE ForeignFunctionInterface, JavaScriptFFI, CPP #-}

module Cochon.Imports where

import React

import Cochon.Model

#ifdef __GHCJS__
foreign import javascript "window.PigmentView.PageLayout"
    pageLayout :: ImportedClass Transition
#else
pageLayout :: ImportedClass Transition
pageLayout = error "pageLayout not available from ghc"
#endif
