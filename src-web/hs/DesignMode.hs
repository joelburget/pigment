{-# LANGUAGE RebindableSyntax, OverloadedStrings #-}
module Main (main) where

import Prelude hiding ((>>), return)

import Data.String
import Data.Void
import React
import React.DOM
import React.GHCJS
import React.Rebindable

import Cochon.Imports
import Cochon.Model
import Cochon.Reactify
import DisplayLang.DisplayTm
import Evidences.Tm


page_ :: () -> ReactNode Void
page_ = classLeaf $ smartClass
    { React.name = "page"
    , transition = \(state, sig) -> (state, Nothing)
    , renderFn = \_ _ -> div_ [] $ do
          h1_ [] "Design Mode!"
          pairs_
          sigmas_
          pis_
          scopes_
          dataLayouts_
    }

-- relnames_ = div_ [] $ do

pairs_ :: ReactNode TermTransition
pairs_ = div_ [ class_ "demo" ] $ do
    h2_ [] "pairs"

    "DVOID"
    pair_ DVOID

    "DPAIR DUNIT (DPAIR DUNIT (DPAIR DUNIT DVOID))"
    pair_ $ DPAIR DUNIT (DPAIR DUNIT (DPAIR DUNIT DVOID))

    "DPAIR (DPAIR DUNIT DVOID) (DPAIR DUNIT DVOID)"
    pair_ $ DPAIR (DPAIR DUNIT DVOID) (DPAIR DUNIT DVOID)


sigmas_ :: ReactNode TermTransition
sigmas_ = div_ [ class_ "demo" ] $ do
    h2_ [] "sigmas"

    "DUNIT"
    sigma_ DUNIT

    "DSIGMA (DL \"x\" ::. DUNIT)"
    sigma_ $ DSIGMA DUNIT (DL ("x" ::. DUNIT))

    "DSIGMA (DL (DK DUNIT))"
    sigma_ $ DSIGMA DUNIT (DL (DK DUNIT))

    "DSIGMA DUNIT DUNIT"
    sigma_ $ DSIGMA DUNIT DUNIT


pis_ :: ReactNode TermTransition
pis_ = div_ [ class_ "demo" ] $ do
    h2_ [] "pis"

    "DARR DUNIT DUNIT"
    pi_ $ DARR DUNIT DUNIT

    "DPI DUNIT (DLK DUNIT)"
    pi_ $ DPI DUNIT (DLK DUNIT)

    "DPI DUNIT (DL (\"unit\" ::. DUNIT))"
    pi_ $ DPI DUNIT (DL ("unit" ::. DUNIT))


scopes_ :: ReactNode TermTransition
scopes_ = div_ [ class_ "demo" ] $ do
    h2_ [] "scopes"

    "DLK DUNIT"
    dInTmRN_ $ DLK DUNIT

    "DL (\"x\" ::. DUNIT)"
    dInTmRN_ $ DL ("x" ::. DUNIT)

    "DL (\"x\" ::. (DL (\"y\" ::. (DL (\"z\" ::. DUNIT)))))"
    dInTmRN_ $ DL ("x" ::. (DL ("y" ::. (DL ("z" ::. DUNIT)))))

-- cans_ = div_ [] $ do
--     can_ Set
--     -- can_ (Pi )
--
-- dInTms_ = div_ [] $ do
--     dInTmRN_ SET
--     dInTmRN_ ARR SET SET

dataLayouts_ :: ReactNode TermTransition
dataLayouts_ = div_ [ class_ "demo" ] $ do
    h2_ [] "data"

    locally dataLayout_


main :: IO ()
main = currentDocument >>= \(Just doc) ->
  documentGetElementById doc ("inject" :: JSString) >>= \(Just e) ->
    render (page_ ()) e
