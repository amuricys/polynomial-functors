-- Dynamical/Plot/src/HsPlot.hs
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ImportQualifiedPost #-}

module HsPlot where

-- a shit ton of nix stuff was needed. cairo, cairo.dev, zlib, zlib.dev, pkgconfig (NOT pkg-config with a dash)

import Graphics.Rendering.Chart.Easy
import Graphics.Rendering.Chart.Backend.Cairo
import Control.Monad (forM_)
import Data.Text qualified as T

plotToFile :: Double -> [(T.Text, [Double])] -> IO ()
plotToFile dt lines = toFile def "plot.png" $ do
    layout_title .= "Dynamics"
    setColors [opaque blue, opaque red]
    forM_ lines \(name, l) ->
        plot (line (T.unpack name) [zip [0, dt..] l ])
    -- plot (line "foxes" [zip [0, dt..] f])