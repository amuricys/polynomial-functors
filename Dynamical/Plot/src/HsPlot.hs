-- Dynamical/Plot/src/HsPlot.hs

module HsPlot where

-- a shit ton of nix stuff was needed. cairo, cairo.dev, zlib, zlib.dev, pkgconfig (NOT pkg-config with a dash)

import Graphics.Rendering.Chart.Easy
import Graphics.Rendering.Chart.Backend.Cairo

plotToFile :: Double -> [Double] -> [Double] -> IO ()
plotToFile dt r f = toFile def "plot.png" $ do
    layout_title .= "Dynamics idk"
    setColors [opaque blue, opaque red]
    plot (line "rabbits" [zip [0, dt..] r ])
    plot (line "foxes" [zip [0, dt..] f])