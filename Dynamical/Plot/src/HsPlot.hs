-- Dynamical/Plot/src/HsPlot.hs
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}

module HsPlot where

import Graphics.Rendering.Chart.Easy
import Graphics.Rendering.Chart.Backend.Cairo
import Control.Monad (forM_)
import Data.Text qualified as T

plotToFile :: T.Text -> T.Text -> T.Text -> Double -> [(T.Text, [Double])] -> IO ()
plotToFile xaxisTitle yaxisTitle title dt lines = toFile def (T.unpack . T.replace " " "_" $ T.toLower title <> ".png") $ do
    layout_title .= T.unpack title
    layout_x_axis . laxis_title .= T.unpack xaxisTitle
    layout_y_axis . laxis_title .= T.unpack yaxisTitle
    setColors . fmap opaque $ [purple, sienna, plum, powderblue, salmon, sandybrown, cornflowerblue, blanchedalmond, firebrick, gainsboro, honeydew]
    forM_ lines \(name, l) ->
        plot (line (T.unpack name) [zip [0, dt..] l ])
    -- plot (line "foxes" [zip [0, dt..] f])