{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}

module OptparseHs where

import Options.Applicative
import GHC.Generics (Generic)
import Data.Text (Text)

data ParamType = ReservoirParamsType | LorenzParamsType | HodgkinHuxleyParamsType | LotkaVolterraParamsType

--(rdimf ∷ trainStepsf ∷ touchStepsf ∷ outputLengthf ∷ lorinitx ∷ lorinity ∷ lorinitz ∷ dt ∷ [])
data SystemParams where
  ReservoirParams :: 
    { rdimf         :: Integer
    , trainStepsf   :: Integer
    , touchStepsf   :: Integer
    , outputLengthf :: Integer
    , lorinitx      :: Double
    , lorinity      :: Double
    , lorinitz      :: Double
    , dt            :: Double
    , variance       :: Double
    } -> SystemParams
  LorenzParams ::
    { lorinitx' :: Double
    , lorinity' :: Double
    , lorinitz' :: Double
    , dt'       :: Double
    } -> SystemParams
  HodgkinHuxleyParams ::
    { dt'' :: Double }
    -> SystemParams
  LotkaVolterraParams ::
    { alpha :: Double
    , beta :: Double
    , delta :: Double
    , gamma :: Double
    , r0 :: Double
    , f0 :: Double
    , dt''' :: Double }
    -> SystemParams
deriving instance Show SystemParams

data Options = Options
  { system :: SystemParams
  } deriving (Show, Generic)

systemParser :: Parser SystemParams
systemParser = hsubparser $ 
     command "Reservoir" (info reservoirParamsParser (progDesc "Reservoir system"))
  <> command "Lorenz" (info lorenzParamsParser (progDesc "Lorenz system"))
  <> command "HodgkinHuxley" (info hodgkinHuxleyParamsParser (progDesc "Hodgkin-Huxley system"))
  <> command "LotkaVolterra" (info lotkaVolterraParamsParser (progDesc "Lotka-Volterra system"))


reservoirParamsParser :: Parser SystemParams
reservoirParamsParser = ReservoirParams
  <$> option auto (long "numNodes" <> short 'n' <> metavar "NUMNODES" <> help "Number of nodes in the reservoir")
  <*> option auto (long "trainingSteps" <> short 't' <> metavar "TRAINSTEPS" <> help "Number of data points to train on")
  <*> option auto (long "touchingSteps" <> short 'c' <> metavar "TOUCHSTEPS" <> help "Number of points from training system to feed before looping RC into itself")
  <*> option auto (long "outputLength" <> short 'o' <> metavar "OUTPUTLENGTH" <> help "Length of total output by reservoir + test system")
  <*> option auto (long "x0" <> short 'x' <> metavar "X0" <> help "X initial condition")
  <*> option auto (long "y0" <> short 'y' <> metavar "Y0" <> help "Y initial condition")
  <*> option auto (long "z0" <> short 'z' <> metavar "Z0" <> help "Z initial condition")
  <*> option auto (long "dt" <> short 'd' <> metavar "DT" <> help "Time step size")
  <*> option auto (long "variance" <> short 'v' <> metavar "VARIANCE" <> help "Variance")

lorenzParamsParser :: Parser SystemParams
lorenzParamsParser = LorenzParams
  <$> option auto (long "x0" <> short 'x' <> metavar "X0" <> help "Initial x value")
  <*> option auto (long "y0" <> short 'y' <> metavar "Y0" <> help "Initial y value")
  <*> option auto (long "z0" <> short 'z' <> metavar "Z0" <> help "Initial z value")
  <*> option auto (long "dt" <> short 't' <> metavar "DT" <> help "Time step")

lotkaVolterraParamsParser :: Parser SystemParams
lotkaVolterraParamsParser = LotkaVolterraParams
  <$> option auto (long "alpha" <> short 'a' <> metavar "α" <> help "Maximum prey per capita growth rate on rabbits")
  <*> option auto (long "beta" <> short 'b' <> metavar "β" <> help "Effect of the presence of foxes on the rabbit growth rate")
  <*> option auto (long "delta" <> short 'd' <> metavar "δ" <> help "Foxes' per capita death rate")
  <*> option auto (long "gamma" <> short 'g' <> metavar "γ" <> help "Effect of the presence of rabbits on the foxes' growth rate")
  <*> option auto (long "r0" <> short 'r' <> metavar "R0" <> help "Initial rabbit population")
  <*> option auto (long "f0" <> short 'f' <> metavar "F0" <> help "Initial fox population")
  <*> option auto (long "dt" <> short 't' <> metavar "DT" <> help "Time step")

hodgkinHuxleyParamsParser :: Parser SystemParams
hodgkinHuxleyParamsParser = HodgkinHuxleyParams <$> option auto (long "dt" <> short 't' <> metavar "DT" <> help "Time step")

optionsParser :: Parser Options
optionsParser = Options <$> systemParser

parseOptions :: IO Options
parseOptions = execParser $ info (optionsParser <**> helper) fullDesc
