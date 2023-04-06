{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}

module OptparseHs where

import Options.Applicative
import GHC.Generics (Generic)
import Data.Text (Text)

data DynamicalSystem = LotkaVolterra | HodgkinHuxley | Lorenz | Reservoir
  deriving (Show, Generic, Read)

data Options = Options
  { system :: DynamicalSystem
  , params :: [Double]
  } deriving (Show, Generic)


systemParser :: Parser DynamicalSystem
systemParser = option auto
  ( long "system"
    <> short 's'
    <> metavar "SYSTEM"
    <> help "Choose a dynamical system: LotkaVolterra, HodgkinHuxley, Lorenz, Reservoir" )

optionsParser :: Parser Options
optionsParser = Options
  <$> systemParser
  <*> many (option auto
      ( long "params"
     <> short 'p'
     <> metavar "PARAMS"
     <> help "Parameters to the chosen dynamical system" ))

parseOptions :: IO Options
parseOptions = execParser $ info (optionsParser <**> helper) fullDesc