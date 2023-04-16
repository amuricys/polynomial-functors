{-# LANGUAGE ImportQualifiedPost #-}
module Lup where

import Prelude hiding (length , sum , zipWith)

import Data.Function (on)
import Data.Vector as V
import Debug.Trace
import System.Random
import Numeric.LinearAlgebra qualified as HMat
import Control.Monad as M

type Matrix a = V.Vector (V.Vector a)

eye :: Int -> Matrix Double
eye size = V.generate size (\i -> V.generate size (\j -> if i == j then 1 else 0))

swapRows :: Matrix a -> Int -> Int -> Matrix a
swapRows mat i j = mat // [(i, mat ! j), (j, mat ! i)]

setElem2D :: Matrix a -> Int -> Int -> a -> Matrix a
setElem2D mat i j elem = mat // [(i, (mat ! i) // [(j, elem)])]

getColumn :: Matrix Double -> Int -> Vector Double
getColumn mat j = fromList [row ! j | row <- toList mat]

-- Matrix multiplication
matrixMult :: Matrix Double -> Matrix Double -> Matrix Double
matrixMult a b
  | aCols /= bRows = error "Matrix dimensions do not match for multiplication."
  | otherwise = generate aRows (\i -> generate bCols (\j -> dotProduct (a ! i) (getColumn b j)))
  where
    aRows = length a
    aCols = length (a ! 0)
    bRows = length b
    bCols = length (b ! 0)
    dotProduct row col = sum $ zipWith (*) row col

matrixVectorMult :: Matrix Double -> Vector Double -> Vector Double
matrixVectorMult mat vec = fmap (\row -> sum (V.zipWith (*) row vec)) mat

-- Matrix transpose
transpose :: Matrix Double -> Matrix Double
transpose a = generate aCols (\i -> generate aRows (\j -> a ! j ! i))
  where
    aRows = length a
    aCols = length (a ! 0)

doolittleLupDecomposition :: Matrix Double -> (Matrix Double, Matrix Double, Matrix Double)
doolittleLupDecomposition a = loop 0 a (eye n) (V.replicate n $ V.replicate n 0) (eye n)
  where
    n = V.length a
    loop k aInit l u p
      | k == n = (l, u, p)
      | otherwise =
        let currentColumn = V.slice k (n - k) (V.map (\row -> row ! k) aInit)
            maxIndex = if V.null currentColumn then k else V.maxIndexBy (compare `on` abs) currentColumn
            maxRow = maxIndex + k
            pSwapped = swapRows p k maxRow
            aSwapped = swapRows aInit k maxRow
            (lUpdated, uUpdated, aUpdated) = V.foldl'
              (\(lAcc, uAcc, aAcc) i ->
                let lNew = setElem2D lAcc i k (aAcc ! i ! k / aAcc ! k ! k)
                    aNew = V.imap (\j aij -> if j < k then aij else aij - lNew ! i ! k * aAcc ! k ! j) (aAcc ! i)
                in (lNew, uAcc, aAcc // [(i, aNew)])
              )
              (l, u, aSwapped)
              (V.enumFromN (k + 1) (n - k - 1))
            uRow = V.foldl' (\uAcc j -> setElem2D uAcc k j (aUpdated ! k ! j)) uUpdated $ fromList [k..n-1]
        in loop (k + 1) aUpdated lUpdated uRow pSwapped




forwardSubstitution :: Int -> Matrix Double -> Vector Double -> Vector Double
forwardSubstitution n lower b =  V.foldl' calc_xi V.empty (V.enumFromN 0 n)
  where
    calc_xi acc i = let xi = b ! i - sum (V.zipWith (*) (V.slice 0 i (lower ! i)) acc) in
       V.snoc acc xi

backSubstitution :: Int -> Matrix Double -> Vector Double -> Vector Double
backSubstitution n upper y = V.foldr calc_xi V.empty (V.enumFromN 0 n)
  where
    calc_xi i acc = V.cons ((y ! i - sum (V.zipWith (*) (V.slice (i + 1) (n - i - 1) (upper ! i)) acc)) / upper ! i ! i) acc


-- Matrix inversion using Doolittle LUP decomposition
invertMatrix :: Matrix Double -> Matrix Double
invertMatrix a = loop 0 (eye n)
  where
    n = length a
    (l, u, p) = doolittleLupDecomposition a

    loop :: Int -> Matrix Double -> Matrix Double
    loop k inv
      | k == n = inv
      | otherwise =
          let b = p `matrixVectorMult` getColumn inv k
              x = forwardSubstitution n l b
              y = backSubstitution n u x
          in loop (k + 1) (setColumn inv k y)

    setColumn :: Matrix Double -> Int -> Vector Double -> Matrix Double
    setColumn mat j vec = imap (\i row -> row // [(j, vec ! i)]) mat

printMatrix :: Show a => Matrix a -> IO ()
printMatrix m = Prelude.mapM_ (putStrLn . show . V.toList) (V.toList m)

exampleMatrix :: Matrix Double
exampleMatrix = V.fromList
  [ V.fromList [4, 3, -1]
  , V.fromList [5, 3, 2]
  , V.fromList [2, 1, 3]
  ]

exampleMatrix2 :: IO (HMat.Matrix Double)
exampleMatrix2 = HMat.fromLists <$> M.replicateM 1000 (M.replicateM 1000 randomIO)

bTest :: Vector Double
bTest = V.fromList [1, 2, 3]

x = let (l, _, _) = doolittleLupDecomposition exampleMatrix in forwardSubstitution 3 l bTest
-- Expected output: [1.0,1.2,3.0000000000000004]
-- >>> x
-- [1.0,1.2,3.0000000000000004]

x' = let (_, u, _) = doolittleLupDecomposition exampleMatrix in backSubstitution 3 u bTest
-- Expected output: [-8.0, -10.0, 3.0]
-- >>> x'
-- [-8.550000000000013,13.083333333333352,2.250000000000002]

main :: IO ()
main = do
  ex <- exampleMatrix2
  putStrLn "\nMatrix A:"
  putStr . HMat.dispf 2 $ ex
  putStrLn "\nMatrix A⁻¹:"
  putStr . HMat.dispf 2 $ HMat.pinv ex
  putStrLn "\nMatrix A * A⁻¹:"
  putStr . HMat.dispf 2 $ ex HMat.<> HMat.pinv ex
  
