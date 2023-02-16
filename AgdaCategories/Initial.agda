{-# OPTIONS --cubical #-}

module AgdaCategories.Initial where

-- zeroArrowUnique : (f : Arrow Zero A) -> arrowFromZero Cubical.≡ f
-- zeroArrowUnique {A = A} f@(MkArrow mapPosition mapDirection) = {! arrowEqual {A = Zero} {B = A} { f = arrowFromZero} {g = f} (zeroMapPositionsUnique f) !} -- arrowEqual {A = Zero} {B = A} { f = arrowFromZero} {g = f} (?)  -- {! arrowEqual (zeroMapPositionsUnique ? ?) !} -- {! arrowEqual {f = arrowFromZero} {g = f} zeroMapPositionsUnique arrowFromZero f !}

-- isInitial : IsInitial Zero 
-- isInitial = record { ! = arrowFromZero ; !-unique = zeroArrowUnique }