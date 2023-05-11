{-# OPTIONS --without-K #-}

module CategoryData.Polynomial where

record Polynomial : Set₁ where
    constructor mkpoly
    field
        position : Set
        direction : position → Set
open Polynomial public