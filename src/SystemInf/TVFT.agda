module SystemInf.TVFT where

{-
-- "Type variable from term"
-- Do simple type inference and /also/ try to figure out
--  ∀ α . α → T
-}

open import SystemInf.Prelude
open import SystemInf.Type

open import SystemInf.TVFT.Term public
open import SystemInf.TVFT.WtTerm public
open import SystemInf.TVFT.TypeCheck public
