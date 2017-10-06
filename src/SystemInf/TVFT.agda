module SystemInf.TVFT where

{-
-- "Type variable from term"
-- Do simple type inference and /also/ try to figure out
--  ∀ α . α → T

-- Also includes "Type variable from context"
-- Try to infer the first type variable of an ∀ α . T
-- when checking it against [S/α]T
-}

open import SystemInf.Prelude
open import SystemInf.Type.Curried

open import SystemInf.TVFT.Term public
open import SystemInf.TVFT.WtTerm public
open import SystemInf.TVFT.Matching public
open import SystemInf.TVFT.TypeCheck public
