module SystemInf.TVFC.WtTerm where

open import SystemInf.Prelude
open import SystemInf.Type.Curried
open import SystemInf.Ctx as Ctx
open Ctx.Curried

open import SystemInf.TVFC.Term

open TypeSubst using () renaming (_[/_]  to _[/tp_])

data WtMode : Set where
  chk inf : WtMode
