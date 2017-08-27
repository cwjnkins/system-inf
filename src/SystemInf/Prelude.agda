module SystemInf.Prelude where

open import Data.Nat        public
open import Data.Fin as Fin
  using (Fin ; zero ; suc)  public
open import Data.Vec        public
  hiding ([_])
  renaming (_++_ to _++𝕍_)
open import Data.String     public
  renaming (_≟_ to _≟𝕊_)
  hiding (fromList ; toList ; decSetoid ; setoid)

open import Relation.Binary.PropositionalEquality public
  hiding ([_])
open import Relation.Nullary public
