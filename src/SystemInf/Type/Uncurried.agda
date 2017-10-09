module SystemInf.Type.Uncurried where

open import SystemInf.Prelude

open import Data.Fin.Substitution
open import Relation.Binary using (Decidable)

infix 7 ∀<_,_>_→'_

data Type (n : ℕ) : Set where
  var   : Fin n               → Type n
  Top Bot : Type n
  ∀<_,_>_→'_ : ∀ m l → Vec (Type (m + n)) l → Type (m + n) → Type n
  -- type arguments, term arguments, result

module TypeSubst where
  import Data.List as List
  module TypeApp {T} (l : Lift T Type) where
    open Lift l hiding (var)

    infixl 8 _/_

    -- Apply a substitution to a type
    {-# TERMINATING #-}
    _/_ : ∀ {m n} → Type m → Sub T m n → Type n
    var x / σ = lift (lookup x σ)
    Top / σ = Top
    Bot / σ = Bot
    (∀< m , l > xs →' τ) / σ = ∀< m , l > map (_/ σ ↑⋆ m) xs →' (τ / σ ↑⋆ m)

  -- Defining the abstract members var and _/_ in
  -- Data.Fin.Substitution.TermSubst for T = Type gives us access to a
  -- number of (generic) substitution functions out-of-the-box.
  typeSubst : TermSubst Type
  typeSubst = record { var = var; app = TypeApp._/_ }

  open TermSubst typeSubst public hiding (var)

  weaken↑ : ∀ {n} → Type (1 + n) → Type (2 + n)
  weaken↑ a = a / wk ↑

  infix 8 _[/_]

  -- Shorthand for single-variable type substitutions
  _[/_] : ∀ {n} → Type (1 + n) → Type n → Type n
  a [/ b ] = a / sub b

open TypeSubst public
  using ()
  renaming (weaken to weakenTy)
