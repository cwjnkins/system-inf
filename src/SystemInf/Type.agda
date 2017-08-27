module SystemInf.Type where

open import SystemInf.Prelude

open import Data.Fin.Substitution
open import Relation.Binary using (Decidable)

-- Code borrowed somewhat from https://github.com/sstucki/system-f-agda
-- (Types, terms, etc)

infixr 7 _→'_

-- Types with n free variables
data Type (n : ℕ) : Set where
  var   : Fin n               → Type n
  _→'_  : (τ₁ τ₂ : Type n)    → Type n
  ∀'    : (τ : Type (1 + n))  → Type n


------------------------------------------------------------------------
-- Substitutions in types

module TypeSubst where
  module TypeApp {T} (l : Lift T Type) where
    open Lift l hiding (var)

    infixl 8 _/_

    -- Apply a substitution to a type
    _/_ : ∀ {m n} → Type m → Sub T m n → Type n
    var x       / σ = lift (lookup x σ)
    (τ₁ →' τ₂)  / σ = (τ₁ / σ) →' (τ₂ / σ)
    ∀' τ        / σ = ∀' (τ / σ ↑)

    open Application (record { _/_ = _/_})


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


-- A decision procedure for (syntactic) type equality
-- TODO
postulate
  _≟T_ : ∀ {n} → Decidable {A = Type n} _≡_

