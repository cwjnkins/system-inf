module SystemInf.Simple.Term where

open import SystemInf.Prelude

open import SystemInf.Type
open import Data.Fin.Substitution

infixl 9 _[_] _·_

-- Untyped terms with up to m free term variables and up to n free
-- type variables
data Term (m n : ℕ) : Set where
  var     : (x : Fin m)                   → Term m n  -- term variable
  Λ       : Term m (1 + n)                → Term m n  -- type abstraction
  λ'      : Type n       → Term (1 + m) n → Term m n  -- term abstraction
  _[_]    : Term m n     → Type n         → Term m n  -- type application
  _·_     : Term m n     → Term m n       → Term m n  -- term application

module TermTypeSubst where

  module TermTypeApp {T} (l : Lift T Type) where
    open Lift l hiding (var)
    open TypeSubst.TypeApp l renaming (_/_ to _/tp_)

    infixl 8 _/_

    -- Apply a type substitution to a term
    _/_ : ∀ {m n k} → Term m n → Sub T n k → Term m k
    var x      / σ = var x
    Λ t        / σ = Λ (t / σ ↑)
    λ' a t     / σ = λ' (a /tp σ) (t / σ)
    t [ a ]    / σ = (t / σ) [ a /tp σ ]
    s · t      / σ = (s / σ) · (t / σ)


  open TypeSubst using (varLift; termLift; sub)

  module Lifted {T} (lift : Lift T Type) {m} where
    application : Application (Term m) T
    application = record { _/_ = TermTypeApp._/_ lift {m = m} }

    open Application application public

  open Lifted termLift public

    -- Apply a type variable substitution (renaming) to a term
  _/Var_ : ∀ {m n k} → Term m n → Sub Fin n k → Term m k
  _/Var_ = TermTypeApp._/_ varLift

  -- Weaken a term with an additional type variable
  weaken : ∀ {m n} → Term m n → Term m (suc n)
  weaken t = t /Var VarSubst.wk
