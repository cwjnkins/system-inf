module SystemInf.Explicit.Term where

open import SystemInf.Prelude
open import SystemInf.Type.Curried
open import SystemInf.Substitution as Subst

infixl 9 _[_] _·_

-- Untyped terms with up to m free term variables and up to n free
-- type variables
data Term (m n : ℕ) : Set where
  var     : (x : Fin m)                   → Term m n  -- term variable
  Λ       : Term m (1 + n)                → Term m n  -- type abstraction
  λ'      : Type n       → Term (1 + m) n → Term m n  -- term abstraction
  _[_]    : Term m n     → Type n         → Term m n  -- type application
  _·_     : Term m n     → Term m n       → Term m n  -- term application

Term' = ∀ {m n} → Term m n

module TermTypeSubst where
  open Subst.Generic Type TypeSubst.typeSubst Term

  module _ {T} (l : Lift T Type) where
    open Lift l hiding (var)
    open TypeSubst.TypeApp l renaming (_/_ to _/tp_)

    infixl 8 _/ty'_
    --     -- Apply a type substitution to a term
    _/ty'_ : ∀ {m n k} → Term m n → Sub T n k → Term m k
    var x      /ty' σ = var x
    Λ t        /ty' σ = Λ (t /ty' σ ↑)
    λ' a t     /ty' σ = λ' (a /tp σ) (t /ty' σ)
    t [ a ]    /ty' σ = (t /ty' σ) [ a /tp σ ]
    s · t      /ty' σ = (s /ty' σ) · (t /ty' σ)

  tySub : TmTySubst
  tySub =
    record { _/ty_ = λ l tm subst → _/ty'_ l tm subst }

  open TermType tySub public
open TermTypeSubst public
  using ()
  renaming (weaken to weakenTmTy ; _/_ to _/tmty_ ; _[/_] to _[/tmty_])

-- module TermTermSubst where
--   open Subst.Generic Type TypeSubst.typeSubst Term

--   module _ {T} (l : TmLift T) where
--     open TmLift l

--     infixl 8 _/tm'_
--     _/tm'_ : ∀ {m n k} → Term m n → TmSub T m n k → Term k n
--     var x   /tm' ρ = lift (lookup x ρ)
--     Λ x     /tm' ρ = Λ (x /tm' ρ ↑ty)
--     λ' t a  /tm' ρ = λ' t (a /tm' ρ ↑tm)
--     a [ t ] /tm' ρ = (a /tm' ρ) [ t ]
--     a · b   /tm' ρ = (a /tm' ρ) · (b /tm' ρ)

--   tmSub : TmTmSubst
--   tmSub =
--     record { tmvar = var ; _/tm_ = λ l tm subst → _/tm'_ l tm subst }

--   open TermTerm tmSub TermTypeSubst.tySub public
-- open TermTermSubst public
--   using ()
--   renaming (weaken to weakenTmTm ; _/_ to _/tmtm_ ; _[/_] to _[/tmtm_])

