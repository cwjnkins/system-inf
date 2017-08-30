module SystemInf.Explicit.Term where

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

module TermTermSubst where

  -- Substitutions of terms in terms
  --
  -- A TermSub T m n k is a substitution which, when applied to a term
  -- with at most m free term variables and n free type variables,
  -- yields a term with at most k free term variables and n free type
  -- variables.
  TermSub : (ℕ → ℕ → Set) → ℕ → ℕ → ℕ → Set
  TermSub T m n k = Sub (flip T n) m k

  record TermLift (T : ℕ → ℕ → Set) : Set where
    infix 10 _↑tm _↑tp
    field
      lift : ∀ {m n} → T m n → Term m n
      _↑tm : ∀ {m n k} → TermSub T m n k → TermSub T (suc m) n (suc k)
      _↑tp : ∀ {m n k} → TermSub T m n k → TermSub T m (suc n) k

  module TermTermApp {T} (l : TermLift T) where
    open TermLift l

    infixl 8 _/_

        -- Apply a term substitution to a term
    _/_ : ∀ {m n k} → Term m n → TermSub T m n k → Term k n
    var x      / ρ = lift (lookup x ρ)
    Λ t        / ρ = Λ (t / ρ ↑tp)
    λ' a t     / ρ = λ' a (t / ρ ↑tm)
    t [ a ]    / ρ = (t / ρ) [ a ]
    s · t      / ρ = (s / ρ) · (t / ρ)

  Fin′ : ℕ → ℕ → Set
  Fin′ m _ = Fin m

  varLift : TermLift Fin′
  varLift = record { lift = var; _↑tm = VarSubst._↑; _↑tp = id }

  infixl 8 _/Var_

  _/Var_ : ∀ {m n k} → Term m n → Sub Fin m k → Term k n
  _/Var_ = TermTermApp._/_ varLift

  Term′ : ℕ → ℕ → Set
  Term′ = flip Term

  private
    module ExpandSimple {n : ℕ} where
      simple : Simple (Term′ n)
      simple = record { var = var; weaken = λ t → t /Var VarSubst.wk }

      open Simple simple public

  open ExpandSimple  using (_↑; simple)
  open TermTypeSubst using () renaming (weaken to weakenTp)

  termLift : TermLift Term
  termLift = record
    { lift = id; _↑tm = _↑ ; _↑tp = λ ρ → map weakenTp ρ }

  private
    module ExpandSubst {n : ℕ} where
      app : Application (Term′ n) (Term′ n)
      app = record { _/_ = TermTermApp._/_ termLift {n = n} }

      subst : Subst (flip Term n)
      subst = record
        { simple      = simple
        ; application = app
        }

      open Subst subst public

  open ExpandSubst public hiding (var; simple)

  infix 8 _[/_]

  -- Shorthand for single-variable term substitutions in terms
  _[/_] : ∀ {m n} → Term (1 + m) n → Term m n → Term m n
  s [/ t ] = s / sub t



