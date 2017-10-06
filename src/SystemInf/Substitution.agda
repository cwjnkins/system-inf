module SystemInf.Substitution where

open import SystemInf.Prelude
open import SystemInf.Type.Curried

open import Data.Fin.Substitution public

module Generic (Tm : ℕ → ℕ → Set) where
  ------------------------------------------------------------
  -- Substitutition of terms in types
  record TmTySubst : Set₁ where
    infixl 8 _/ty_
    field
      _/ty_ : ∀ {T m n k} → (l : Lift T Type) → Tm m n → Sub T n k → Tm m k

  module TermType (tySubst : TmTySubst) where
    open TmTySubst tySubst
    open TypeSubst using (varLift; termLift; sub)

    module Lifted {T} (lift : Lift T Type) {m} where
      application : Application (Tm m) T
      application = record { _/_ = _/ty_ lift }

      open Application application public

    open Lifted termLift public

    -- Apply a type variable substitution (renaming) to a term
    _/Var_ : ∀ {m n k} → Tm m n → Sub Fin n k → Tm m k
    _/Var_ = _/ty_ varLift

    -- Weaken a term with an additional type variable
    weaken : ∀ {m n} → Tm m n → Tm m (suc n)
    weaken t = t /Var VarSubst.wk

    infix 8 _[/_]

    -- Shorthand for single-variable type substitutions in terms
    _[/_] : ∀ {m n} → Tm m (1 + n) → Type n → Tm m n
    t [/ b ] = t / sub b

  ------------------------------------------------------------
  -- Substitution of terms in terms
  TmSub : (T : ℕ → ℕ → Set) → ℕ → ℕ → ℕ  → Set
  TmSub T m n k = Sub (flip T n) m k

  record TmLift (T : ℕ → ℕ → Set) : Set where
    infix 10 _↑tm _↑ty
    field
      lift : ∀ {m n} → T m n → Tm m n
      _↑tm : ∀ {m n k} → TmSub T m n k → TmSub T (suc m) n (suc k)
      _↑ty : ∀ {m n k} → TmSub T m n k → TmSub T m (suc n) k

  record TmTmSubst : Set₁ where
    infixl 8 _/tm_
    field
      tmvar : ∀ {m n} → Fin m → Tm m n
      _/tm_ : ∀ {T m n k} → (l : TmLift T) → Tm m n → TmSub T m n k → Tm k n

  module TermTerm (tmSubst : TmTmSubst) (tySubst : TmTySubst) where
    open TermType tySubst using () renaming (weaken to weakenTp)
    open TmTySubst tySubst
    open TmTmSubst tmSubst

    private
      Fin′ : ℕ → ℕ → Set
      Fin′ m _ = Fin m

    varLift : TmLift Fin′
    varLift =
      record { lift = tmvar
             ; _↑tm = VarSubst._↑
             ; _↑ty = id }

    infixl 8 _/Var_

    _/Var_ : ∀ {m n k} → Tm m n → Sub Fin m k → Tm k n
    _/Var_ = _/tm_ varLift

    Tm′ : ℕ → ℕ → Set
    Tm′ = flip Tm

    private
      module ExpandSimple {n : ℕ} where
        simple : Simple (Tm′ n)
        simple = record { var = tmvar; weaken = λ t → t /Var VarSubst.wk }

        open Simple simple public

    open ExpandSimple  using (_↑; simple)

    termLift : TmLift Tm
    termLift = record
      { lift = id
      ; _↑tm = _↑
      ; _↑ty = λ ρ → map weakenTp ρ -- map weakenTp ρ
      }

    private
      module ExpandSubst {n : ℕ} where
        app : Application (Tm′ n) (Tm′ n)
        app = record { _/_ = λ tm s → _/tm_ termLift tm s }

        subst : Subst (flip Tm n)
        subst = record
          { simple      = simple
          ; application = app
          }

        open Subst subst public

    open ExpandSubst public hiding (var; simple)

    infix 8 _[/_]

    -- Shorthand for single-variable term substitutions in terms
    _[/_] : ∀ {m n} → Tm (1 + m) n → Tm m n → Tm m n
    s [/ t ] = s / sub t
