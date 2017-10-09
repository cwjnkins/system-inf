module SystemInf.PierceTurner.Term where

open import SystemInf.Prelude
open import SystemInf.Type.Uncurried
open import SystemInf.Substitution as Subst

-- infixl 9 _[_] _·_

-- Untyped terms with up to m free term variables and up to n free
-- type variables
data ITerm (m n : ℕ) : Set where
  var    : (x : Fin m) → ITerm m n
  fun[_] : ∀ k {l}
           → Vec (Type (k + n)) l -- l new term variables mentioning
                                  -- k new type variables
           → ITerm (l + m) (k + n) → ITerm m n
  _[_]·_ : ∀ {k l} → ITerm m n
           → Vec (Type n) l    -- all the types
           → Vec (ITerm m n) k -- all the terms
           → ITerm m n

ITerm' = ∀ {m n} → ITerm m n

data ETerm (m n : ℕ) : Set where
  var     : (x : Fin m) → ETerm m n
  -- function abstraction w/ term argument types
  fun[X=_]x:T=_,_ : ∀ k l
           → Vec (Type (k + n)) l -- l new term variables mentioning
                                  -- k new type variables
           → ETerm (l + m) (k + n) → ETerm m n
  -- function abstraction w/o term argument types
  fun[X=_]x=_ : ∀ k l
                → ETerm (l + m) (k + n) → ETerm m n
  -- application with explicit type arugments
  _[_]·_  : ∀ {k l} → ETerm m n
           → Vec (Type n) l    -- all the types
           → Vec (ETerm m n) k -- all the terms
           → ETerm m n
  -- application w/o explicit type arguments
  _·_ : ∀ {k}
        → ETerm m n → Vec (ETerm m n) k → ETerm m n

module ETermTypeSubst where
  open Subst.Generic Type TypeSubst.typeSubst ETerm

  module _ {T} (l : Lift T Type) where
    open Lift l hiding (var)
    open TypeSubst.TypeApp l renaming (_/_ to _/tp_)

    infixl 8 _/ty'_
    {-# TERMINATING #-}
    _/ty'_ : ∀ {m n k} → ETerm m n → Sub T n k → ETerm m k
    var x                     /ty' σ
      = var x
    (fun[X= k ]x:T= l , ts) t /ty' σ
      = (fun[X= k ]x:T= l , map (_/tp σ ↑⋆ k) ts) $' t /ty' σ ↑⋆ k
    (fun[X= k ]x=   l)      t /ty' σ
      = (fun[X= k ]x= l)                          $' t /ty' σ ↑⋆ k
    -- termination checking fails here--------------------+
    (t [ X ]· x)              /ty' σ                   -- |
      = (t /ty' σ) [ map (_/tp σ) X ]· map (_/ty' σ) x -- |
    (t · x)                   /ty' σ                   -- |
      = (t /ty' σ) · map (_/ty' σ) x                   -- |

  tySub : TmTySubst
  tySub = record { _/ty_ = λ l t σ → _/ty'_ l t σ }

  open TermType tySub public
open ETermTypeSubst public
  using () renaming (weaken to weakenTyTm ; _/_ to _/tytm_; _[/_] to _[/tytm_])
