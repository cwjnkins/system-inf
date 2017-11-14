module SystemInf.TVFC.WtTerm where

open import SystemInf.Prelude
open import SystemInf.Type.Curried
open import SystemInf.Ctx as Ctx
open Ctx.Curried

open import SystemInf.TVFC.Term

open TypeSubst using () renaming (_[/_]  to _[/tp_])

data WtMode : Set where
  chk inf : WtMode

infix 4 _⊢_m:_∈_
data _⊢_m:_∈_ {m n} (Γ : Ctx m n) : Term m n → WtMode → Type n → Set where
  -- variables
  var : ∀ (x : Fin m) →
        ---------------
        Γ ⊢ var x m: inf ∈ lookup x Γ

  -- lambda (terms)
  λ'  : ∀ {s t a} →
        (s ∷ Γ) ⊢ a m: chk ∈ t →
        ------------------------
        Γ ⊢ λ' a m: chk ∈ s →' t

  -- lambda (types)
  Λ   : ∀ {t a} →
        (weakenCtx Γ) ⊢ a m: chk ∈ t →
        ------------------------------
        Γ ⊢ Λ a m: chk ∈ ∀' t

  -- application (no type argument synthesis)
  _·-mono_ : ∀ {s t a b} →
        Γ ⊢ a m: inf ∈ s →' t →
        Γ ⊢ b m: chk ∈ s →
        -----------------------
        Γ ⊢ a · b m: inf ∈ t

  -- application (type argument synthesis)
  -- note: whether we're synthesizing or checking at type,
  -- we're still guessing a type argument non-algorithmically
  _·-poly_ : ∀ {s t u a b m} →
        Γ ⊢ a m: inf ∈ ∀' t →
        Γ ⊢ (a [ u ]) · b m: inf ∈ s →
        ----------------------------
        Γ ⊢ a · b m: m ∈ s

  -- application (types)
  _[_] : ∀ {s a} →
        Γ ⊢ a m: inf ∈ ∀' s → (t : Type n) →
        ------------------------------------
        Γ ⊢ a [ t ] m: inf ∈ (s [/tp t ])

  -- implicit type application
  _[·] : ∀ {s t a} →
        Γ ⊢ a [ s ] m: inf ∈ t →
        ------------------------
        Γ ⊢ a [·] m: chk ∈ t

  ann : ∀ {a} →
        (s : Type n) → Γ ⊢ a m: chk ∈ s →
        -----------------------------------
        Γ ⊢ a :: s m: inf ∈ s

  chkinf : ∀ {s a} →
        Γ ⊢ a m: inf ∈ s →
        ------------------
        Γ ⊢ a m: chk ∈ s
