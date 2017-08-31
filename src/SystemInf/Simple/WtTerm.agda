module SystemInf.Simple.WtTerm where

open import SystemInf.Prelude
open import SystemInf.Type
open import SystemInf.Ctx

open import SystemInf.Simple.Term

open TypeSubst using () renaming (_[/_]  to _[/tp_])

data WtMode : Set where
  chk inf : WtMode

infix 4 _⊢_m:_∈_
data _⊢_m:_∈_ {m n} (Γ : Ctx m n) : Term m n → WtMode → Type n → Set where
  var : ∀ (x : Fin m) →
        ---------------
        Γ ⊢ var x m: inf ∈ lookup x Γ

  λ' : ∀ {s t a} →
       (s ∷ Γ) ⊢ a m: chk ∈ t →
       ------------------------
       Γ ⊢ λ' a m: chk ∈ s →' t

  Λ : ∀ {t a} →
      (weakenCtx Γ) ⊢ a m: chk ∈ t →
      -----------------------
      Γ ⊢ Λ a m: chk ∈ ∀' t

  _·_ : ∀ {s t a b} →
        Γ ⊢ a m: inf ∈ s →' t → Γ ⊢ b m: chk ∈ s →
        ----------------------------------------
        Γ ⊢ a · b m: inf ∈ t

  _[_] : ∀ {s a} →
         Γ ⊢ a m: inf ∈ ∀' s → (t : Type n) →
         ------------------------------------
         Γ ⊢ a [ t ] m: inf ∈ (s [/tp t ])

  ann : ∀ {a} →
        (s : Type n) → Γ ⊢ a m: chk ∈ s →
        -----------------------------------
        Γ ⊢ a :: s m: inf ∈ s

  chkinf : ∀ {s a} →
           Γ ⊢ a m: inf ∈ s →
           ------------------
           Γ ⊢ a m: chk ∈ s

