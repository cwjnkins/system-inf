module SystemInf.Explicit.WtTerm where

open import SystemInf.Prelude

open import Data.Fin.Substitution

open import SystemInf.Type.Curried
open import SystemInf.Ctx as Ctx
open Ctx.Curried
open import SystemInf.Explicit.Term

------------------------------------------------------------------------
-- Typing derivations for polymorphic lambda terms

open TypeSubst using () renaming (_[/_]  to _[/tp_])

infix  4 _⊢_∈_

data _⊢_∈_ {m n} (Γ : Ctx m n) : Term m n → Type n → Set where
  var : (x : Fin m) →
        ----------------------
        Γ ⊢ var x ∈ lookup x Γ

  Λ   : ∀ {t a} →
          (weakenCtx Γ) ⊢ t ∈ a →
        -----------------------
          Γ ⊢ Λ t ∈ ∀' a

  λ'  : ∀ {t b} →
          (a : Type n) → a ∷ Γ ⊢ t ∈ b →
        ------------------------------
          Γ ⊢ λ' a t ∈ a →' b

  _[_] : ∀ {t a} →
           Γ ⊢ t ∈ ∀' a → (b : Type n) →
         -----------------------------
           Γ ⊢ t [ b ] ∈ a [/tp b ]

  _·_ : ∀ {s t a b} →
          Γ ⊢ s ∈ a →' b → Γ ⊢ t ∈ a →
          ----------------------------
          Γ ⊢ s · t ∈ b
