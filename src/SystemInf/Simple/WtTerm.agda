module SystemInf.Simple.WtTerm where

open import SystemInf.Prelude

open import Data.Fin.Substitution

open import SystemInf.Type
open import SystemInf.Simple.Term

------------------------------------------------------------------------
-- Typing derivations for polymorphic lambda terms

-- Typing contexts mapping free (term) variables to types.  A context
-- of type Ctx m n maps m free variables to types containing up to n
-- free type variables each.
Ctx : ℕ → ℕ → Set
Ctx m n = Vec (Type n) m

-- Type and variable substitutions lifted to typing contexts
module CtxSubst where

  infixl 8 _/_ _/Var_

  -- Type substitution lifted to typing contexts
  _/_ : ∀ {m n k} → Ctx m n → Sub Type n k → Ctx m k
  Γ / σ = Γ TypeSubst.⊙ σ

  -- Weakening of typing contexts with additional type variables
  weaken : ∀ {m n} → Ctx m n → Ctx m (1 + n)
  weaken Γ = map TypeSubst.weaken Γ

  -- Variable substitution (renaming) lifted to typing contexts
  _/Var_ : ∀ {m n k} → Sub Fin m k → Ctx k n → Ctx m n
  σ /Var Γ = map (λ x → lookup x Γ) σ

open TypeSubst using () renaming (_[/_]  to _[/tp_])
open CtxSubst  using () renaming (weaken to weakenCtx)

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
          
      
