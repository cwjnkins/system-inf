module SystemInf.Ctx where

open import SystemInf.Prelude
open import SystemInf.Type

-- Typing contexts mapping free (term) variables to types.  A context
-- of type Ctx m n maps m free variables to types containing up to n
-- free type variables each.
Ctx : ℕ → ℕ → Set
Ctx m n = Vec (Type n) m

-- Type and variable substitutions lifted to typing contexts
module CtxSubst where
  open import Data.Fin.Substitution

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

open CtxSubst public using () renaming (weaken to weakenCtx)
