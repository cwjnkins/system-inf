module SystemInf.Simple.TypeCheck where

open import SystemInf.Prelude
open import SystemInf.Type

open import SystemInf.Simple.Term
open import SystemInf.Simple.WtTerm

open TypeSubst using () renaming (_[/_]  to _[/tp_])
open CtxSubst  using () renaming (weaken to weakenCtx)

data TyInf {m n} (Γ : Ctx m n) : Term m n → Set where
  ok  : ∀ {a t} → (wt : Γ ⊢ a ∈ t) → TyInf Γ a
  bad : ∀ {t} → (msg : String) → TyInf Γ t

inferType : ∀ {m n} (Γ : Ctx m n) t → TyInf Γ t
inferType Γ (var x)
  = ok (var x)
inferType Γ (Λ t)
  with inferType (weakenCtx Γ) t
... | bad msg
  = bad msg
... | ok wt = ok (Λ wt)
inferType Γ (λ' t a)
  with inferType (t ∷ Γ) a
... | bad msg
  = bad msg
... | ok {t = s} wt = ok (λ' t wt)
inferType Γ (a [ t ])
  with inferType Γ a
... | bad msg
  = bad msg
... | ok {t = var x} wt
  = bad ""
... | ok {t = s' →' t'} wt
  = bad ""
... | ok {t = ∀' t'} wt
  = ok {t = t' [/tp t ]} (wt [ t ])
inferType Γ (a · b)
  with inferType Γ a | inferType Γ b
... | bad msg  | _ = bad msg
... |  _       | (bad msg) = bad msg
... | ok {t = s →' t} wt₁ | (ok {t = s'} wt₂)
  with s ≟T s'
... | (no ¬p)
  = bad ""
inferType Γ (a · b)
  | ok {_} {s →' t} wt₁ | (ok {_} {.s} wt₂)
  | (yes refl)
  = ok {t = t} (wt₁ · wt₂)
inferType Γ (a · b) | ok {t = _} wt₁ | (ok {t = t} wt₂)
  = bad ""


