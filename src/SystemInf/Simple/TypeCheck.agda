module SystemInf.Simple.TypeCheck where

open import SystemInf.Prelude
open import SystemInf.Type

open import SystemInf.Simple.Term
open import SystemInf.Simple.WtTerm

open TypeSubst using () renaming (_[/_]  to _[/tp_])
open CtxSubst  using () renaming (weaken to weakenCtx)

data TyInf {m n} (Γ : Ctx m n) : Term m n → Set where
  ok  : ∀ {a} t → (wt : Γ ⊢ a ∈ t) → TyInf Γ a
  bad : ∀ {a} → (msg : String) → TyInf Γ a

inferType : ∀ {m n} (Γ : Ctx m n) t → TyInf Γ t
inferType Γ (var x)
  = ok (lookup x Γ) (var x)
inferType Γ (Λ a)
  with inferType (weakenCtx Γ) a
... | bad msg
  = bad msg
... | ok t wt = ok (∀' t) (Λ wt)
inferType Γ (λ' t a)
  with inferType (t ∷ Γ) a
... | bad msg
  = bad msg
... | ok s wt = ok (t →' s) (λ' t wt)
inferType Γ (a [ t ])
  with inferType Γ a
... | bad msg
  = bad msg
... | ok (var _) wt
  = bad ""
... | ok (s' →' t') wt
  = bad ""
... | ok (∀' t') wt
  = ok (t' [/tp t ]) (wt [ t ])
inferType Γ (a · b)
  with inferType Γ a | inferType Γ b
... | bad msg  | _ = bad msg
... |  _       | (bad msg) = bad msg
... | ok (s →' t) wt₁ | (ok s' wt₂)
  with s ≟T s'
... | (no ¬p)
  = bad ""
inferType Γ (a · b)
  | ok (s →' t) wt₁ | (ok .s wt₂)
  | (yes refl)
  = ok t (wt₁ · wt₂)
inferType Γ (a · b) | ok _ wt₁ | (ok _ wt₂)
  = bad ""


