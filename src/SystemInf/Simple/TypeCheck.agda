module SystemInf.Simple.TypeCheck where

open import SystemInf.Prelude
  hiding (bad ; ok)
open import SystemInf.Type.Curried
open import SystemInf.Ctx as Ctx
open Ctx.Curried

open import SystemInf.Simple.Term
open import SystemInf.Simple.WtTerm

open TypeSubst using () renaming (_[/_]  to _[/tp_])

data TyInf {m n} (Γ : Ctx m n) : Term m n → Set where
  ok  : ∀ {a} t → (wt : Γ ⊢ a m: inf ∈ t) → TyInf Γ a
  bad : ∀ {a} → (msg : String) → TyInf Γ a

data TyChk {m n} (Γ : Ctx m n) : Term m n → Type n → Set where
  ok  : ∀ {a} t → (wt : Γ ⊢ a m: chk ∈ t) → TyChk Γ a t
  bad : ∀ {a t} → (msg : String) → TyChk Γ a t

-- mutual recursive type check and inference

infType : ∀ {m n} (Γ : Ctx m n) a   → TyInf Γ a
chkType : ∀ {m n} (Γ : Ctx m n) a t → TyChk Γ a t

infType Γ (var x)   = ok (lookup x Γ) (var x)
infType Γ (λ' a)    = bad "Cannot infer term function type"
infType Γ (Λ a)     = bad "Cannot infer type function types" -- ?
infType Γ (a · b)   with infType Γ a
... | bad msg         = bad ("When inferring >_< ·  _\n" ++ msg)
... | ok (s →' t) wt₁ with chkType Γ b s
...   | (ok .s wt₂)     = ok t (wt₁ · wt₂)
...   | (bad msg)       = bad ("When checking _  · >_<\n" ++ msg)
infType Γ (a · b)
    | ok t wt         = bad "When infering >_< · _\nNot a (term) function"
infType Γ (a [ t ]) with infType Γ a
... | bad msg = bad ("When infering >_< [_]\n" ++ msg)
...   | ok (∀' t') wt = ok (t' [/tp t ]) (wt [ t ])
infType Γ (a [ t ])
      | ok t' wt      = bad "When infering >_< [_]\nNot a (type) function"
infType Γ (a :: t)  with chkType Γ a t
... | bad msg         = bad ("When inferring _ :: _\n" ++ msg)
... | ok .t wt        = ok t (ann t wt)

-- chkType Γ (λ' a) t      = {!!}
chkType Γ (λ' a) (s →' t)    with chkType (s ∷ Γ) a t
... | bad msg                  = bad ("When checking λ _\n" ++ msg)
... | ok .t wt                 = ok (s →' t) (λ' wt)
chkType Γ (λ' a) t           = bad "When checking λ _\nNot a (term) function type"
-- chkType Γ (Λ a) t       = 
chkType Γ (Λ a) (∀' t)       with chkType (weakenCtx Γ) a t
... | bad msg                  = bad ("When checking Λ _\n" ++ msg)
... | ok .t wt                 = ok (∀' t) (Λ wt)
chkType Γ (Λ a) t            = bad "When checking Λ _\nNot a (type) function type"
chkType Γ (a :: t) t'      with t ≟T t'
... | no ¬p                  = bad "When checking _ :: >_<\nGot _ != Expected _"
... | yes refl               with chkType Γ a t
...   | (bad msg)              = bad ("When checking >_< :: _\n" ++ msg)
...   | (ok .t wt)             = ok t (chkinf (ann t wt))
chkType Γ a t              with infType Γ a
... | bad msg                = bad ("When checking _ has type _\n" ++ msg)
... | ok t' wt               with t ≟T t'
...   | (no ¬p)                = bad "When checking _ has type _\nGot _ != Expected _"
...   | (yes refl)             = ok t (chkinf wt)
-- chkType Γ (var x) t     = {!!}
-- chkType Γ (a · b) t     = {!!}
-- chkType Γ (a [ x ]) t    = {!!}
