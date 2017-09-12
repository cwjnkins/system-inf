module SystemInf.TVFT.TypeCheck where

open import SystemInf.Prelude
open import SystemInf.Type
open import SystemInf.Ctx

open import SystemInf.TVFT.Term
open import SystemInf.TVFT.WtTerm

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
infType Γ (λ' a)    = bad $'
  "(1) Cannot infer term function type"
infType Γ (Λ a)     = bad $'
  "(2) Cannot infer type function types" -- ?
infType Γ (a · b)   with infType Γ a
... | bad msg         = bad $'
  "(3) When inferring >_< · _\n" ++ msg
... | ok (s →' t) wt₁ with chkType Γ b s
...   | (ok .s wt₂)     = ok t (wt₁ · wt₂)
...   | (bad msg)       = bad $'
  "(4) When checking _ · >_<\n" ++ msg
infType Γ (a · b)
    | ok t wt         = bad
  "(5) When infering >_< · _\nNot a (term) function"
infType Γ (a [ t ]) with infType Γ a
... | bad msg = bad $'
  "(6) When infering >_< [_]\n" ++ msg
...   | ok (∀' t') wt = ok (t' [/tp t ]) (wt [ t ])
infType Γ (a [ t ])
      | ok t' wt      = bad
  "(7) When inferring >_< [_]\nNot a (type) function"
infType Γ (a ·[ b ])with infType Γ a
... | bad msg         = bad $'
  "(8) When inferring >_< ·[_]\n" ++ msg
... | ok (∀' (var zero →' t)) wt
                      with infType Γ b
...   | (bad msg)       = bad $'
  "(9) When inferring _ ·[>_<]\n" ++ msg
...   | (ok t' wt')     = ok (t [/tp t' ]) (wt ·[ wt' ])
infType Γ (a ·[ b ])
    | ok t wt         = bad $'
  "(10) When inferring >_< ·[_]\n"
    ++ "Inferred type " ++ showTy t ++ " not of the form ∀ z. (z → z)"
infType Γ (a [·])   = bad $'
  "(11) TODO"
infType Γ (a :: t)  with chkType Γ a t
... | bad msg         = bad $'
  "(12) When inferring _ :: " ++ showTy t ++ "\n" ++ msg
... | ok .t wt        = ok t (ann t wt)

-- chkType Γ (λ' a) t      = {!!}
chkType Γ (λ' a) (s →' t)    with chkType (s ∷ Γ) a t
... | bad msg                  = bad $'
  "(1) When checking λ _ has type " ++ showTy (s →' t) ++ "\n" ++ msg
... | ok .t wt                 = ok (s →' t) (λ' wt)
chkType Γ (λ' a) t           = bad $'
  "(2) When checking λ _ has type " ++ showTy t ++ "\nNot a (term) function type"
-- chkType Γ (Λ a) t       =
chkType Γ (Λ a) (∀' t)       with chkType (weakenCtx Γ) a t
... | bad msg                  = bad $'
  "(3) When checking Λ _ has type " ++ showTy (∀' t) ++ "\n" ++ msg
... | ok .t wt                 = ok (∀' t) (Λ wt)
chkType Γ (Λ a) t            = bad $'
  "(4) When checking Λ _ has type " ++ showTy t
    ++ "\nNot a (type) function type"
chkType Γ (a :: t) t'      with t ≟T t'
... | no ¬p                  = bad $'
  "(5) When checking _ :: >" ++ showTy t
    ++ "<\nGot " ++ showTy t ++ " != Expected " ++ showTy t'
... | yes refl               with chkType Γ a t
...   | (bad msg)              = bad $'
  "(6) When checking >_< :: " ++ showTy t ++ "\n" ++ msg
...   | (ok .t wt)             = ok t (chkinf (ann t wt))
chkType Γ a t              with infType Γ a
... | bad msg                = bad $'
  "(7) When checking _ has type " ++ showTy t ++ "\n" ++ msg
... | ok t' wt               with t ≟T t'
...   | (no ¬p)                = bad $'
  "(8) When checking _ has type " ++ showTy t
    ++ "\nGot "  ++ showTy t ++ "!= Expected "  ++ showTy t'
...   | (yes refl)             = ok t (chkinf wt)
-- chkType Γ (var x) t     = {!!}
-- chkType Γ (a · b) t     = {!!}
-- chkType Γ (a [ x ]) t   = {!!}
-- chkType Γ (a ·[ b ]) t  = {!!}
