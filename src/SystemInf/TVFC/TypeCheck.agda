module SystemInf.TVFC.TypeCheck where

open import SystemInf.Prelude
open import SystemInf.Type.Curried
open import SystemInf.Ctx as Ctx
open Ctx.Curried

open import SystemInf.TVFC.Term
open import SystemInf.TVFC.WtTerm

open import Relation.Binary.PropositionalEquality
  as PropEq
  using ()


-- Type synthesis
data TySyn {m n} (Γ : Ctx m n) : Term m n → Set where
  ok  : ∀ {a} t → (wt : Γ ⊢ a m: inf ∈ t) → TySyn Γ a
  bad : ∀ {a} → (msg : String) → TySyn Γ a

-- Type checking
data TyChk {m n} (Γ : Ctx m n) : Term m n → Type n → Set where
  ok  : ∀ {a} t → (wt : Γ ⊢ a m: chk ∈ t) → TyChk Γ a t
  bad : ∀ {a t} → (msg : String) → TyChk Γ a t

synType : ∀ {m n} (Γ : Ctx m n) a   → TySyn Γ a
chkType : ∀ {m n} (Γ : Ctx m n) a t → TyChk Γ a t

synType Γ a = {!!}

chkType Γ (Λ a) t = {!!}
chkType Γ (λ' a) t = {!!}
chkType Γ (a [ x ]) t = {!!}
chkType Γ (a · a₁) t = {!!}
chkType Γ (a [·]) t
  with synType Γ a
  -- error synthesizing
... | bad msg = bad $' msg
  -- synthesized non-polymorphic type
... | ok (var x) wt = bad $' ""
... | ok (t' →' t'') wt = bad $' ""
  -- synth polymorphic type
... | ok (∀' t') wt = {!!}

-- synthesize type, then check equal to incoming type
chkType Γ a t with synType Γ a
... | bad msg     = bad $' msg
... | ok t' wt with t ≟T t'
... | (no ¬p)     = bad $' ""
... | (yes refl)  = ok t' (chkinf wt)
