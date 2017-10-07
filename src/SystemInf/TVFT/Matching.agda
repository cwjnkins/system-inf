module SystemInf.TVFT.Matching where

open import SystemInf.Prelude
open import SystemInf.Type.Curried

open TypeSubst using (_[/_])

import Level as ℓ
open import Category.Monad
open RawMonad {ℓ.zero} {M = Maybe} monad
  renaming (_>>=_ to _>>=M_ ; return to returnM)
import Data.Fin as Fin

unweakenTy : ∀ {n} → Fin (1 + n) → Type (1 + n) → Maybe (Type n)
unweakenTy x (var y) with Fin.compare x y
-- eq
unweakenTy x (var .x) | Fin.equal .x = nothing
-- less
unweakenTy .(Fin.inject _) (var zero) | Fin.less .zero ()
unweakenTy .(Fin.inject least) (var (suc y)) | Fin.less .(suc y) least
  = just (var y)
unweakenTy x (var .(Fin.inject least)) | Fin.greater .x least
  = just (var (help x least)) where
  help : ∀ {n} (x : Fin (suc n)) → Fin.Fin′ x → Fin n
  help {n} zero ()
  help {zero} (suc ()) y
  help {suc n} (suc x) zero = zero
  help {suc n} (suc x) (suc y) = suc $' help x y

unweakenTy x (s →' t) =
         unweakenTy x s >>=M
  λ s' → unweakenTy x t >>=M
  λ t' → returnM $' s' →' t'
unweakenTy x (∀' t)
  = unweakenTy (suc x) t >>=M
    λ t' → returnM $' ∀' t'

findVar : ∀ {n} → Fin (1 + n) → Type (1 + n) → Type n → Maybe (Type n)
findVar x (var y) t with x i≟ y
... | no ¬p = nothing
... | yes p = just t
findVar x (s₁ →' s₂) (t₁ →' t₂) with findVar x s₁ t₁
                                |    findVar x s₂ t₂
... | just t' | _ = just t'
... | nothing | just t' = just t'
... | nothing | nothing = nothing
findVar x (∀' s) (∀' t)
  =       findVar (suc x) s t >>=M
    λ u → unweakenTy zero u   >>=M
    λ u' → returnM u'
findVar _ _ _ = nothing
