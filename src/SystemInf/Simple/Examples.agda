module SystemInf.Simple.Examples where

open import SystemInf.Prelude
  hiding (id)
open import SystemInf.Type

open import SystemInf.Simple

module Terms where

  id : ∀ {m n} → Term m n
  id = Λ (λ' (var zero) (var zero))

  tt : ∀ {m n} → Term m n
  tt = Λ (λ' (var zero) (λ' (var zero) (var (suc zero))))

  ff : ∀ {m n} → Term m n
  ff = Λ (λ' (var zero) (λ' (var zero) (var zero)))

  pair : ∀ {m n} → (A B : Type n) → (u v : Term m n) → Term m n
  pair A B u v =
    let A' = TypeSubst.weaken A
        B' = TypeSubst.weaken B
        u' = TermTypeSubst.weaken (TermTermSubst.weaken u)
        v' = TermTypeSubst.weaken (TermTermSubst.weaken v)
    in Λ (λ' (A' →' B' →' var zero) (var zero · u' · v'))

  pair-test : TyInf {m = 0} {n = 0} [] (pair Types.𝔹 Types.𝔹 tt ff)
  pair-test = inferType [] (pair Types.𝔹 Types.𝔹 tt ff)

{-
Type inferred for pair-test:
(∀'
 ((∀' (var zero →' var zero →' var zero) →'
   ∀' (var zero →' var zero →' var zero) →' var zero)
  →' var zero))

Type of A × B
∀'
(∀' (var zero →' var zero →' var zero) →'
 ∀' (var zero →' var zero →' var zero) →' var zero)
-}
