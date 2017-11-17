module SystemInf.TVFC.Matching where

open import SystemInf.Prelude
open import SystemInf.Type.Curried

open TypeSubst using (_[/_])

open import Data.Vec.All as All
  hiding (lookup ; map ; tabulate ; zipWith)
open import Relation.Unary

import Level as ℓ
open import Category.Monad
open RawMonad {ℓ.zero} {M = Maybe} monad
  renaming (_>>=_ to _>>=M_ ; return to returnM)

import Data.Fin as Fin

open import Data.Nat.Properties.Simple

open import Relation.Binary.PropositionalEquality

data Constraint (n : ℕ) : Set where
  empty  : Constraint n
  solved : Type n → Constraint n
  contra : ∀ {m} → Vec (∃ λ n → Type n) m → Constraint n 

data SolvedC {n : ℕ} : Constraint n → Set where
  solved : (t : Type n) → SolvedC (solved t)

data NotContraC {n : ℕ} : Constraint n → Set where
  solved : (t : Type n) → NotContraC (solved t)
  empty  : NotContraC empty

Constraints : (m n : ℕ) → Set
Constraints m n = Vec (Constraint n) m

unweaken : ∀ {n} → Fin (suc n) → Type (suc n) → Maybe $' Type n
unweaken x (var x') with Fin.compare x x'
... | Fin.equal .x = nothing
unweaken .(Fin.inject _) (var zero)
    | Fin.less .zero ()
unweaken .(Fin.inject least) (var (suc x'))
    | Fin.less .(suc x') least = just $' var x'
... | Fin.greater .x least = just $' var (Fin.inject! least)
unweaken x (t₁ →' t₂) =
  unweaken x t₁ >>=M λ t₁' →
  unweaken x t₂ >>=M λ t₂' →
  just $' t₁' →' t₂' 
unweaken x (∀' t) =
  unweaken (suc x) t >>=M λ t' →
  just $' ∀' t'


private
  module T = Types
  open import Data.Unit

  t₁ : Type 0
  t₁ = T.List T.𝔹

  t₂ : Type 1
  t₂ = T.List T.𝔹

  t₂' : Type 0
  t₂' = from-just (unweaken zero t₂)

  t₃ : Type 1
  t₃ = T.List (var zero)

  t₃' : ℓ.Lift ⊤
  t₃' = from-just (unweaken zero t₃)


module _ {m n : ℕ} where
  isSolvedC : (Xs : Constraints m n) → Dec (All SolvedC Xs)
  isSolvedC = all $' λ { empty      → no (λ ())
                      ; (solved x) → yes (solved x)
                      ; (contra x) → no (λ ())}

  isContraC : (Xs : Constraints m n) → Dec (All NotContraC Xs)
  isContraC = all $' λ { empty      → yes empty
                      ; (solved x) → yes (solved x)
                      ; (contra x) → no (λ ())}

  solve : Type n → Constraint n → Constraint n
  solve t empty = solved t
  solve t (contra ts) = contra $' (, t) ∷ ts
  solve t c@(solved t') with t ≟T t'
  ... | no ¬p = contra ((, t) ∷ (, t') ∷ [])
  ... | yes p = c

  solveC : Type n → Fin m → Constraints m n → Constraints m n
  solveC t x Xs with lookup x Xs
  ... | c = Xs [ x ]≔ (solve t c) 

  emptyC : Constraints m n
  emptyC = replicate empty

  mergeC : (Xs Ys : Constraints m n) → Constraints m n
  mergeC = 𝕍zipWith λ
    { empty c₂ → c₂
    ; c₁ empty → c₁
    ; (solved t) c₂ → solve t c₂
    ; c₁ (solved t) → solve t c₁
    ; (contra ts₁) (contra ts₂) → contra $' ts₁ ++𝕍 ts₂ }

  weakenC : Constraints m n → Constraints m (suc n)
  weakenC = map λ { empty → empty
                  ; (solved t) → solved (weakenTy t)
                  ; (contra ts) → contra $' map (λ {(_ , t) → , weakenTy t}) ts}

  unweakenC : Constraints m (suc n) → Constraints m n
  unweakenC = map λ { empty → empty
                    ; (solved t) → case unweaken zero t of
                      λ { (just t') → solved t'
                        ; nothing → contra ((, t) ∷ [])}
                    ; (contra ts) → contra ts}

matchType : ∀ m {n} → Type (m + n) → Type n → Error $' Constraints m n
matchType m {n} (var x) t'
  with splitFin n (subst Fin (+-comm m n) x)
  -- we're constraining this variable
... | right x' = ok $' solveC t' x' emptyC
  -- we're not constraining this variable
matchType m {n} (var x) (var x')
    | left y with x' i≟ y
  -- and we compared it with a non-equal variable
...   | (no ¬p) = bad $' "1) " ++ showTy (var y) ++ " != " ++ showTy (var x)
  -- and we compared it to the same variable
...   | (yes p) = ok $' emptyC
matchType m {n} (var x) t'
    | left y = bad $' "2) " ++ showTy (var x) ++ " != " ++ showTy t'
matchType m (s →' t) (s' →' t')
  = matchType m s s' >>=E λ Xs →
    matchType m t t' >>=E λ Ys →
    ok $' mergeC Xs Ys
matchType m {n} (∀' t) (∀' t') rewrite sym (+-suc m n)
  = matchType m t t' >>=E λ Xs → -- matchType m t t' >>=E λ Xs → ok $' unweakenC Xs
    ok $' unweakenC Xs
matchType m t t' = bad $' "3) " ++ showTy t ++ " != " ++ showTy t'

private
  open Types
  module _ {n : ℕ} where
    t₄ : Type n
    t₄ = T.List 𝔹

    t₅ : Type (suc n)
    t₅ = T.List (var zero)

    t₆ : Type n
    t₆ = 𝔹 × Top

    t₇ : Type $' 2 + n
    t₇ = (var zero) × (var (suc zero))

    t₇' : Type $' 2 + n
    t₇' = (var zero) × var zero

  test₁ : matchType 1 {0} t₅ t₄ ≡ right (solved 𝔹 ∷ [])
  test₁ = refl

  test₂ : matchType 2 {0} t₇ t₆ ≡ right (solved 𝔹 ∷ solved Top ∷ [])
  test₂ = refl

  test₃ : matchType 2 {0} t₇' t₆ ≡ right (contra ((, 𝔹) ∷ (, Top) ∷ []) ∷ empty ∷ [])
  test₃ = refl
