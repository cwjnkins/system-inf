module SystemInf.Type.Curried where

open import SystemInf.Prelude
  hiding (List)

open import Data.Fin.Substitution
open import Relation.Binary using (Decidable)

-- Code borrowed from https://github.com/sstucki/system-f-agda
-- (Types, terms, etc)

infixr 7 _→'_

-- Types with n free variables
data Type (n : ℕ) : Set where
  var   : Fin n               → Type n
  _→'_  : (τ₁ τ₂ : Type n)    → Type n
  ∀'    : (τ : Type (1 + n))  → Type n

------------------------------------------------------------------------
-- Substitutions in types

module TypeSubst where
  module TypeApp {T} (l : Lift T Type) where
    open Lift l hiding (var)

    infixl 8 _/_

    -- Apply a substitution to a type
    _/_ : ∀ {m n} → Type m → Sub T m n → Type n
    var x       / σ = lift (lookup x σ)
    (τ₁ →' τ₂)  / σ = (τ₁ / σ) →' (τ₂ / σ)
    ∀' τ        / σ = ∀' (τ / σ ↑)

    open Application (record { _/_ = _/_})


  -- Defining the abstract members var and _/_ in
  -- Data.Fin.Substitution.TermSubst for T = Type gives us access to a
  -- number of (generic) substitution functions out-of-the-box.
  typeSubst : TermSubst Type
  typeSubst = record { var = var; app = TypeApp._/_ }

  open TermSubst typeSubst public hiding (var)

  weaken↑ : ∀ {n} → Type (1 + n) → Type (2 + n)
  weaken↑ a = a / wk ↑

  infix 8 _[/_]

  -- Shorthand for single-variable type substitutions
  _[/_] : ∀ {n} → Type (1 + n) → Type n → Type n
  a [/ b ] = a / sub b

open TypeSubst public
  using ()
  renaming (weaken to weakenTy)

open import Relation.Binary.PropositionalEquality.TrustMe

module TypeEquality where

  infix 4 _≡tp_ _≟n_

  -- Equal successors have equal predecessors.
  ≡suc : ∀ {n} {x y : Fin n} → Fin.suc x ≡ Fin.suc y → x ≡ y
  ≡suc refl = refl

  -- A decision procedure for equality of variable names.
  _≟n_ : ∀ {n} → Decidable {A = Fin n} _≡_
  zero  ≟n zero   = yes refl
  suc x ≟n suc y  with x ≟n y
  ... | yes x≡y   = yes (cong suc x≡y)
  ... | no  x≢y   = no (x≢y ∘ ≡suc)
  zero  ≟n suc y  = no λ()
  suc x ≟n zero   = no λ()

  -- A shorthand for (syntactic) type equality.
  _≡tp_ : ∀ {n} → Type n → Type n → Set
  a ≡tp b = a ≡ b

  -- Equal type variables have equal names.
  ≡var : ∀ {n} {x y : Fin n} → var x ≡tp var y → x ≡ y
  ≡var refl = refl

  -- Equal function types have equal domains.
  ≡dom→ : ∀ {n} {a a′ b b′ : Type n} → a →' b ≡tp a′ →' b′ → a ≡ a′
  ≡dom→ refl = refl

  -- Equal function types have equal codomains.
  ≡cod→ : ∀ {n} {a a′ b b′ : Type n} → a →' b ≡tp a′ →' b′ → b ≡ b′
  ≡cod→ refl = refl

  -- A decision procedure for (syntactic) type equality
  _≟T_ : ∀ {n} → Decidable {A = Type n} _≡_
  var x ≟T var y with x ≟n y
  ... | no ¬p                  = no (¬p ∘ ≡var)
  ... | yes refl               = yes refl
  (x →' x₁) ≟T (y →' y₁)
    with x ≟T y | x₁ ≟T y₁
  ... | no ¬p | _              = no (¬p ∘ ≡dom→)
  ... | yes p | (no ¬p)        = no (¬p ∘ ≡cod→)
  ... | yes refl | (yes refl)  = yes refl
  ∀' x ≟T ∀' y with x ≟T y
  ... | no ¬p                  = no TrustMe.unsafeNotEqual
  ... | yes refl               = yes refl
  x ≟T y                       = no TrustMe.unsafeNotEqual

open TypeEquality using (_≟T_; _≟n_) public

-- Some common types
module Types where
  private
    ↑_ = TypeSubst.weaken

  Top : ∀ {n} → Type n
  Top = ∀' (var zero →' var zero)
  --    ∀ X . X → X

  Bot : ∀ {n} → Type n
  Bot = ∀' (var zero)
  --    ∀ X . X

  _×_ : ∀ {n} → (A B : Type n) → Type n
  A × B = ∀' ((↑ A →' ↑ B →' var zero) →' var zero)

  Pair : ∀ {n} → Type n
  Pair = ∀' (∀' (var (suc zero) →' var zero →' var (suc zero) × var zero))

  Pair' : ∀ {n} → Type n
  Pair' = ∀' (var zero →' ∀' (var zero →' (var (suc zero) × var zero)))

  _∪_ : ∀ {n} →  (A B : Type n) → Type n
  A ∪ B = ∀' ((↑ A →' var zero) →' (↑ B →' var zero) →' var zero)

  𝔹 : ∀ {n} → Type n
  𝔹 = ∀' (var zero →' var zero →' var zero)

  If : ∀ {n} → Type n
  If = ∀' (𝔹 →' var zero →' var zero →' var zero)

  List : ∀ {n} → Type n → Type n
  List A = ∀' (var zero →' (↑ A →' var zero →' var zero) →' var zero)

  Nil' : ∀ {n} → Type (1 + n)
  Nil' = List (var zero)

  Nil : ∀ {n} → Type n
  Nil = ∀' Nil'

  Cons : ∀ {n} →  Type n
  Cons = ∀' (var zero →' List (var zero) →' List (var zero))

  Either : ∀ {n} → (A B : Type n) → Type n
  Either A B = ∀' ((↑ A →' var zero) →' (↑ B →' var zero) →' var zero)

  Left : ∀ {n} → Type n
  Left = ∀' (var zero →' ∀' (Either (var (suc zero)) (var zero)))

  Right : ∀ {n} → Type n
  Right = ∀' (var zero →' ∀' (Either (var zero) (var (suc zero))))

module _ where
-- Show
  open import Data.Fin using (toℕ)

  private
    freshNames : (n : ℕ) → Fin n → String
    freshNames n i = primShowChar ∘ primNatToChar ∘ ((123 ∸ n) +_) ∘ toℕ $ i

  -- go
  showTy : ∀ {n} → Type n → String
  showTy {n} (var x) = freshNames n x
  showTy (t →' t₁)   = "(" ++ showTy t ++ " → " ++ showTy t₁ ++ ")"
  showTy {n} (∀' t)  = "∀ " ++ freshNames (suc n) zero ++ ". " ++ showTy t

  private
    test : showTy {0} (∀' (var zero →' var zero)) ≡ "∀ 'z'. ('z' → 'z')"
    test = refl
