module SystemInf.Type.Uncurried where

open import SystemInf.Prelude

open import Data.Fin.Substitution
open import Relation.Binary using (Decidable)

infix 7 ∀<_,_>_→'_

data Type (n : ℕ) : Set where
  var   : Fin n               → Type n
  Top Bot : Type n
  ∀<_,_>_→'_ : ∀ m l → Vec (Type (m + n)) l → Type (m + n) → Type n
  -- type arguments, term arguments, result

module TypeSubst where
  import Data.List as List
  module TypeApp {T} (l : Lift T Type) where
    open Lift l hiding (var)

    infixl 8 _/_

    -- Apply a substitution to a type
    {-# TERMINATING #-}
    _/_ : ∀ {m n} → Type m → Sub T m n → Type n
    var x / σ = lift (lookup x σ)
    Top / σ = Top
    Bot / σ = Bot
    (∀< m , l > xs →' τ) / σ = ∀< m , l > map (_/ σ ↑⋆ m) xs →' (τ / σ ↑⋆ m)

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

module TypeEquality where
  open import Relation.Binary.PropositionalEquality.TrustMe

  infix 4 _≡tp_

  -- A shorthand for (syntactic) type equality.
  _≡tp_ : ∀ {n} → Type n → Type n → Set
  a ≡tp b = a ≡ b

  -- Equal type variables have equal names.
  ≡var : ∀ {n} {x y : Fin n} → var x ≡tp var y → x ≡ y
  ≡var refl = refl

  -- Equal function types have equal domains.
  ≡dom→ : ∀ {m n l} {ts₁ ts₂ : Vec _ l} {s₁ s₂ : Type (m + n)}
          → (∀< m , l > ts₁ →' s₁) ≡tp (∀< m , l > ts₂ →' s₂)
          → ts₁ ≡ ts₂
  ≡dom→ refl = refl


  -- Equal function types have equal codomains.
  ≡cod→ : ∀ {m n l} {ts₁ ts₂ : Vec _ l} {s₁ s₂ : Type (m + n)}
          → (∀< m , l  > ts₁ →' s₁) ≡tp (∀< m , l > ts₂ →' s₂)
          → s₁ ≡ s₂
  ≡cod→ refl = refl

  {-# TERMINATING #-}
  _T≟_ : ∀ {n} → Decidable {A = Type n} _≡_
  var x T≟ var y  with x i≟ y
  ... | no ¬p       = no (¬p ∘ ≡var)
  ... | yes refl    = yes refl
  Top T≟ Top      = yes refl
  Bot T≟ Bot      = yes refl
  (∀< m₁ , l₁ > (xs) →' τ₁)
      T≟ (∀< m₂ , l₂ > ys →' τ₂)
                 with m₁ ≟ m₂
  ... | no ¬p      = no (λ { refl → ¬p refl})
  ... | yes refl   with l₁ ≟ l₂
  ...   | (no ¬q)    = no λ { refl → ¬q refl }
  ...   | (yes refl) with (xs V≟ ys) _T≟_
  ...     | (no ¬r)    = no λ { refl → ¬r refl}
  ...     | (yes refl) with τ₁ T≟ τ₂
  ...       | (no ¬s)    = no λ { refl → ¬s refl}
  ...       | (yes refl) = yes refl
  _ T≟ _ = no TrustMe.unsafeNotEqual

