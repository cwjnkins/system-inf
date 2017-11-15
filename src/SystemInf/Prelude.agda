module SystemInf.Prelude where

open import Data.Nat            public
  hiding (_⊔_)
open import Data.Fin as Fin
  using (Fin ; zero ; suc ; #_) public
open import Data.Fin.Properties public
  using (suc-injective)
  renaming (_≟_ to _i≟_)
open import Data.Vec            public
  hiding ([_])
  renaming (_++_ to _++𝕍_ ; zipWith to 𝕍zipWith)
open import Data.List as List   public
  using (_∷_ ; []; List)
open import Data.Char           public
  using (Char)
open import Data.String         public
  renaming (_≟_ to _≟𝕊_)
  hiding (fromList ; toList ; decSetoid ; setoid)
open import Data.Empty
open import Data.Product        public
  hiding (map; zip; _×_)
open import Data.Sum
  hiding (map)
open import Data.Maybe          public
  hiding (map; decSetoid; setoid; All)
open import Data.Bool           public
  hiding (_≟_; decSetoid)

open import Relation.Binary.PropositionalEquality
                                public
  hiding ([_] ; subst)
open import Relation.Nullary    public

open import Function            public

open import Agda.Builtin.Char   public
   using (primNatToChar)
open import Agda.Builtin.String public
  using (primShowChar)

-- non-dependent _$_
infixr 0 _$'_
_$'_ : ∀ {a b} {A : Set a} {B : Set b} →
       (f : A → B) → (x : A) → B
f $' x = f x

module TrustMe where

  private postulate erasedBottom : ⊥

  erase-⊥ : ⊥ → ⊥
  erase-⊥ _ = erasedBottom

  open import Relation.Binary.PropositionalEquality.TrustMe public

  unsafeNotEqual : ∀ {a} {A : Set a} {x y : A} → ¬ (x ≡ y)
  unsafeNotEqual _ = erasedBottom

module VecEq where
  open import Level
  _V≟_ : ∀ {ℓ} {m} {A : Set ℓ}
         → (xs ys : Vec A m)
         → (_A≟_ : (a b : A) → Dec (a ≡ b)) → Dec (xs ≡ ys)
  ([] V≟ []) _A≟_  = yes refl
  ((x ∷ xs) V≟ (y ∷ ys)) _A≟_
                  with x A≟ y
  ... | no ¬p        = no (λ { refl → ¬p refl})
  ... | yes refl     with (xs V≟ ys) _A≟_
  ...   | (no ¬q)      = no λ { refl → ¬q refl}
  ...   | (yes refl)   = yes refl

open VecEq public

module VecAll where
  open import Data.Vec.All

  toAll₂ : ∀ {a p} {l} {A B : Set a} {P : A → B → Set p}
           → (xs : Vec A l) → (ys : Vec B l)
           → (p? : (x : A) → (y : B) → Maybe (P x y))
           → Maybe (All₂ P xs ys)
  toAll₂ [] [] p? = just []
  toAll₂ (x ∷ xs) (y ∷ ys) p? with p? x y
  ... | nothing = nothing
  ... | just pxy with toAll₂ xs ys p?
  ... | nothing = nothing
  ... | (just all-pxy) = just $' pxy ∷ all-pxy

module Either where
  open import Level
  Either : ∀ {a b} → (A : Set a) → (B : Set b) → Set (a ⊔ b)
  Either A B = A ⊎ B

  pattern left  a = inj₁ a
  pattern right b = inj₂ b

open Either public

module SplitFin where

  splitFin : ∀ {n} k → Fin (k + n) → Either (Fin k) (Fin n)
  splitFin zero i = right i
  splitFin (suc k) zero = left zero
  splitFin (suc k) (suc i) with splitFin k i
  ... | left  x = left (suc x)
  ... | right y = right y

open SplitFin public

