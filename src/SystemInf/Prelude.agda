module SystemInf.Prelude where

open import Data.Nat            public
open import Data.Fin as Fin
  using (Fin ; zero ; suc)      public
open import Data.Vec            public
  hiding ([_])
  renaming (_++_ to _++𝕍_)
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
open import Data.Maybe          public
  hiding (map; decSetoid; setoid)

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


