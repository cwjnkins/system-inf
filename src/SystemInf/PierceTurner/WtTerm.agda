module SystemInf.PierceTurner.WtTerm where

open import SystemInf.Prelude
open import SystemInf.Type.Uncurried
open import SystemInf.Ctx as Ctx
open Ctx.Uncurried

open import SystemInf.PierceTurner.Term

open import Data.Vec.All
  hiding (lookup ; map)

open TypeSubst using ()
  renaming (_[/_] to _[/tp_] ; _/_ to _/tp_)

data WtMode : Set where
  chk inf : WtMode

infix 4 _⊢_m:_∈_
data _⊢_m:_∈_ {m n} (Γ : Ctx m n) : ETerm m n → WtMode → Type n → Set where
  var : ∀ (x : Fin m) →
        ---------------
        Γ ⊢ var x m: inf ∈ lookup x Γ
  fun[X=_]x=_ : ∀ k l →
                (Ts : Vec (Type $' k + n) l) →
                {e : ETerm (l + m) (k + n)} →
                {S : Type $' k + n} →
                (Ts ++𝕍 weakenCtx⋆ k Γ) ⊢ e m: inf ∈ S →
                ------------------------------
                Γ ⊢ (fun[X= k ]x:T= l , Ts) e
                  m: inf ∈ ∀< k , l > Ts →' S
  -- if you're having trouble with just the specification...
  _[_]·_ : ∀ {x s} {Ss : Vec (Type $' x + n) s} {R : Type $' x + n}
           → {f : ETerm m n}
             (wt-f : Γ ⊢ f m: inf ∈ ∀< x , s > Ss →' R)
           → (Ts : Vec (Type n) x)
           → {es : Vec (ETerm m n) s}
             {Us : Vec (Type n) s}
             (wt-es : All₂ (λ e U → Γ ⊢ e m: inf ∈ U) es Us)
           → (Us<:Ss : All₂ (_<:_ {n}) Us (map (λ S → S /tp subsTy _ Ts) Ss))
           → Γ ⊢ f [ Ts ]· es m: inf ∈ R /tp subsTy _ Ts

