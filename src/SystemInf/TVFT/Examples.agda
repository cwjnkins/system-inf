module SystemInf.TVFT.Examples where

open import SystemInf.Prelude
  hiding (id)
open import SystemInf.Type
open import SystemInf.Ctx

open import SystemInf.TVFT

module Terms where
  open Types public

  ↑τ = weakenTy

  ↑τt_ : ∀ {m n} → Term m n → Term (1 + m) (1 + n)
  ↑τt_ = weakenTmTm ∘ weakenTmTy

  -- Top
  id' : Term'
  id' = Λ (λ' (var zero))

  id : Term'
  id = id' :: Top

  app-id-id : Term'
  app-id-id = id ·[ id ]

  -- 𝔹
  tt : Term'
  tt = Λ (λ' (λ' (var (suc zero)))) :: 𝔹

  ff : Term'
  ff = Λ (λ' (λ' (var zero))) :: 𝔹

  or : Term'
  or = (λ' $' λ' $' var (suc zero) ·[ tt ] · var zero) :: (𝔹 →' 𝔹 →' 𝔹)

  if : Term'
  if = (Λ{-X-} $' λ'{-c-} $' λ'{-t-} $' λ'{-e-} $'
       let c = var (suc (suc zero))
           t = var (suc zero)
           e = var zero
       in c ·[ t ] · e) :: If

  pair : Term'
  pair = (Λ{-A-} $' Λ{-B-} $' λ'{-a-} $' λ'{-b-} $'
           Λ{-X-} $' λ'{-p-} $'
           let p = var zero
               a = var (suc (suc zero))
               b = var (suc zero)
           in p · a · b)
         :: Pair

  pair-tt-id : Term'
  pair-tt-id = pair [ 𝔹 ] [ Top ] · tt · id'

  pair' : Term'
  pair' = (Λ{-A-} $' λ'{-a-} $' Λ{-B-} $' λ'{-b-} $'
            Λ{-X-} $' λ'{-p-} $'
            let p = var zero
                a = var (suc (suc zero))
                b = var (suc zero)
            in p · a · b)
          :: Pair'

  pair'-tt-id : Term'
  pair'-tt-id = pair' ·[ tt ] ·[ id ] -- note: not id'!

  nil : Term'
  nil = Λ{-U-} (Λ{-X-} (λ'{-n-} (λ'{-c-} (var (suc zero))))) :: Nil

  cons : Term'
  cons = (Λ{-U-} $' λ'{-u-} $' λ'{-xs-} $'
           Λ{-X-} $' λ'{-n-} $' λ'{-c-}
           let u  = var (suc (suc (suc zero)))
               xs = var (suc (suc zero))
               n  = var (suc zero)
               c  = var zero
           in c · u · (xs ·[ n ] · c))
         :: Cons

  list₁ : Term'
  list₁ = cons ·[ tt ] · (cons ·[ tt ] · (nil [ 𝔹 ]))

  list₂ : Term'
  list₂ = cons ·[ tt ] · (cons ·[ tt ] · (nil [·]))

module WtTerms where
  open Terms

  -- We can infer the annotated id'
  wt-id-test : ∀ {m n} {Γ : Ctx m n} → ∃ λ wt → infType Γ id ≡ ok Top wt
  wt-id-test = _ , refl

  -- We cannot infer the unannotated id'
  wt-id'-test : ∀ {m n} {Γ : Ctx m n} → infType Γ id' ≡ bad _
  wt-id'-test = refl

  wt-app-id-id : ∀ {m n} {Γ : Ctx m n} → ∃ λ wt → infType Γ app-id-id ≡ ok Top wt
  wt-app-id-id = _ , refl

  -- 𝔹
  wt-or-test : ∀ {m n} {Γ : Ctx m n} → ∃ λ wt → infType Γ or ≡ ok (𝔹 →' 𝔹 →' 𝔹) wt
  wt-or-test = _ , refl

  -- _×_
  wt-if-test : ∀ {m n} {Γ : Ctx m n} → ∃ λ wt → infType Γ if ≡ ok (∀' $' 𝔹 →' var zero →' var zero →' var zero) wt
  wt-if-test = _ , refl

  wt-pair-test : ∀ {m n} {Γ : Ctx m n} → ∃ λ wt → infType Γ pair ≡ ok Pair wt
  wt-pair-test = _ , refl

  wt-pair'-test : ∀ {m n} {Γ : Ctx m n} → ∃ λ wt → infType Γ pair' ≡ ok Pair' wt
  wt-pair'-test = _ , refl

  -- woo!
  wt-pair'-tt-id : ∀ {m n} {Γ : Ctx m n} →
                   ∃ λ wt → infType Γ pair'-tt-id ≡ ok (𝔹 × Top) wt
  wt-pair'-tt-id = _ , refl

  -- 𝕃
  wt-nil-test : ∀ {m n} {Γ : Ctx m n} → ∃ λ wt → infType Γ nil ≡ ok Nil wt
  wt-nil-test = _ , refl

  wt-cons-test : ∀ {m n} {Γ : Ctx m n} → ∃ λ wt →  infType Γ cons ≡ ok Cons wt
  wt-cons-test = _ , refl

  wt-list₁ : ∀ {m n} {Γ : Ctx m n} → ∃ λ wt → infType Γ list₁ ≡ ok (List 𝔹) wt
  wt-list₁ = _ , refl

  wt-list₂ : ∀ {m n} {Γ : Ctx m n} → ∃ λ wt → infType Γ list₂ ≡ ok (List 𝔹) wt
  wt-list₂ = _ , refl
