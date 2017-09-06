module SystemInf.Simple.Examples where

open import SystemInf.Prelude
  hiding (id)
open import SystemInf.Type
open import SystemInf.Ctx

open import SystemInf.Simple

module Terms where
  open Types public

  ↑τ_ = weakenTy

  ↑τt_ : ∀ {m n} → Term m n → Term (1 + m) (1 + n)
  ↑τt_ = weakenTmTm ∘ weakenTmTy

  -- Top
  id : Term'
  id = Λ (λ'(var zero)) :: Top

  id' : Term'
  id' = Λ (λ'(var zero))

  app-id-id' : Term'
  app-id-id' = id [ Types.Top ] · id'

  -- 𝔹
  tt : Term'
  tt = Λ (λ' (λ' (var (suc zero)))) :: 𝔹

  or : Term'
  or = λ' (λ' (var (suc zero) [ 𝔹 ] · tt · var zero)) :: (𝔹 →' 𝔹 →' 𝔹)

  if : Term'
  if = Λ (λ' (λ' (λ'
         (var (suc (suc zero)) [ var zero ] · var (suc zero) · var zero))))
       :: If

  pair : Term'
  pair = Λ (Λ (λ' (λ'
           (Λ (λ' (var zero · var (suc (suc zero))
                            · (var (suc zero))))))))
         :: Pair

  pair-tt-id : Term'
  pair-tt-id = pair [ 𝔹 ] [ Top ] · tt · id'

  pair-tt-id-bad : Term'
  pair-tt-id-bad = pair · tt · id'

  nil : Term'
  nil = Λ{-U-} (Λ{-X-} (λ'{-n-} (λ'{-c-} (var (suc zero))))) :: Nil

  cons : Term'
  cons = Λ{-U-} (λ'{-u-} (λ'{-xs-} (Λ{-X-} (λ'{-x-} (λ'{-y-}
         let X  = var zero
             u  = var (suc (suc (suc zero)))
             xs = var (suc (suc zero))
             x  = var (suc zero)
             y  = var zero
         in y · u · (xs [ X ] · x · y))))))
         :: Cons

module WtTerms where
  open Terms

  wt-id-test : ∀ {m n} {Γ : Ctx m n} → ∃ (λ wt → infType Γ id ≡ ok Top wt)
  wt-id-test = _ , refl

  -- We cannot infer the unannotated id'
  wt-id'-test₁ : ∀ {m n} {Γ : Ctx m n} → infType Γ id' ≡ bad _
  wt-id'-test₁ = refl

  -- We can infer id applied to id'
  wt-app-id-id' : ∀ {m n} {Γ : Ctx m n} → ∃ λ wt → infType Γ app-id-id' ≡ ok Top wt
  wt-app-id-id' = _ , refl

  -- 𝔹
  wt-tt-test : ∀ {m n} {Γ : Ctx m n} → ∃ λ wt → infType Γ tt ≡ ok 𝔹 wt
  wt-tt-test = _ , refl

  wt-or-test : ∀ {m n} {Γ : Ctx m n} → ∃ λ wt → infType Γ or ≡ ok (𝔹 →' 𝔹 →' 𝔹) wt
  wt-or-test = _ , refl

  wt-if-test : ∀ {m n} {Γ : Ctx m n} → ∃ λ wt → infType Γ if ≡ ok If wt
  wt-if-test = _ , refl

  -- _×_
  wt-pair-test : ∀ {m n} {Γ : Ctx m n} →
                 ∃ λ wt → infType Γ pair ≡ ok Pair wt
  wt-pair-test = _ , refl

  wt-pair-tt-id-test : ∀ {m n} {Γ : Ctx m n} →
                       ∃ λ wt → infType Γ pair-tt-id ≡ ok (𝔹 × Top) wt
  wt-pair-tt-id-test = _ , refl

  wt-pair-tt-id-bad : ∀ {m n} {Γ : Ctx m n} →
                        infType Γ pair-tt-id-bad ≡ bad _
  wt-pair-tt-id-bad = refl

  -- 𝕃
  wt-nil-test : ∀ {m n} {Γ : Ctx m n} → ∃ λ wt → infType Γ nil ≡ ok Nil wt
  wt-nil-test = _ , refl

  wt-cons-test : ∀ {m n} {Γ : Ctx m n} → ∃ λ wt → infType Γ cons ≡ ok Cons wt
  wt-cons-test = _ , refl
