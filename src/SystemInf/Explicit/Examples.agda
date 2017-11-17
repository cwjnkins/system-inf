module SystemInf.Explicit.Examples where

open import SystemInf.Prelude
  hiding (id ; List ; ok ; bad)
open import SystemInf.Type.Curried
open import SystemInf.Ctx as Ctx
open Ctx.Curried

open import SystemInf.Explicit

module Terms where
  open Types public
  module T = Types

  ↑τ = weakenTy

  -- ↑τt_ : ∀ {m n} → Term m n → Term (1 + m) (1 + n)
  -- ↑τt_ = weakenTmTm ∘ weakenTmTy

  -- Top
  id : Term'
  id = Λ (λ' (var zero) (var zero))

  app-id-id : Term'
  app-id-id = id [ Top ] · id

  -- 𝔹
  tt : Term'
  tt = Λ (λ' (var zero) (λ' (var zero) (var (# 1))))

  ff : Term'
  ff = Λ (λ' (var zero) (λ' (var zero) (var zero)))

  or : Term'
  or = λ' 𝔹 (λ' 𝔹 (var (# 1) [ 𝔹 ] · tt · var zero))

  -- _×_
  pair : Term'
  pair = Λ (Λ (λ' A (λ' B (Λ (λ' (↑τ A →' ↑τ B →' var zero) (var zero · a · b))))))
    where
      A = var (# 1)
      B = var zero
      a = var (# 2)
      b = var (# 1)

  nil : Term'
  nil = Λ (Λ (λ' (var zero) (λ' (var (# 1) →' var zero →' var zero)
                 (var (# 1)))))

  cons : Term'
  cons = Λ {- U -} (λ' {- u -} (var zero) (λ' {- xs -} (List (var zero))
           (Λ {- X -} (λ' {- x -} (var zero) (λ' {- y -} (var (# 1) →' var zero →' var zero)
                  let X  = var zero
                      u  = var (# 3)
                      xs = var (# 2)
                      x  = var (# 1)
                      y  = var zero
                  in (y · u · (xs [ X ] · x · y)))))))

  list : Term'
  list = cons [ 𝔹 ] · tt · (cons [ 𝔹 ] · tt · (nil [ 𝔹 ]))

  -- Either
  isLeftTrue : Term'
  isLeftTrue = λ' (T.Either 𝔹 Top) $' var zero [ 𝔹 ] · (id [ 𝔹 ]) · λ' Top ff

module WtTerm where
  open Terms

  -- Top
  wt-id : ∀ {m n} {Γ : Ctx m n} → Γ ⊢ id ∈ Top
  wt-id = Λ (λ' (var zero) (var zero))

  wt-id-test : ∀ {m n} {Γ : Ctx m n} → inferType Γ id ≡ ok Top wt-id
  wt-id-test = refl

  wt-app-id-id : ∀ {m n} {Γ : Ctx m n} → Γ ⊢ app-id-id ∈ Top
  wt-app-id-id = (wt-id [ Top ]) · wt-id

  wt-app-id-id-test : ∀ {m n} {Γ : Ctx m n} → inferType Γ app-id-id ≡ ok Top wt-app-id-id
  wt-app-id-id-test = refl

  -- 𝔹
  wt-tt : ∀ {m n} {Γ : Ctx m n} → Γ ⊢ tt ∈ 𝔹
  wt-tt = Λ (λ' (var zero) (λ' (var zero) (var (# 1))))

  wt-tt-test : ∀ {m n} {Γ : Ctx m n} → inferType Γ tt ≡ ok 𝔹 wt-tt
  wt-tt-test = refl

  wt-ff : ∀ {m n} {Γ : Ctx m n} → Γ ⊢ ff ∈ 𝔹
  wt-ff = Λ (λ' (var zero) (λ' (var zero) (var zero)))

  wt-ff-test : ∀ {m n} {Γ : Ctx m n} → inferType Γ ff ≡ ok 𝔹 wt-ff
  wt-ff-test = refl

  wt-or : ∀ {m n} {Γ : Ctx m n}
            → Γ ⊢ or ∈ 𝔹 →' 𝔹 →' 𝔹
  wt-or = λ' 𝔹 (λ' 𝔹 (var (# 1) [ 𝔹 ] · wt-tt · var zero))

  wt-or-test : ∀ {m n} {Γ : Ctx m n} → inferType Γ or ≡ ok (𝔹 →' 𝔹 →' 𝔹) wt-or
  wt-or-test = refl

  wt-or-app : ∀ {m n} {Γ : Ctx m n}
               → {a b : Term m n}
               → (x : Γ ⊢ a ∈ 𝔹) → (y : Γ ⊢ b ∈ 𝔹)
               → Γ ⊢ or · a · b ∈ 𝔹
  wt-or-app x y = wt-or · x · y

  wt-pair : ∀ {m n} {Γ : Ctx m n}
            → Γ ⊢ pair ∈ Pair
  wt-pair = Λ (Λ (
    let A = var (# 1)
        B = var zero
    in λ' A (λ' B (
          Λ (λ' (↑τ A →' ↑τ B →' var zero) (var zero · a · b))))))
    where
    a = var (# 2)
    b = var (# 1)

  wt-pair-test : ∀ {m n} {Γ : Ctx m n}
                 → inferType Γ pair ≡ ok Pair wt-pair
  wt-pair-test = refl

  wt-nil-test : ∀ {m n} {Γ : Ctx m n} → ∃ λ wt → inferType Γ nil ≡ ok Nil wt
  wt-nil-test = _ , refl

  wt-cons-test : ∀ {m n} {Γ : Ctx m n}
                 → ∃ λ wt → inferType Γ cons ≡ ok Cons wt
  wt-cons-test = _ , refl

  wt-list-test : ∀ {m n} {Γ : Ctx m n} → ∃ λ wt
                 → inferType Γ list ≡ ok (List 𝔹) wt
  wt-list-test = _ , refl

   -- erase the wt at the end for an example of what we /don't/ want for type errors :)
  wt-isLeftTrue-test : ∀ {m n} {Γ : Ctx m n}
                       → ∃ λ wt → inferType Γ isLeftTrue ≡ ok (T.Either 𝔹 Top →' 𝔹) wt
  wt-isLeftTrue-test = _ , refl
