module SystemInf.Explicit.Examples where

open import SystemInf.Prelude
  hiding (id)
open import SystemInf.Type

open import SystemInf.Explicit

module Terms where
  open Types public

  ↑τ_ = TypeSubst.weaken
  ↑τt_ : ∀ {m n} → Term m n → Term (1 + m) (1 + n)
  ↑τt_ = TermTermSubst.weaken ∘ TermTypeSubst.weaken
  ↑Γ = CtxSubst.weaken

  -- left : ∀ {m n} → (A B : Type n) → (u : Term m n) → Term m n
  -- left A B u =
  --   Λ (λ' (↑τ A →' var zero) (λ' (↑τ B →' var zero) ({!!} · {!!})))

  -- Top
  id : ∀ {m n} → Term m n
  id = Λ (λ' (var zero) (var zero))

  app-id-id : ∀ {m n} → Term m n
  app-id-id = id [ Types.Top ] · id

  -- 𝔹
  tt : ∀ {m n} → Term m n
  tt = Λ (λ' (var zero) (λ' (var zero) (var (suc zero))))

  ff : ∀ {m n} → Term m n
  ff = Λ (λ' (var zero) (λ' (var zero) (var zero)))

  or : ∀ {m n} → Term m n
  or = λ' 𝔹 (λ' 𝔹 (var (suc zero) [ 𝔹 ] · tt · var zero))

  pair : ∀ {m n} → Term m n
  pair = Λ (Λ (λ' A (λ' B (Λ (λ' (A' →' B' →' var zero) (var zero · a · b))))))
    where
      A = var (suc zero)
      A' = var (suc (suc zero))
      B = var zero
      B' = var (suc zero)
      a = var (suc (suc zero))
      b = var (suc zero)

module WtTerm where
  open Terms

  -- Top
  wt-id : ∀ {m n} {Γ : Ctx m n} → Γ ⊢ id ∈ Top
  wt-id = Λ (λ' (var zero) (var zero))

  wt-id-test : ∀ {m n} {Γ : Ctx m n} → inferType Γ id ≡ ok Top wt-id
  wt-id-test = refl

  -- 𝔹
  wt-tt : ∀ {m n} {Γ : Ctx m n} → Γ ⊢ tt ∈ 𝔹
  wt-tt = Λ (λ' (var zero) (λ' (var zero) (var (suc zero))))

  wt-tt-test : ∀ {m n} {Γ : Ctx m n} → inferType Γ tt ≡ ok 𝔹 wt-tt
  wt-tt-test = refl

  wt-ff : ∀ {m n} {Γ : Ctx m n} → Γ ⊢ ff ∈ 𝔹
  wt-ff = Λ (λ' (var zero) (λ' (var zero) (var zero)))

  wt-ff-test : ∀ {m n} {Γ : Ctx m n} → inferType Γ ff ≡ ok 𝔹 wt-ff
  wt-ff-test = refl

  wt-or : ∀ {m n} {Γ : Ctx m n}
            → Γ ⊢ or ∈ 𝔹 →' 𝔹 →' 𝔹
  wt-or = λ' 𝔹 (λ' 𝔹 (var (suc zero) [ 𝔹 ] · wt-tt · var zero))

  wt-or-test : ∀ {m n} {Γ : Ctx m n} → inferType Γ or ≡ ok (𝔹 →' 𝔹 →' 𝔹) wt-or
  wt-or-test = refl

  wt-or-app : ∀ {m n} {Γ : Ctx m n}
               → {a b : Term m n}
               → (x : Γ ⊢ a ∈ 𝔹) → (y : Γ ⊢ b ∈ 𝔹)
               → Γ ⊢ or · a · b ∈ 𝔹
  wt-or-app x y = wt-or · x · y

  wt-pair-σ : ∀ {m} → Type m
  wt-pair-σ =
    ∀' (∀'
       let A = var (suc zero)
           B = var zero
       in A →' B →' A × B)

  wt-pair : ∀ {m n} {Γ : Ctx m n}
            → Γ ⊢ pair ∈ wt-pair-σ
  wt-pair = Λ (Λ (
    let A = var (suc zero)
        B = var zero
    in λ' A (λ' B (
          Λ (λ' (↑τ A →' ↑τ B →' var zero) (var zero · a · b))))))
    where
    a = var (suc (suc zero))
    b = var (suc zero)

  wt-pair-test : ∀ {m n} {Γ : Ctx m n}
                 → inferType Γ pair ≡ ok wt-pair-σ wt-pair
  wt-pair-test = refl
