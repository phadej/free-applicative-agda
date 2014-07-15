module WellFounded where

open import Agda.Primitive
open import Prelude

-- open import Control.WellFounded

module Definitions {ℓ ℓᵣ} {A : Set ℓ} (_<_ : A → A → Set ℓᵣ) where
  data Acc (x : A) : Set (ℓ ⊔ ℓᵣ) where
    acc : (∀ y → y < x → Acc y) → Acc x

  record WellFounded : Set (ℓ ⊔ ℓᵣ) where
    field wf : (x : A) → Acc x

  open WellFounded {{...}} public

  module Fixpoint {ℓ₂} (P : A → Set ℓ₂)  (F : (x : A) → ((y : A) → y < x → P y) → P x) where
    fix-F : {x : A} → Acc x → P x
    fix-F (acc H) = F _ (λ y pf → fix-F (H y pf))

    fix : (x : A) {{wfA : WellFounded}} → P x
    fix x = fix-F (wf x)

  open Fixpoint public

open Definitions public

-- Some nat mungling lemmas
private
  ℕ : Set
  ℕ = Nat

  trans : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans refl refl = refl

  plus-n-Sm : (n : ℕ) {m : ℕ} → suc (n + m) ≡ n + suc m
  plus-n-Sm zero    = refl
  plus-n-Sm (suc n) = cong suc (plus-n-Sm n)

  plus-assoc : (n : ℕ) {m p : ℕ} → n + m + p ≡ n + (m + p)
  plus-assoc zero    = refl
  plus-assoc (suc n) = cong suc (plus-assoc n)

  plus-inj₁ : (n : ℕ) {m p : ℕ} → m ≡ p → n + m ≡ n + p
  plus-inj₁ zero x = x
  plus-inj₁ (suc n) x = cong suc (plus-inj₁ n x)

  Nat-le-lt-trans : ∀ {n m p} → LessNat n m → LessNat m (suc p) → LessNat n p
  Nat-le-lt-trans (diffP k eq) (diffP k₁ eq₁) = diffP (k₁ + k)
    (trans (suc-inj eq₁) (trans (plus-inj₁ k₁ eq) (trans (sym (plus-n-Sm k₁)) (sym (cong suc (plus-assoc k₁))))))

module Measure {ℓ} {A : Set ℓ} (measure : A → ℕ) where
  LessMeasure : A → A → Set
  LessMeasure x y = LessNat (measure x) (measure y)

  private
    measure-wf' : (n : Nat) (x : A) → LessNat (measure x) n → Acc LessMeasure x
    measure-wf' zero x (diffP k ())
    measure-wf' (suc n) x pf = acc (λ y pf' → measure-wf' n y (Nat-le-lt-trans pf' pf))

  measure-wf : (x : A) → Acc LessMeasure x
  measure-wf x = acc λ { y pf → measure-wf' (suc (measure y)) y (diffP zero refl) }

  WellFoundedMeasure : WellFounded LessMeasure
  WellFoundedMeasure = record { wf = measure-wf }

open Measure public

WellFoundedNat : WellFounded LessThan
WellFoundedNat = WellFoundedMeasure id

-- Demo
module fix-example where
  plus-rec : ∀ x → (∀ y → LessNat y x → ℕ → ℕ) → ℕ → ℕ
  plus-rec zero rec y = y
  plus-rec (suc x) rec y = suc (rec x (diffP zero refl) y)

  plus : ℕ → ℕ → ℕ
  plus x = fix LessNat (λ _ → ℕ → ℕ) plus-rec x

  example : plus 12 30 ≡ 42
  example = refl
