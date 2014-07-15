module Free where

-- http://ro-che.info/articles/2013-03-31-flavours-of-free-applicative-functors.html

open import Agda.Primitive
open import Prelude
open import Builtin.Size

open import WellFounded

private
  ℕ : Set
  ℕ = Nat

  trans : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans refl refl = refl

  le-suc : (n m : ℕ) → n ≡ m → LessNat n (suc m)
  le-suc n .n refl = diffP zero refl

module Ap {ℓ₁ ℓ₂} (F : Set ℓ₁ -> Set ℓ₂) where
  data Free  (a : Set ℓ₁) : Set (lsuc ℓ₁ ⊔ ℓ₂) where
    Pure : a → Free a
    Ap   : {b : Set ℓ₁} → Free (b → a) → F b → Free a

  freeMap : {a b : Set ℓ₁} → (a → b) → Free a → Free b
  freeMap g (Pure x) = Pure (g x)
  freeMap g (Ap tx ay) = Ap (freeMap (λ h x → g (h x)) tx) ay

  FunctorFree : Functor Free
  FunctorFree = record { fmap = freeMap }

  -- Non structurally recursive
  {-
  freeAp : {a b : Set ℓ₁} → Free (a → b) → Free a → Free b
  freeAp (Pure g) tx = freeMap g tx
  freeAp (Ap tx ay) tz = Ap (freeAp (freeMap flip tx) tz) ay
  -}

  -- Definition using explicit size index
  freeSize : {a : Set ℓ₁} → Free a → ℕ
  freeSize (Pure _) = zero
  freeSize (Ap x _) = suc (freeSize x)

  freeMap-size-invariant : ∀ {a b} {f : a → b} (x : Free a) → freeSize (freeMap f x) ≡ freeSize x
  freeMap-size-invariant (Pure _) = refl
  freeMap-size-invariant (Ap x _) = cong suc (freeMap-size-invariant x)

  freeAp-index′ : {a b : Set ℓ₁} → (f : Free (a → b)) (n : ℕ) → freeSize f ≡ n → Free a → Free b
  freeAp-index′ (Pure g) _ _ tx = freeMap g tx
  freeAp-index′ (Ap tx ay) zero () tz
  freeAp-index′ (Ap tx ay) (suc n) pf tz = Ap (freeAp-index′ (freeMap flip tx) n pf' tz) ay
    where pf' = (trans (freeMap-size-invariant tx) (suc-inj pf))

  freeAp-index : {a b : Set ℓ₁} → Free (a → b) → Free a → Free b
  freeAp-index f x = freeAp-index′ f (freeSize f) refl x

  -- Definition using well founded induction, coq-y way.
  measure-type : Set (lsuc ℓ₁ ⊔ ℓ₂)
  measure-type = Σ (Set ℓ₁ × Set ℓ₁) (λ a → Free (fst a → snd a))

  freeApMeasure : measure-type → measure-type → Set
  freeApMeasure = LessMeasure (freeSize ∘ snd)

  freeApMeasure-wf : WellFounded freeApMeasure
  freeApMeasure-wf = WellFoundedMeasure (freeSize ∘ snd)

  freeAp-rec-type : measure-type → Set (ℓ₂ ⊔ lsuc ℓ₁)
  freeAp-rec-type ((a , b) , _) = Free a → Free b

  freeAp-rec-proof : {a b c : Set ℓ₁} (tx : Free (a → b → c)) →
                   LessNat (freeSize (freeMap flip tx))
                   (suc (freeSize tx))
  freeAp-rec-proof x = le-suc (freeSize (freeMap flip x)) (freeSize x) (freeMap-size-invariant x)

  freeAp-rec : (x : measure-type) → ((y : measure-type) → freeApMeasure y x → freeAp-rec-type y) → freeAp-rec-type x
  freeAp-rec ((a , b) , Pure g)   rec tx  = freeMap g tx
  freeAp-rec ((a , b) , Ap tx ay) rec tz  = Ap (rec ((a , _) , freeMap flip tx) (freeAp-rec-proof tx) tz) ay

  freeAp-wf : {a b : Set ℓ₁} → Free (a → b) → Free a → Free b
  freeAp-wf f = fix freeApMeasure freeAp-rec-type freeAp-rec (_ , f)

  -- ... more agda way, looks like you don't need to use fix
  freeAp-agda-wf′ : {a b : Set ℓ₁} → (f : Free (a → b)) → Acc freeApMeasure ((a , b) , f) → Free a → Free b
  freeAp-agda-wf′ (Pure g) _ tx = freeMap g tx
  freeAp-agda-wf′ {a = a} (Ap tx ay) (acc f) tz
    = Ap (freeAp-agda-wf′ (freeMap flip tx) (f ((a , _) , freeMap flip tx) (freeAp-rec-proof tx)) tz) ay

  freeAp-agda-wf : {a b : Set ℓ₁} → Free (a → b) → Free a → Free b
  freeAp-agda-wf  f = freeAp-agda-wf′ f (wf freeApMeasure (_ , f))

  -- sized types
  data SFree  (a : Set ℓ₁) : {_ : Size} -> Set (lsuc ℓ₁ ⊔ ℓ₂) where
    Pure : ∀ {i} → a → SFree a {↑ i}
    Ap   : ∀ {i} {b : Set ℓ₁} → SFree (b → a) {i} → F b → SFree a {↑ i}

  fromFree : ∀ {a} → Free a → SFree a
  fromFree (Pure x) = Pure x
  fromFree (Ap x x₁) = Ap (fromFree x) x₁

  toFree : ∀ {a} → SFree a → Free a
  toFree (Pure x) = Pure x
  toFree (Ap x x₁) = Ap (toFree x) x₁

  freeMap-sized : ∀ {i} {a b : Set ℓ₁} → (a → b) → SFree a {i} → SFree b {i}
  freeMap-sized g (Pure x) = Pure (g x)
  freeMap-sized g (Ap tx ay) = Ap (freeMap-sized (λ h x → g (h x)) tx) ay

  -- The below doesn't work as index is erased in between
  --  freeMap-sized f = fromFree ∘ freeMap f ∘ toFree

  -- And actually we can't use sized types here as there aren't + for Size.
  -- http://www2.tcs.ifi.lmu.de/~abel/talkAIM2008Sendai.pdf
  postulate
    freeAp-sized′ : {a b : Set ℓ₁} → SFree (a → b) → SFree a → SFree b
  {-
  freeAp-sized′ : {i j} {a b : Set ℓ₁} → SFree (a → b) {i} → SFree a {j} → SFree b {i + j}
  freeAp-sized′ (Pure g) tx = freeMap-sized g tx
  freeAp-sized′ (Ap tx ay) tz = Ap (freeAp-sized′ (freeMap-sized flip tx) tz) ay
  -}

  freeAp-sized : {a b : Set ℓ₁} → Free (a → b) → Free a → Free b
  freeAp-sized f x = toFree (freeAp-sized′ (fromFree f) (fromFree x))

  -- We can pick any
  ApplicativeFree : Applicative Free
  ApplicativeFree = record { pure = Pure ; _<*>_ = freeAp-index }
