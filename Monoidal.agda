module Monoidal where

open import Prelude
open import Data.List

-- | Heteregorenous n-ary function
--
-- we can represent any function type as list of paramater types and an result type
infixr 0 _⇉_
_⇉_ : ∀ {ℓ} → List (Set ℓ) → Set ℓ → Set ℓ
[]       ⇉ r = r
(x ∷ ps) ⇉ r = x → ps ⇉ r

module ⇉-example where
  type : Set
  type = Bool ∷ Nat ∷ Bool ∷ [] ⇉ Bool

  type' : type ≡ (Bool → Nat → Bool → Bool)
  type' = refl

  scalar : Set
  scalar = [] ⇉ Nat

  scalar' : scalar ≡ Nat
  scalar' = refl

compose1 : ∀ {ℓ} (as : List (Set ℓ)) {b c : Set ℓ} → (b → c) → (as ⇉ b) → (as ⇉ c)
compose1 []       f g    = f g
compose1 (a ∷ as) f g x  = compose1 as f (g x)

compose : ∀ {ℓ} (as : List (Set ℓ)) (ds : List (Set ℓ)) {b c : Set ℓ} →
  (as ⇉ (b → c)) → (ds ⇉ b) → ((as ++ ds) ⇉ c)
compose []       ds f g    = compose1 ds f g
compose (a ∷ as) ds f g x  = compose as ds (f x) g

lemma-compose1≡∘ : ∀ {ℓ} {a b c : Set ℓ}
                    {f : b -> c} {g : a -> b} →
                    compose1 (a ∷ []) f g ≡ f ∘ g
lemma-compose1≡∘ = refl

lemma-compose≡∘ : ∀ {ℓ} {a b c : Set ℓ}
                    {f : b -> c} {g : a -> b} →
                    compose [] (a ∷ []) f g ≡ f ∘ g
lemma-compose≡∘ = refl

-- Variadic apply. Not so interesting, but variation will be useful
applyN : ∀ {ℓ} (as : List (Set ℓ)) {b : Set ℓ} → (as ⇉ b) → All id as → b
applyN []       f []        = f
applyN (x ∷ as) f (p ∷ ps)  = applyN as (f p) ps

-- Variadic ap and lift
module ApplicativeN {ℓ₁ ℓ₂} {F : Set ℓ₁ → Set ℓ₂} {{ApplicativeF : Applicative F}} where
  apN : (as : List (Set ℓ₁)) {b : Set ℓ₁} → (F (as ⇉ b)) → (map F as ⇉ F b)
  apN [] f = f
  apN (a ∷ as) f x = apN as (f <*> x)

  liftAN : (as : List (Set ℓ₁)) {b : Set ℓ₁} → (as ⇉ b) → (map F as ⇉ F b)
  liftAN as f = apN as (pure f)

open ApplicativeN public

-- append of All objects
infixr 5 _All++_
_All++_ : ∀ {ℓ₁ ℓ₂} {a : Set ℓ₁} {P : a → Set ℓ₂} {xs ys : List a} → All P xs → All P ys → All P (xs ++ ys)
[]       All++ qs  = qs
(p ∷ ps) All++ qs  = p ∷ ps All++ qs

-- Free Applicative - Monoidal
module MonoidalModule {ℓ₁ ℓ₂} (F : Set ℓ₁ → Set ℓ₂) where
  data Monoidal (a : Set ℓ₁) : Set (lsuc ℓ₁ ⊔ ℓ₂) where
    mkMonoidal : (bs : List (Set ℓ₁)) → (xs : All F bs) → (bs ⇉ a) → Monoidal a

  monoidalMap : ∀ {a b} → (a → b) → Monoidal a → Monoidal b
  monoidalMap f (mkMonoidal as xs g) = mkMonoidal as xs (compose1 as f g)

  FunctorMonoidal : Functor Monoidal
  FunctorMonoidal = record { fmap = monoidalMap }

  monoidalPure : ∀ {a} → a → Monoidal a
  monoidalPure x = mkMonoidal [] [] x

  monoidalAp : ∀ {a b} → Monoidal (a → b) → Monoidal a → Monoidal b
  monoidalAp (mkMonoidal as xs f) (mkMonoidal bs ys g) = mkMonoidal (as ++ bs) (xs All++ ys) (compose as bs f g)

  ApplicativeMonoidal : Applicative Monoidal
  ApplicativeMonoidal = record { pure = monoidalPure ; _<*>_ = monoidalAp }

  liftMonoidal : ∀ {a} → F a → Monoidal a
  liftMonoidal {a = a} x = mkMonoidal (a ∷ []) (x ∷ []) id

  applyFN : (as : List (Set ℓ₁)) {b : Set ℓ₁} → (map F as ⇉ F b) → All F as → F b
  applyFN [] f [] = f
  applyFN (a ∷ as) f (p ∷ ps) = applyFN as (f p) ps

  lowerMonoidal : ∀ {a} {{ApplicativeF : Applicative F}} → Monoidal a → F a
  lowerMonoidal (mkMonoidal as xs f) = applyFN as (liftAN as f) xs

open MonoidalModule public

module MonoidalExample where
  a : List Nat
  a = 1 ∷ 2 ∷ []

  b : List Char
  b = 'a' ∷ 'b' ∷ 'c' ∷ []

  c : List Bool
  c = true ∷ false ∷ []

  triple : ∀ {ℓ} {a b c : Set ℓ} → a → b → c → (a × b × c)
  triple x y z = x , y , z

  FunctorMonoidalList : ∀ {a} → Functor (Monoidal (List {a}))
  FunctorMonoidalList = FunctorMonoidal List

  ApplicativeMonoidalList : ∀ {a} → Applicative (Monoidal (List {a}))
  ApplicativeMonoidalList = ApplicativeMonoidal List

  monoidal : Monoidal List (Nat × Char × Bool)
  monoidal = triple <$> a' <*> b' <*> c'
    where a' = liftMonoidal List a
          b' = liftMonoidal List b
          c' = liftMonoidal List c

  example : List (Nat × Char × Bool)
  example = lowerMonoidal List monoidal

  example' : List (Nat × Char × Bool)
  example' = triple <$> a <*> b <*> c

  proof : example ≡ example'
  proof = refl
