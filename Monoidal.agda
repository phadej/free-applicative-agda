module Monoidal where

open import Prelude
open import Data.List

Extensionality : (a b : Level) → Set _
Extensionality a b =
  {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
  (∀ x → f x ≡ g x) → f ≡ g

infix 4 _≅_

data _≅_ {ℓ} {A : Set ℓ} (x : A) : {B : Set ℓ} → B → Set ℓ where
   refl : x ≅ x

postulate
  extensionality : (a b : Level) → Extensionality a b

cong-dep : ∀ {a b} {A : Set a} {B : A → Set b}
        (f : (x : A) → B x) {x y} → x ≅ y → f x ≅ f y
cong-dep f refl = refl

cong-dep₂ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c}
          {x y u v}
        (f : (x : A) (y : B x) → C x y) → x ≅ y → u ≅ v → f x u ≅ f y v
cong-dep₂ f refl refl = refl

cong-dep₃ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c} {D : ∀ x → (y : B x) → C x y → Set d}
          {x y u v z w}
        (f : (x : A) (y : B x) (z : C x y) → D x y z) → x ≅ y → u ≅ v → z ≅ w → f x u z ≅ f y v w
cong-dep₃ f refl refl refl = refl

≡-to-≅ : ∀ {a} {A : Set a} {x y : A} → x ≡ y → x ≅ y
≡-to-≅ refl = refl

≅-to-≡ : ∀ {a} {A : Set a} {x y : A} → x ≅ y → x ≡ y
≅-to-≡ refl = refl

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

postulate
  lemma-compose-[] : ∀ {ℓ} {a b : Set ℓ} →
     (bs : List (Set ℓ)) (y : a) → (x : bs ⇉ (a → b)) → compose bs [] x y ≅ compose1 bs (λ f → f y) x
{-
lemma-compose-[] [] y x = refl
lemma-compose-[] {ℓ} (x ∷ bs) y x₁ = {! !}
-- (λ x₂ → compose bs [] (x₁ x₂) y) ≅ (λ x₂ → compose1 bs (λ f → f y) (x₁ x₂))
-- Do we need heterogenous-extensionality?
-}

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

l++[]≡l : ∀ {ℓ} {a : Set ℓ} (l : List a) → l ++ [] ≡ l
l++[]≡l [] = refl
l++[]≡l (x ∷ l) = cong (λ l′ → x ∷ l′) (l++[]≡l l)

l-All++[]≡l : ∀ {ℓ₁ ℓ₂} {a : Set ℓ₁} {P : a → Set ℓ₂} (l : List a) → All P (l ++ []) ≡ All P l
l-All++[]≡l l = cong (λ l′ → All _ l′) (l++[]≡l l)

postulate
  lemma-All++[] : ∀ {a b} {A : Set a } {P : A → Set b} {l : List A} → (xs : All P l) → xs All++ [] ≅ xs
{-
lemma-All++[] [] = refl
lemma-All++[] (p ∷ ps) = {!!}
-- p ∷ ps All++ [] ≅ p ∷ ps
-- I can't get cong-dep₂ to work (I guess I need cong-dep₂)
-}

-- Free Applicative - Monoidal
module MonoidalModule {ℓ₁ ℓ₂} (F : Set ℓ₁ → Set ℓ₂) where
  data Monoidal (a : Set ℓ₁) : Set (lsuc ℓ₁ ⊔ ℓ₂) where
    mkMonoidal : (bs : List (Set ℓ₁)) → (xs : All F bs) → (bs ⇉ a) → Monoidal a

  monoidalMap : ∀ {a b} → (a → b) → Monoidal a → Monoidal b
  monoidalMap f (mkMonoidal as xs g) = mkMonoidal as xs (compose1 as f g)

  monoidalPure : ∀ {a} → a → Monoidal a
  monoidalPure x = mkMonoidal [] [] x

  monoidalAp : ∀ {a b} → Monoidal (a → b) → Monoidal a → Monoidal b
  monoidalAp (mkMonoidal as xs f) (mkMonoidal bs ys g) = mkMonoidal (as ++ bs) (xs All++ ys) (compose as bs f g)

  instance
    FunctorMonoidal : Functor Monoidal
    FunctorMonoidal = record { fmap = monoidalMap }

    ApplicativeMonoidal : Applicative Monoidal
    ApplicativeMonoidal = record { pure = monoidalPure ; _<*>_ = monoidalAp }

  liftMonoidal : ∀ {a} → F a → Monoidal a
  liftMonoidal {a = a} x = mkMonoidal (a ∷ []) (x ∷ []) id

  applyFN : (as : List (Set ℓ₁)) {b : Set ℓ₁} → (map F as ⇉ F b) → All F as → F b
  applyFN [] f [] = f
  applyFN (a ∷ as) f (p ∷ ps) = applyFN as (f p) ps

  lowerMonoidal : ∀ {a} {{ApplicativeF : Applicative F}} → Monoidal a → F a
  lowerMonoidal (mkMonoidal as xs f) = applyFN as (liftAN as f) xs

  compose1-id-lemma : ∀ {ℓ} (as : List (Set ℓ)) {b : Set ℓ} (x : as ⇉ b) → compose1 as id x ≡ x
  compose1-id-lemma [] x = refl
  compose1-id-lemma {ℓ} (a ∷ as) x = extensionality ℓ ℓ (λ x₁ → compose1-id-lemma as (x x₁))

  identityLaw : ∀ {a} → (v : Monoidal a) → (pure id) <*> v ≡ v
  identityLaw (mkMonoidal bs xs x) = cong (mkMonoidal bs xs) (compose1-id-lemma bs x)

   -- Here one monoidalPure is needed to make clear which Applicative we want
  homomorphismLaw : ∀ {a b} → (f : a → b) → (x : a) → pure f <*> pure x ≡ monoidalPure (f x)
  homomorphismLaw f x = refl

  interchangeLaw : ∀ {a b} → (u : Monoidal (a → b)) → (y : a) → u <*> (pure y) ≡ (pure (λ f → f y)) <*> u
  interchangeLaw (mkMonoidal bs xs x) y = ≅-to-≡ (cong-dep₃ mkMonoidal (≡-to-≅ (l++[]≡l bs)) (lemma-All++[] xs) (lemma-compose-[] bs y x))

  -- Non-dependent composition
  comp : ∀ {a b c : Set ℓ₁} → (b → c) → (a → b) → a → c
  comp g f x = g (f x)

  postulate
    compositionLaw : ∀ {a b c} (u : Monoidal (b → c)) (v : Monoidal (a → b)) (w : Monoidal a) →
      monoidalPure comp <*> u <*> v <*> w ≡ u <*> (v <*> w)
  {-
  The first two holes are technical, but the last one is probably very tricky?
  compositionLaw (mkMonoidal [] [] x) (mkMonoidal [] [] x₁) (mkMonoidal [] [] x₂) = refl
  compositionLaw (mkMonoidal [] [] x) (mkMonoidal [] [] x₁) (mkMonoidal (x₂ ∷ bs₂) xs₂ x₃) = {!!}
  compositionLaw (mkMonoidal [] [] x) (mkMonoidal (x₁ ∷ bs₁) xs₁ x₂) (mkMonoidal bs₂ xs₂ x₃) = {!!}
  compositionLaw (mkMonoidal (x ∷ bs) xs x₁) (mkMonoidal bs₁ xs₁ x₂) (mkMonoidal bs₂ xs₂ x₃) = {!!}
  -}

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

  instance
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
