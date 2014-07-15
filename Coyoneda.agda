module Coyoneda where

-- https://hackage.haskell.org/package/kan-extensions-4.0.3/docs/Data-Functor-Coyoneda.html

open import Agda.Primitive
open import Prelude.Function
open import Prelude.Functor

data Coyoneda {ℓ₁ ℓ₂} (F : Set ℓ₁ → Set ℓ₂) (a : Set ℓ₁) : Set (lsuc ℓ₁ ⊔ ℓ₂) where
  mkCoyoneda : ∀ {b} → (b → a) → F b → Coyoneda F a

coyonedaMap : ∀ {ℓ₁ ℓ₂} {F : Set ℓ₁ → Set ℓ₂} {a b : Set ℓ₁} → (a → b) → Coyoneda F a → Coyoneda F b
coyonedaMap f₁ (mkCoyoneda f₂ x) = mkCoyoneda (f₁ ∘ f₂) x

FunctorCoyoneda : ∀ {ℓ₁ ℓ₂} {F : Set ℓ₁ → Set ℓ₂} → Functor (Coyoneda F)
FunctorCoyoneda = record { fmap = coyonedaMap }

liftCoyoneda : ∀ {ℓ₁ ℓ₂} {F : Set ℓ₁ → Set ℓ₂} {a : Set ℓ₁} → F a → Coyoneda F a
liftCoyoneda x = mkCoyoneda id x

lowerCoyoneda : ∀ {ℓ₁ ℓ₂} {F : Set ℓ₁ → Set ℓ₂} {{Functor : Functor F}} {a : Set ℓ₁} → Coyoneda F a → F a
lowerCoyoneda (mkCoyoneda f x) = fmap f x
