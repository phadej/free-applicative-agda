module README where

-- Free applicatives and related

-- Defined as in Haskell's free package
--
-- Harder to define in Agda
-- Easier to reason about, if you want to prove some facts
import Free

-- More dynamic languages like definition
--
-- Applicative functor is functor from monoidal category to another together
-- with natural transformation η (pure) and morphism φ : F A × F B → F (A × B)
--
-- As product (×) is monoid operation, it is natural to "remember" φ using
-- free monoid structure, i.e. list.
--
-- Though in this case we need heterogenous list, it is easy with dependent types.
--
-- Not requiring F to be functor itself, is quite natural.  We use similar
-- construction as with Coyoneda.  We could use the fact F is a functor, but
-- using this fact will only make implementation more complex.
--
--
-- Definition is very natural after machinery is introduced
-- Yet proving anything (e.g. interchange or composition law) about this variant
-- is tedious
import Monoidal

-- Which is (kind of) extension of Coyoneda from kan-extensions package
import Coyoneda

-- And we are using own definition of well-founded recursion in Free module
-- More universe polymorphism, we can define recursive functions using measures
-- IMHO more flexible than sized-types.
import WellFounded
