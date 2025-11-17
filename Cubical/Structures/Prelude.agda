module Cubical.Structures.Prelude where

import Cubical.Data.Empty as ⊥
import Cubical.HITs.PropositionalTruncation as P
open import Cubical.Foundations.Equiv public
open import Cubical.Foundations.Function public
open import Cubical.Foundations.HLevels public
open import Cubical.Foundations.Isomorphism public
open import Cubical.Foundations.Path public
open import Cubical.Foundations.Prelude public
open import Cubical.Foundations.Structure
open import Cubical.Relation.Nullary.Base
open import Cubical.Structures.Decidability public
open import Cubical.Structures.Semilattices public

private
  variable
    ℓ : Level
    A B C : Type ℓ
    x y z w : A

idp : (x : A) → x ≡ x
idp x = refl

ap : (f : A → B) → x ≡ y → f x ≡ f y
ap = congS

ap₂ : (f : A → B → C) → x ≡ y → z ≡ w → f x z ≡ f y w
ap₂ f p q i = f (p i) (q i)
