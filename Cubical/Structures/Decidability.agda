module Cubical.Structures.Decidability where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Nullary.Base
import Cubical.Data.Empty as ⊥

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    P : Type ℓ

module _ {ℓ ℓ'} {P : Type ℓ} {A : Dec P → Type ℓ'} where

  decElim : ((p : P) → A (yes p)) → ((¬p : ¬ P) → A (no ¬p))
          → (p : Dec P) → A p
  decElim y n (yes p) = y p
  decElim y n (no ¬p) = n ¬p

module _ {ℓ} {P : Type ℓ} (isPropP : isProp P) where

  private
    isPropDec : isProp (Dec P)
    isPropDec (yes p) (yes q) = congS yes (isPropP p q)
    isPropDec (yes p) (no ¬q) = ⊥.rec (¬q p)
    isPropDec (no ¬p) (yes q) = ⊥.rec (¬p q)
    isPropDec (no ¬p) (no ¬q) = congS no (isProp→ ⊥.isProp⊥ ¬p ¬q)

  decRec-yes : {A : Type ℓ} {y : P -> A} {n : ¬ P -> A} (p : P) (d : Dec P) -> decRec y n d ≡ y p
  decRec-yes {A = A} {y = y} {n = n} p = decElim (λ q -> congS y (isPropP q p)) λ ¬p -> ⊥.rec (¬p p)

  decRec-no : {A : Type ℓ} {y : P -> A} {n : ¬ P -> A} (¬p : ¬ P) (d : Dec P) -> decRec y n d ≡ n ¬p
  decRec-no {A = A} {y = y} {n = n} ¬p = decElim (λ p -> ⊥.rec (¬p p)) (λ ¬q -> congS n (isProp→ ⊥.isProp⊥ ¬q ¬p))