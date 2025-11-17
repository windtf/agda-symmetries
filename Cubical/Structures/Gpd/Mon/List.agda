module Cubical.Structures.Gpd.Mon.List where

open import Cubical.Structures.Prelude
open import Cubical.Structures.Prelude.TODO

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma

open import Cubical.Foundations.GroupoidLaws

open import Cubical.Functions.Logic as L

open import Cubical.HITs.PropositionalTruncation as P

import Cubical.Structures.Free as F
import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Set.Mon.List as L

open import Cubical.Structures.Arity
open import Cubical.Structures.Eq
open import Cubical.Structures.Gpd.Mon.Desc as L
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public hiding (struct ; car)
open import Cubical.Structures.Tree

private
  variable
    ℓ : Level
    A : Type ℓ

list-α : sig M.MonSig (List A) -> List A
list-α = L.list-α

private
  list-▿ : (xs ys : List A)
         → ++-assoc xs [] ys ∙ ap (xs ++_) (idp ys)
          ≡ ap (_++ ys) (++-unit-r xs)
  list-▿ [] ys =
      ++-assoc [] [] ys ∙ ap ([] ++_) (idp ys)
    ≡⟨⟩
      refl ∙ refl
    ≡⟨ sym (lUnit refl) ⟩
      refl
    ≡⟨⟩
      ap (_++ ys) (++-unit-r [])
    ∎
  list-▿ (x ∷ xs) ys =
      ++-assoc (x ∷ xs) [] ys ∙ ap ((x ∷ xs) ++_) (idp ys)
    ≡⟨⟩
      ap (x ∷_) (++-assoc xs [] ys) ∙ idp (x ∷ xs ++ ys)
    ≡⟨ sym (rUnit (ap (x ∷_) (++-assoc xs [] ys))) ⟩
      ap (x ∷_) (++-assoc xs [] ys)
    ≡⟨ ap (ap (x ∷_)) (rUnit (++-assoc xs [] ys)) ⟩
      ap (x ∷_) (++-assoc xs [] ys ∙ ap (xs ++_) (idp ys))
    ≡⟨ ap (ap (x ∷_)) (list-▿ xs ys) ⟩
      ap (x ∷_) (ap (_++ ys) (++-unit-r xs))
    ≡⟨⟩
      ap (_++ ys) (ap (x ∷_) (++-unit-r xs))
    ≡⟨⟩
      ap (_++ ys) (++-unit-r (x ∷ xs))
    ∎

listStr : MonStr (List A)
𝟙 listStr = []
_⊗_ listStr = _++_
Λ listStr = idp
ρ listStr = ++-unit-r
α listStr = ++-assoc
▿ listStr = list-▿
⬠ listStr = TODO -- pentagon coherence for lists

module Free {x y : Level} {A : Type x} (𝔜 : MonGpd y) where

  module _ (f : A -> 𝔜 .car) where
    _♯ : List A -> 𝔜 .car
    [] ♯ = 𝔜 .str .𝟙
    (x ∷ xs) ♯ = 𝔜 .str ._⊗_ (f x) (xs ♯)
