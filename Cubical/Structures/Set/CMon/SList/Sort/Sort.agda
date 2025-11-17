module Cubical.Structures.Set.CMon.SList.Sort.Sort where

open import Cubical.Structures.Prelude

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Maybe as Maybe
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order renaming (_≤_ to _≤ℕ_; _<_ to _<ℕ_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎

open import Cubical.Induction.WellFounded

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.HLevels
open import Cubical.Data.List hiding (tail)
open import Cubical.Data.List.Properties hiding (tail)
open import Cubical.HITs.PropositionalTruncation as P
import Cubical.Data.List as L
open import Cubical.Functions.Logic as L hiding (¬_; ⊥)

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Set.CMon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity
open import Cubical.Structures.Set.Mon.List
open import Cubical.Structures.Set.CMon.SList.Base renaming (_∷_ to _∷*_; [] to []*; [_] to [_]*; _++_ to _++*_)
import Cubical.Structures.Set.CMon.SList.Base as S
open import Cubical.Structures.Set.CMon.SList.Length as S
open import Cubical.Structures.Set.CMon.SList.Membership as S
open import Cubical.Structures.Set.CMon.SList.Sort.Base

open Iso

private
  variable
    ℓ : Level
    A : Type ℓ

module Sort→Order (isSetA : isSet A) (sort : SList A -> List A) (sort≡ : ∀ xs -> list→slist (sort xs) ≡ xs) where

  isSetMaybeA : isSet (Maybe A)
  isSetMaybeA = isOfHLevelMaybe 0 isSetA

  isSetListA : isSet (List A)
  isSetListA = isOfHLevelList 0 isSetA

  private
    module 𝔖 = M.CMonSEq < SList A , slistAlpha > slistSat

  open Membership isSetA
  open Membership* isSetA
  open Sort isSetA sort
  open Sort.Section isSetA sort sort≡

  least : SList A -> Maybe A
  least xs = headMaybe (sort xs)

  leastNothing : ∀ xs -> least xs ≡ nothing -> xs ≡ []*
  leastNothing xs p with sort xs | inspect sort xs
  ... | []     | [ q ]ᵢ = sort[] xs q
  ... | y ∷ ys | [ q ]ᵢ = ⊥.rec (¬just≡nothing p)

  leastΣ : ∀ x xs -> least xs ≡ just x -> Σ[ ys ∈ List A ] (sort xs ≡ x ∷ ys)
  leastΣ x xs p with sort xs
  ... | []     = ⊥.rec (¬nothing≡just p)
  ... | y ∷ ys = ys , congS (_∷ ys) (just-inj y x p)

  leastIn : ∀ x xs -> least xs ≡ just x -> x ∈* xs
  leastIn x xs p =
    let (ys , q) = leastΣ x xs p
        x∷ys≡xs = congS list→slist (sym q) ∙ sort≡ xs
    in subst (x ∈*_) x∷ys≡xs (x∈*xs x (list→slist ys))

  leastChoice : ∀ x y -> (least (x ∷* [ y ]*) ≡ just x) ⊔′ (least (x ∷* [ y ]*) ≡ just y)
  leastChoice x y = P.rec squash₁
    (⊎.rec
      (L.inl ∘ congS headMaybe)
      (L.inr ∘ congS headMaybe))
    (sortChoice x y)

  _≤_ : A -> A -> Type _
  x ≤ y = least (x ∷* y ∷* []*) ≡ just x


  ≤Prop : ∀ x y -> hProp _
  ≤Prop x y = (x ≤ y) , isSetMaybeA _ _

  refl≤ : ∀ x -> x ≤ x
  refl≤ x = P.rec (isSetMaybeA _ _) (⊎.rec (idfun _) (idfun _)) (leastChoice x x)

  antisym≤ : ∀ x y -> x ≤ y -> y ≤ x -> x ≡ y
  antisym≤ x y p q = P.rec (isSetA x y)
    (⊎.rec
      (λ xy -> just-inj x y $
        just x ≡⟨ sym xy ⟩
        least (x ∷* y ∷* []*) ≡⟨ congS least (swap x y []*) ⟩
        least (y ∷* x ∷* []*) ≡⟨ q ⟩
        just y
      ∎)
      (λ yx -> just-inj x y $
        just x ≡⟨ sym p ⟩
        least (x ∷* [ y ]*) ≡⟨ yx ⟩
        just y
      ∎))
     (leastChoice x y)

  total≤ : ∀ x y -> (x ≤ y) ⊔′ (y ≤ x)
  total≤ x y = P.rec squash₁
    (⊎.rec
      L.inl
      (λ p -> L.inr $
        least (y ∷* [ x ]*) ≡⟨ congS least (swap y x []*) ⟩
        least (x ∷* [ y ]*) ≡⟨ p ⟩
        just y
      ∎))
    (leastChoice x y)

  dec≤ : (discA : Discrete A) -> ∀ x y -> Dec (x ≤ y)
  dec≤ discA x y = discreteMaybe discA _ _

  isSorted→≤ : ∀ x y -> isSorted (x ∷ y ∷ []) -> x ≤ y
  isSorted→≤ x y = P.rec (isSetMaybeA _ _) λ (xs , p) ->
    congS headMaybe (congS sort (sym (sym (sort≡ xs) ∙ congS list→slist p)) ∙ p)

  ≤→isSorted : ∀ x y -> x ≤ y -> isSorted (x ∷ y ∷ [])
  ≤→isSorted x y p = ∣ x ∷* y ∷* []* , proof ∣₁
    where
      proof : sort (x ∷* [ y ]*) ≡ x ∷ y ∷ []
      proof with leastΣ _ _ p
      ... | [] , r = ⊥.rec $ snotz $ injSuc $
        congS S.length (sym (sort≡ (x ∷* [ y ]*)) ∙  congS list→slist r)
      ... | a ∷ b ∷ c , r = ⊥.rec $ znots $ injSuc $ injSuc $
        congS S.length (sym (sort≡ (x ∷* [ y ]*)) ∙  congS list→slist r)
      ... | y' ∷ [] , q = P.rec isPropΑ
        (⊎.rec
          (λ r →
            sort (x ∷* [ y ]*) ≡⟨ congS (λ z → sort (x ∷* [ z ]*)) r ⟩
            sort (x ∷* [ x ]*) ≡⟨ lemmaΑ ⟩
            x ∷ x ∷ [] ≡⟨ congS (λ z → x ∷ [ z ]) (sym r) ⟩
            x ∷ y ∷ [] ∎)
        (P.rec isPropΑ
          (⊎.rec
            (λ r →
              sort (x ∷* [ y ]*) ≡⟨ q ⟩
              x ∷ y' ∷ [] ≡⟨ congS (λ z → x ∷ [ z ]) (sym r) ⟩
              x ∷ y ∷ [] ∎)
          ⊥.rec*)))
        y∈
        where
          isPropΑ : isProp (sort (x ∷* [ y ]*) ≡ x ∷ y ∷ [])
          isPropΑ = isOfHLevelList 0 isSetA _ _
          y∈* : y ∈* (x ∷* [ y ]*)
          y∈* = L.inr (L.inl refl)
          y∈sort : y ∈ sort (x ∷* [ y ]*)
          y∈sort = ∈*→∈ y (sort (x ∷* [ y ]*)) (subst (y ∈*_) (sym (sort≡ (x ∷* [ y ]*))) y∈*)
          y∈ : y ∈ (x ∷ y' ∷ [])
          y∈ = subst (y ∈_) q y∈sort
          lemmaΑ : sort (x ∷* [ x ]*) ≡ x ∷ x ∷ []
          lemmaΑ with sort (x ∷* [ x ]*) | inspect sort (x ∷* [ x ]*)
          ... | [] | [ r ]ᵢ = ⊥.rec $ snotz $
            congS S.length (sym (sort≡ (x ∷* [ x ]*)) ∙ congS list→slist r)
          ... | a ∷ [] | [ r ]ᵢ = ⊥.rec $ snotz $ injSuc $
            congS S.length (sym (sort≡ (x ∷* [ x ]*)) ∙ congS list→slist r)
          ... | a ∷ b ∷ c ∷ as | [ r ]ᵢ = ⊥.rec $ znots $ injSuc $ injSuc $
            congS S.length (sym (sort≡ (x ∷* [ x ]*)) ∙ congS list→slist r)
          ... | a ∷ b ∷ [] | [ r ]ᵢ = cong₂ (λ m n → m ∷ [ n ]) (x∈*[yy]→x≡y a x a∈*) (x∈*[yy]→x≡y b x b∈*)
            where
              xx≡ab : x ∷* [ x ]* ≡ a ∷* [ b ]*
              xx≡ab = sym (sort≡ (x ∷* [ x ]*)) ∙ congS list→slist r
              a∈* : a ∈* (x ∷* [ x ]*)
              a∈* = subst (a ∈*_) (sym xx≡ab) (L.inl refl)
              b∈* : b ∈* (x ∷* [ x ]*)
              b∈* = subst (b ∈*_) (sym xx≡ab) (L.inr (L.inl refl))

  isSorted↔≤ : ∀ x y -> isSorted (x ∷ y ∷ []) ≃ (x ≤ y)
  isSorted↔≤ x y = isoToEquiv (iso (isSorted→≤ x y) (≤→isSorted x y)
    (λ p → isSetMaybeA _ _ _ p)
    (λ p → squash₁ _ p))

  module _ (sortIsSort : imCut) where
    trans≤ : ∀ x y z -> x ≤ y -> y ≤ z -> x ≤ z
    trans≤ x y z x≤y y≤z with least (x ∷* y ∷* z ∷* []*) | inspect least (x ∷* y ∷* z ∷* []*)
    ... | nothing | [ p ]ᵢ = ⊥.rec (snotz (congS S.length (leastNothing _ p)))
    ... | just u | [ p ]ᵢ =
      P.rec (isSetMaybeA _ _)
        (⊎.rec case1
          (P.rec (isSetMaybeA _ _)
            (⊎.rec case2 (case3 ∘ x∈[y]→x≡y _ _))
          )
        )
        (leastIn u (x ∷* y ∷* z ∷* []*) p)
      where
      tail' : Σ[ xs ∈ List A ] u ∷ xs ≡ sort (x ∷* y ∷* z ∷* []*)
      tail' with sort (x ∷* y ∷* z ∷* []*)
      ... | [] = ⊥.rec (¬nothing≡just p)
      ... | v ∷ xs = xs , congS (_∷ xs) (just-inj _ _ (sym p))
      tail : List A
      tail = tail' .fst
      tailProof : u ∷ tail ≡ sort (x ∷* y ∷* z ∷* []*)
      tailProof = tail' .snd
      u∷tailIsSorted : isSorted (u ∷ tail)
      u∷tailIsSorted = ∣ ((x ∷* y ∷* z ∷* []*) , sym tailProof) ∣₁
      uIsSmallest : ∀ v -> v ∈* (x ∷* y ∷* z ∷* []*) -> u ≤ v
      uIsSmallest v q =
        isSorted→≤ u v (sortIsSort u v tail u∷tailIsSorted (subst (v ∈_) (sym tailProof) (sort∈ v _ q)))
      case1 : u ≡ x -> x ≤ z
      case1 u≡x = subst (_≤ z) u≡x (uIsSmallest z (L.inr (L.inr (L.inl refl))))
      case2 : u ≡ y -> x ≤ z
      case2 u≡y = subst (_≤ z) (antisym≤ y x y≤x x≤y) y≤z
        where
        y≤x : y ≤ x
        y≤x = subst (_≤ x) u≡y (uIsSmallest x (L.inl refl))
      case3 : u ≡ z -> x ≤ z
      case3 u≡z = subst (x ≤_) (antisym≤ y z y≤z z≤y) x≤y
        where
        z≤y : z ≤ y
        z≤y = subst (_≤ y) u≡z (uIsSmallest y (L.inr (L.inl refl)))

    ≤IsToset : IsToset _≤_
    IsToset.is-set ≤IsToset = isSetA
    IsToset.is-prop-valued ≤IsToset x y = isOfHLevelMaybe 0 isSetA _ _
    IsToset.is-refl ≤IsToset = refl≤
    IsToset.is-trans ≤IsToset = trans≤
    IsToset.is-antisym ≤IsToset = antisym≤
    IsToset.is-total ≤IsToset = total≤
