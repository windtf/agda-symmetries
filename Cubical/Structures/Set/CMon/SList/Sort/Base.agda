{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module Cubical.Structures.Set.CMon.SList.Sort.Base where

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
open import Cubical.Data.List
open import Cubical.Data.List.Properties
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

open Iso

private
  variable
    ℓ : Level
    A : Type ℓ

headMaybe : List A -> Maybe A
headMaybe [] = nothing
headMaybe (x ∷ xs) = just x

module Sort {A : Type ℓ} (isSetA : isSet A) (sort : SList A -> List A) where
  open Membership isSetA

  isSorted : List A -> Type _
  isSorted list = ∥ fiber sort list ∥₁

  isSection : Type _
  isSection = ∀ xs -> list→slist (sort xs) ≡ xs

  isPropIsSection : isProp isSection
  isPropIsSection = isPropΠ (λ _ -> trunc _ _)

  imCut : Type _
  imCut = ∀ x y xs -> isSorted (x ∷ xs) -> y ∈ (x ∷ xs) -> isSorted (x ∷ y ∷ [])

  imCons : Type _
  imCons = ∀ x xs -> isSorted (x ∷ xs) -> isSorted xs

  isSort : Type _
  isSort = imCut × imCons

  isPropImCut : isProp imCut
  isPropImCut = isPropΠ5 λ _ _ _ _ _ -> squash₁

  isPropImCons : isProp imCons
  isPropImCons = isPropΠ3 (λ _ _ _ -> squash₁)

  isPropIsSort : isProp isSort
  isPropIsSort = isProp× isPropImCut isPropImCons

  isSortSection : Type _
  isSortSection = isSection × isSort

  isPropIsSortSection : isProp isSortSection
  isPropIsSortSection = isOfHLevelΣ 1 isPropIsSection (λ _ -> isPropIsSort)

  module Section (sort≡ : isSection) where
    open Membership* isSetA

    list→slistΗ : ∀ xs -> (x : A) -> list→slist xs ≡ [ x ]* -> xs ≡ [ x ]
    list→slistΗ [] x p = ⊥.rec (znots (congS S.length p))
    list→slistΗ (x ∷ []) y p = congS [_] ([-]-inj {ϕ = isSetA} p)
    list→slistΗ (x ∷ y ∷ xs) z p = ⊥.rec (snotz (injSuc (congS S.length p)))

    sortLength≡Α : ∀ (xs : List A) -> L.length xs ≡ S.length (list→slist xs)
    sortLength≡Α [] = refl
    sortLength≡Α (x ∷ xs) = congS suc (sortLength≡Α xs)

    sortLength≡ : ∀ xs -> L.length (sort xs) ≡ S.length xs
    sortLength≡ xs = sortLength≡Α (sort xs) ∙ congS S.length (sort≡ xs)

    length0 : ∀ (xs : List A) -> L.length xs ≡ 0 -> xs ≡ []
    length0 [] p = refl
    length0 (x ∷ xs) p = ⊥.rec (snotz p)

    sort[] : ∀ xs -> sort xs ≡ [] -> xs ≡ []*
    sort[] xs p = sym (sort≡ xs) ∙ congS list→slist p

    sort[]' : sort []* ≡ []
    sort[]' = length0 (sort []*) (sortLength≡ []*)

    sort[-] : ∀ x -> sort [ x ]* ≡ [ x ]
    sort[-] x = list→slistΗ (sort [ x ]*) x (sort≡ [ x ]*)

    sort∈ : ∀ x xs -> x ∈* xs -> x ∈ sort xs
    sort∈ x xs p = ∈*→∈ x (sort xs) (subst (x ∈*_) (sym (sort≡ xs)) p)

    sort∈* : ∀ x xs -> x ∈ sort xs -> x ∈* xs
    sort∈* x xs p = subst (x ∈*_) (sort≡ xs) (∈→∈* x (sort xs) p)

    sortUnique : ∀ xs -> isSorted xs -> sort (list→slist xs) ≡ xs
    sortUnique xs = P.rec (isOfHLevelList 0 isSetA _ xs) λ (ys , p) ->
      sym (congS sort (sym (sort≡ ys) ∙ congS list→slist p)) ∙ p

    sortChoiceLemma : ∀ x -> sort (x ∷* x ∷* []*) ≡ x ∷ x ∷ []
    sortChoiceLemma x with sort (x ∷* x ∷* []*) | inspect sort (x ∷* x ∷* []*)
    ... | []                | [ p ]ᵢ = ⊥.rec (snotz (sym (sortLength≡ (x ∷* x ∷* []*)) ∙ congS L.length p))
    ... | x₁ ∷ []           | [ p ]ᵢ = ⊥.rec (snotz (injSuc (sym (sortLength≡ (x ∷* x ∷* []*)) ∙ congS L.length p)))
    ... | x₁ ∷ x₂ ∷ x₃ ∷ xs | [ p ]ᵢ = ⊥.rec (znots (injSuc (injSuc (sym (sortLength≡ (x ∷* x ∷* []*)) ∙ congS L.length p))))
    ... | a ∷ b ∷ [] | [ p ]ᵢ =
      P.rec (isOfHLevelList 0 isSetA _ _)
        (⊎.rec lemma1 (lemma1 ∘ x∈[y]→x≡y a x))
        (sort∈* a (x ∷* x ∷* []*) (subst (a ∈_) (sym p) (x∈xs a [ b ])))
      where
      lemma2 : a ≡ x -> b ≡ x -> a ∷ b ∷ [] ≡ x ∷ x ∷ []
      lemma2 q r = cong₂ (λ u v -> u ∷ v ∷ []) q r
      lemma1 : a ≡ x -> a ∷ b ∷ [] ≡ x ∷ x ∷ []
      lemma1 q =
          P.rec (isOfHLevelList 0 isSetA _ _)
            (⊎.rec (lemma2 q) (lemma2 q ∘ x∈[y]→x≡y b x))
            (sort∈* b (x ∷* x ∷* []*) (subst (b ∈_) (sym p) (L.inr (L.inl refl))))

    sortChoice : ∀ x y -> (sort (x ∷* y ∷* []*) ≡ x ∷ y ∷ []) ⊔′ (sort (x ∷* y ∷* []*) ≡ y ∷ x ∷ [])
    sortChoice x y with sort (x ∷* y ∷* []*) | inspect sort (x ∷* y ∷* []*)
    ... | []                | [ p ]ᵢ = ⊥.rec (snotz (sym (sortLength≡ (x ∷* y ∷* []*)) ∙ congS L.length p))
    ... | x₁ ∷ []           | [ p ]ᵢ = ⊥.rec (snotz (injSuc (sym (sortLength≡ (x ∷* y ∷* []*)) ∙ congS L.length p)))
    ... | x₁ ∷ x₂ ∷ x₃ ∷ xs | [ p ]ᵢ = ⊥.rec (znots (injSuc (injSuc (sym (sortLength≡ (x ∷* y ∷* []*)) ∙ congS L.length p))))
    ... | a ∷ b ∷ [] | [ p ]ᵢ =
      P.rec squash₁
        (⊎.rec
          (λ x≡a -> P.rec squash₁
            (⊎.rec
              (λ y≡a -> L.inl (sym p ∙ subst (λ u -> sort (x ∷* [ u ]*) ≡ x ∷ u ∷ []) (x≡a ∙ sym y≡a) (sortChoiceLemma x)))
              (λ y∈[b] -> L.inl (cong₂ (λ u v → u ∷ v ∷ []) (sym x≡a) (sym (x∈[y]→x≡y y b y∈[b]))))
            )
            (subst (y ∈_) p (sort∈ y (x ∷* y ∷* []*) (L.inr (L.inl refl))))
          )
          (λ x∈[b] -> P.rec squash₁
            (⊎.rec
              (λ y≡a -> L.inr (cong₂ (λ u v → u ∷ v ∷ []) (sym y≡a) (sym (x∈[y]→x≡y x b x∈[b]))))
              (λ y∈[b] ->
                let x≡y = (x∈[y]→x≡y x b x∈[b]) ∙ sym (x∈[y]→x≡y y b y∈[b])
                in L.inl (sym p ∙ subst (λ u -> sort (x ∷* [ u ]*) ≡ x ∷ u ∷ []) x≡y (sortChoiceLemma x))
              )
            )
            (subst (y ∈_) p (sort∈ y (x ∷* y ∷* []*) (L.inr (L.inl refl))))
          )
        )
        (subst (x ∈_) p (sort∈ x (x ∷* y ∷* []*) (L.inl refl)))
