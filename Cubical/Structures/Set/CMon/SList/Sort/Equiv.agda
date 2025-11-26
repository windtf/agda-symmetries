{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module Cubical.Structures.Set.CMon.SList.Sort.Equiv where

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
open import Cubical.Functions.Embedding
import Cubical.Data.List as L
open import Cubical.Functions.Logic as L hiding (¬_; ⊥)

open import Cubical.Structures.Prelude
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
open import Cubical.Structures.Set.CMon.SList.Sort.Sort
open import Cubical.Structures.Set.CMon.SList.Sort.Order

open Iso

private
  variable
    ℓ : Level
    A : Type ℓ

module MDef = F.Definition M.MonSig M.CMonEqSig M.CMonSEq
module LDef = F.Definition M.MonSig M.MonEqSig M.MonSEq

module Sort↔Order {ℓ : Level} {A : Type ℓ} (isSetA : isSet A) where
  open Sort isSetA
  open Sort.Section isSetA
  open Sort→Order isSetA
  open Order→Sort
  open IsToset
  open Toset

  IsHeadLeastSection : (SList A -> List A) -> Type _
  IsHeadLeastSection s = isSection s × imCut s

  IsSortSection : (SList A -> List A) -> Type _
  IsSortSection s = isSection s × imCut s × imCons s

  HasHeadLeastSectionAndIsDiscrete : Type _
  HasHeadLeastSectionAndIsDiscrete = (Σ _ IsHeadLeastSection) × (Discrete A)

  HasSortSectionAndIsDiscrete : Type _
  HasSortSectionAndIsDiscrete = (Σ (SList A -> List A) IsSortSection) × (Discrete A)

  IsSortSection→IsHeadLeastSection : ∀ s -> IsSortSection s -> IsHeadLeastSection s
  IsSortSection→IsHeadLeastSection s (section , imCut , _) = section , imCut

  order→sort : HasDecOrder -> HasSortSectionAndIsDiscrete
  order→sort (_≤_ , isToset , isDec) =
    (sort _≤_ isToset isDec , subst (λ isSetA' -> Sort.isSortSection isSetA' (sort _≤_ isToset isDec)) (isPropIsSet _ _) (Order→Sort.sortIsSortSection _≤_ isToset isDec)) , isDiscreteA _≤_ isToset isDec

  order→imCut : HasDecOrder -> HasHeadLeastSectionAndIsDiscrete
  order→imCut p = let ((s , sIsSort) , r) = order→sort p in (s , IsSortSection→IsHeadLeastSection s sIsSort) , r

  imCut→order : HasHeadLeastSectionAndIsDiscrete -> HasDecOrder
  imCut→order ((s , sIsSection , sIsSort) , discA) =
    _≤_ s sIsSection , ≤IsToset s sIsSection sIsSort , dec≤ s sIsSection discA

  sort→order : HasSortSectionAndIsDiscrete -> HasDecOrder
  sort→order ((s , sIsSort) , r) = imCut→order ((s , IsSortSection→IsHeadLeastSection s sIsSort) , r)

  order→imCut→order : ∀ x -> imCut→order (order→imCut x) ≡ x
  order→imCut→order (_≤_ , isToset , isDec) =
    Σ≡Prop (λ _≤'_ -> isOfHLevelΣ 1 (isPropIsToset _) (λ p -> isPropΠ2 λ x y -> isPropDec (is-prop-valued p x y))) (sym ≤≡)
    where
    _≤*_ : A -> A -> Type _
    _≤*_ = imCut→order (order→imCut (_≤_ , isToset , isDec)) .fst

    ≤*isToset : IsToset _≤*_
    ≤*isToset = imCut→order (order→imCut (_≤_ , isToset , isDec)) .snd .fst

    isoTo : ∀ x y -> x ≤ y -> x ≤* y
    isoTo x y x≤y with isDec x y
    ... | yes p = refl
    ... | no ¬p = ⊥.rec (¬p x≤y)

    isoFrom : ∀ x y -> x ≤* y -> x ≤ y
    isoFrom x y x≤y with isDec x y
    ... | yes p = p
    ... | no ¬p = ⊥.rec (¬p (subst (_≤ y) (just-inj y x x≤y) (is-refl isToset y)))

    iso≤ : ∀ x y -> Iso (x ≤ y) (x ≤* y)
    iso≤ x y = iso (isoTo x y) (isoFrom x y) (λ p -> is-prop-valued ≤*isToset x y _ p) (λ p -> is-prop-valued isToset x y _ p)
    ≤≡ : _≤_ ≡ _≤*_
    ≤≡ = funExt λ x -> funExt λ y -> isoToPath (iso≤ x y)

  sort→order→sort : ∀ x -> order→sort (sort→order x) ≡ x
  sort→order→sort ((s , sIsSection , sIsSort) , discA) =
    Σ≡Prop (λ _ -> isPropDiscrete)
    $ Σ≡Prop isPropIsSortSection
    $ sym
    $ funExt λ xs -> uniqueSort' _≤*_ ≤*isToset ≤*dec s xs (sIsSection , ∣_∣₁ ∘ sIsSort')
    where
    s' : SList A -> List A
    s' = order→sort (sort→order ((s , sIsSection , sIsSort) , discA)) .fst .fst

    s'IsSortSection : isSortSection s'
    s'IsSortSection = order→sort (sort→order ((s , sIsSection , sIsSort) , discA)) .fst .snd

    _≤*_ : A -> A -> Type _
    _≤*_ = _≤_ s sIsSection

    ≤*isToset : IsToset _≤*_
    ≤*isToset = ≤IsToset s sIsSection (sIsSort .fst)

    ≤*dec : ∀ x y -> Dec (x ≤* y)
    ≤*dec = dec≤ s sIsSection discA

    Sorted* : List A -> Type _
    Sorted* = Sorted _≤*_ ≤*isToset ≤*dec

    sIsSort'' : ∀ xs n -> n ≡ L.length (s xs) -> Sorted* (s xs)
    sIsSort'' xs n p with n | s xs | inspect s xs
    ... | zero  | []     | _ = sorted-nil
    ... | zero  | y ∷ ys | _ = ⊥.rec (znots p)
    ... | suc _ | []     | _ = ⊥.rec (snotz p)
    ... | suc _ | y ∷ [] | _ = sorted-one y
    ... | suc m | y ∷ z ∷ zs | [ q ]ᵢ = induction (sIsSort'' (list→slist (z ∷ zs)) m (injSuc p ∙ wit))
      where
      wit : suc (L.length zs) ≡ L.length (s (list→slist (z ∷ zs)))
      wit = sym $
        L.length (s (list→slist (z ∷ zs))) ≡⟨ sortLength≡ s sIsSection (list→slist (z ∷ zs)) ⟩
        S.length (list→slist (z ∷ zs)) ≡⟨ sym (sortLength≡α s sIsSection (z ∷ zs)) ⟩
        L.length (z ∷ zs) ∎

      z∷zsSorted : s (list→slist (z ∷ zs)) ≡ z ∷ zs
      z∷zsSorted = sortUnique s sIsSection (z ∷ zs) (sIsSort .snd y (z ∷ zs) ∣ _ , q ∣₁)

      induction : Sorted* (s (list→slist (z ∷ zs))) -> Sorted* (y ∷ z ∷ zs)
      induction IH =
        sorted-cons y z zs
          (isSorted→≤ s sIsSection y z (sIsSort .fst y z _ ∣ _ , q ∣₁ (L.inr (L.inl refl))))
          (subst Sorted* z∷zsSorted IH)

    sIsSort' : ∀ xs -> Sorted* (s xs)
    sIsSort' xs = sIsSort'' xs (L.length (s xs)) refl -- helps with termination checking

  -- without tail sort, we get an embedding
  order⊂imCut : isEmbedding order→imCut
  order⊂imCut = injEmbedding (isSet× (isSetΣ (isSetΠ (λ _ -> isOfHLevelList 0 isSetA)) λ q -> isProp→isSet (isProp× (isPropIsSection q) (isPropImCut q))) (isProp→isSet isPropDiscrete))
    (λ p -> sym (order→imCut→order _) ∙ congS imCut→order p ∙ order→imCut→order _)

  -- with tail sort, we can construct a full equivalence
  sort↔order : Iso HasDecOrder HasSortSectionAndIsDiscrete
  sort↔order = iso order→sort sort→order sort→order→sort order→imCut→order

  sort≃order : HasDecOrder ≃ HasSortSectionAndIsDiscrete
  sort≃order = isoToEquiv sort↔order

  -- module AnyFree (𝔐 : MDef.Free ℓ ℓ 2) (𝔏 : LDef.Free ℓ ℓ 2) where