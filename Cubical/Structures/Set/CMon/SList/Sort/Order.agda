{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module Cubical.Structures.Set.CMon.SList.Sort.Order where

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

module Order→Sort {A : Type ℓ} (_≤_ : A -> A -> Type ℓ) (≤-isToset : IsToset _≤_) (_≤?_ : ∀ x y -> Dec (x ≤ y)) where
  open IsToset ≤-isToset
  open Membership is-set
  open Membership* is-set

  isDiscreteA : Discrete A
  isDiscreteA x y with x ≤? y | y ≤? x
  ... | yes p | yes q = yes (is-antisym x y p q)
  ... | yes p | no ¬q = no λ r -> ¬q (subst (_≤ x) r (is-refl x))
  ... | no ¬p | yes q = no λ r -> ¬p (subst (x ≤_) r (is-refl x))
  ... | no ¬p | no ¬q = ⊥.rec $ P.rec isProp⊥ (⊎.rec ¬p ¬q) (is-total x y)

  A-is-loset : Loset _ _
  A-is-loset = Toset→Loset (A , tosetstr _≤_ ≤-isToset) _≤?_

  _<_ : A -> A -> Type ℓ
  _<_ = LosetStr._<_ (A-is-loset .snd)

  <-isLoset : IsLoset _<_
  <-isLoset = LosetStr.isLoset (A-is-loset .snd)

  insert : A -> List A -> List A
  insert x [] = [ x ]
  insert x (y ∷ ys) with x ≤? y
  ... | yes p = x ∷ y ∷ ys
  ... | no ¬p = y ∷ insert x ys

  insertβ1 : ∀ x y ys -> x ≤ y -> insert x (y ∷ ys) ≡ x ∷ y ∷ ys
  insertβ1 x y ys p with x ≤? y
  ... | yes _ = refl
  ... | no ¬p = ⊥.rec (¬p p)

  insertβ2 : ∀ x y ys -> ¬ (x ≤ y) -> insert x (y ∷ ys) ≡ y ∷ insert x ys
  insertβ2 x y ys ¬p with x ≤? y
  ... | yes p = ⊥.rec (¬p p)
  ... | no ¬_ = refl

  insert≤ : ∀ x y xs ys -> insert x (insert y xs) ≡ x ∷ y ∷ ys -> x ≤ y
  insert≤ x y [] ys p with x ≤? y
  ... | yes x≤y = x≤y
  ... | no ¬x≤y = subst (_≤ y) (cons-inj₁ p) (is-refl y)
  insert≤ x y (z ∷ zs) ys p with y ≤? z
  ... | yes y≤z = lemma
    where
    lemma : x ≤ y
    lemma with x ≤? y
    ... | yes x≤y = x≤y
    ... | no ¬x≤y = subst (_≤ y) (cons-inj₁ p) (is-refl y)
  ... | no ¬y≤z = lemma
    where
    lemma : x ≤ y
    lemma with x ≤? z
    ... | yes x≤z = subst (x ≤_) (cons-inj₁ (cons-inj₂ p)) x≤z
    ... | no ¬x≤z = ⊥.rec (¬x≤z (subst (_≤ z) (cons-inj₁ p) (is-refl z)))

  insertCons : ∀ x xs ys -> x ∷ xs ≡ insert x ys -> xs ≡ ys
  insertCons x xs [] p = cons-inj₂ p
  insertCons x xs (y ∷ ys) p with x ≤? y
  ... | yes x≤y = cons-inj₂ p
  ... | no ¬x≤y = ⊥.rec (¬x≤y (subst (x ≤_) (cons-inj₁ p) (is-refl x)))

  private
    not-total-impossible : ∀ {x y} -> ¬(x ≤ y) -> ¬(y ≤ x) -> ⊥
    not-total-impossible {x} {y} p q =
      P.rec isProp⊥ (⊎.rec p q) (is-total x y)

  insertInsert : ∀ x y xs -> insert x (insert y xs) ≡ insert y (insert x xs)
  insertInsert x y [] with x ≤? y | y ≤? x
  ... | yes x≤y | no ¬y≤x = refl
  ... | no ¬x≤y | yes y≤x = refl
  ... | no ¬x≤y | no ¬y≤x = ⊥.rec (not-total-impossible ¬x≤y ¬y≤x)
  ... | yes x≤y | yes y≤x = let x≡y = is-antisym x y x≤y y≤x in cong₂ (λ u v -> u ∷ v ∷ []) x≡y (sym x≡y)
  insertInsert x y (z ∷ zs) with y ≤? z | x ≤? z
  ... | yes y≤z | yes x≤z = case1 y≤z x≤z
    where
    case1 : y ≤ z -> x ≤ z -> insert x (y ∷ z ∷ zs) ≡ insert y (x ∷ z ∷ zs)
    case1 y≤z x≤z with x ≤? y | y ≤? x
    ... | yes x≤y | yes y≤x = let x≡y = is-antisym x y x≤y y≤x in cong₂ (λ u v -> (u ∷ v ∷ z ∷ zs)) x≡y (sym x≡y)
    ... | yes x≤y | no ¬y≤x = sym (congS (x ∷_) (insertβ1 y z zs y≤z))
    ... | no ¬x≤y | yes y≤x = congS (y ∷_) (insertβ1 x z zs x≤z)
    ... | no ¬x≤y | no ¬y≤x = ⊥.rec (not-total-impossible ¬x≤y ¬y≤x)
  ... | yes y≤z | no ¬x≤z = case2 y≤z ¬x≤z
    where
    case2 : y ≤ z -> ¬(x ≤ z) -> insert x (y ∷ z ∷ zs) ≡ insert y (z ∷ insert x zs)
    case2 y≤z ¬x≤z with x ≤? y
    ... | yes x≤y = ⊥.rec (¬x≤z (is-trans x y z x≤y y≤z))
    ... | no ¬x≤y = congS (y ∷_) (insertβ2 x z zs ¬x≤z) ∙ sym (insertβ1 y z _ y≤z)
  ... | no ¬y≤z | yes x≤z = case3 ¬y≤z x≤z
    where
    case3 : ¬(y ≤ z) -> x ≤ z -> insert x (z ∷ insert y zs) ≡ insert y (x ∷ z ∷ zs)
    case3 ¬y≤z x≤z with y ≤? x
    ... | yes y≤x = ⊥.rec (¬y≤z (is-trans y x z y≤x x≤z))
    ... | no ¬y≤x = insertβ1 x z _ x≤z ∙ congS (x ∷_) (sym (insertβ2 y z zs ¬y≤z))
  ... | no ¬y≤z | no ¬x≤z =
    insert x (z ∷ insert y zs) ≡⟨ insertβ2 x z _ ¬x≤z ⟩
    z ∷ insert x (insert y zs) ≡⟨ congS (z ∷_) (insertInsert x y zs) ⟩
    z ∷ insert y (insert x zs) ≡⟨ sym (insertβ2 y z _ ¬y≤z) ⟩
    insert y (z ∷ insert x zs) ∎

  sort : SList A -> List A
  sort = Elim.f []
    (λ x xs -> insert x xs)
    (λ x y xs -> insertInsert x y xs)
    (λ _ -> isOfHLevelList 0 is-set)

  insertIsPermute : ∀ x xs -> list→slist (x ∷ xs) ≡ list→slist (insert x xs)
  insertIsPermute x [] = refl
  insertIsPermute x (y ∷ ys) with x ≤? y
  ... | yes p = refl
  ... | no ¬p =
    x ∷* y ∷* list→slist ys ≡⟨ swap x y _ ⟩
    y ∷* x ∷* list→slist ys ≡⟨ congS (y ∷*_) (insertIsPermute x ys) ⟩
    y ∷* list→slist (insert x ys) ∎

  open Sort is-set

  sortIsPermute : isSection sort
  sortIsPermute = ElimProp.f (trunc _ _) refl lemma
    where
    lemma : ∀ x {xs} p -> list→slist (sort (x ∷* xs)) ≡ x ∷* xs
    lemma x {xs} p = sym $
      x ∷* xs ≡⟨ congS (x ∷*_) (sym p) ⟩
      list→slist (x ∷ sort xs) ≡⟨ insertIsPermute x (sort xs) ⟩
      list→slist (insert x (sort xs)) ≡⟨⟩
      list→slist (sort (x ∷* xs)) ∎

  tailIsSorted : ∀ x xs -> isSorted sort (x ∷ xs) -> isSorted sort xs
  tailIsSorted x xs = P.rec squash₁ (uncurry lemma)
    where
    lemma : ∀ ys p -> isSorted sort xs
    lemma ys p = ∣ (list→slist xs) , sym (insertCons x _ _ sortProof) ∣₁
      where
      ysProof : ys ≡ x ∷* list→slist xs
      ysProof = sym (sortIsPermute ys) ∙ (congS list→slist p)
      sortProof : x ∷ xs ≡ insert x (sort (list→slist xs))
      sortProof = sym p ∙ congS sort ysProof

  -- Inductive definition of IsSorted
  data IsSorted : List A -> Type ℓ where
    sorted-nil : IsSorted []
    sorted-one : ∀ x -> IsSorted [ x ]
    sorted-cons : ∀ x y zs -> x ≤ y -> IsSorted (y ∷ zs) -> IsSorted (x ∷ y ∷ zs)

  isPropSorted : ∀ xs -> isProp (IsSorted xs)
  isPropSorted [] = isContr→isProp (sorted-nil , λ { sorted-nil → refl })
  isPropSorted (x ∷ []) = isContr→isProp (sorted-one x , λ { (sorted-one .x) → refl })
  isPropSorted (x ∷ y ∷ xs) (sorted-cons .x .y .xs ϕ p) (sorted-cons .x .y .xs ψ q) =
    cong₂ (sorted-cons x y xs) (is-prop-valued x y ϕ ψ) (isPropSorted (y ∷ xs) p q)

  open Sort.Section is-set

  isSort' : (SList A -> List A) -> Type _
  isSort' f = (∀ xs -> list→slist (f xs) ≡ xs) × (∀ xs -> ∥ IsSorted (f xs) ∥₁)

  tailSorted' : ∀ {x xs} -> IsSorted (x ∷ xs) -> IsSorted xs
  tailSorted' (sorted-one ._) = sorted-nil
  tailSorted' (sorted-cons ._ _ _ _ p) = p

  ≤tail : ∀ {x y ys} -> y ∈ (x ∷ ys) -> IsSorted (x ∷ ys) -> x ≤ y
  ≤tail {y = y} p (sorted-one x) = subst (_≤ y) (x∈[y]→x≡y y x p) (is-refl y)
  ≤tail {x} {y = z} p (sorted-cons x y zs q r) =
    P.rec (is-prop-valued x z)
      (⊎.rec
        (λ z≡x -> subst (x ≤_) (sym z≡x) (is-refl x))
        (λ z∈ys -> is-trans x y z q (≤tail z∈ys r))
      ) p

  smallestSorted : ∀ x xs -> (∀ y -> y ∈ xs -> x ≤ y) -> IsSorted xs -> IsSorted (x ∷ xs)
  smallestSorted x .[] p sorted-nil =
    sorted-one x
  smallestSorted x .([ y ]) p (sorted-one y) =
    sorted-cons x y [] (p y (x∈[x] y)) (sorted-one y)
  smallestSorted x .(_ ∷ _ ∷ _) p (sorted-cons y z zs y≤z r) =
    sorted-cons x y (z ∷ zs) (p y (x∈xs y (z ∷ zs))) (smallestSorted y (z ∷ zs) lemma r)
    where
    lemma : ∀ a -> a ∈ (z ∷ zs) -> y ≤ a
    lemma a = P.rec (is-prop-valued y a) $ ⊎.rec
      (λ a≡z -> subst (y ≤_) (sym a≡z) y≤z)
      (λ a∈zs -> is-trans y z a y≤z (≤tail (L.inr a∈zs) r))

  insert∈ : ∀ {x} {y} ys -> x ∈ insert y ys -> x ∈ (y ∷ ys)
  insert∈ {x} {y} ys p = ∈*→∈ x (y ∷ ys)
    (subst (x ∈*_) (sym (insertIsPermute y ys)) (∈→∈* x (insert y ys) p))

  insertIsSorted : ∀ x xs -> IsSorted xs -> IsSorted (insert x xs)
  insertIsSorted x [] p = sorted-one x
  insertIsSorted x (y ∷ ys) p with x ≤? y
  ... | yes q = sorted-cons x y ys q p
  ... | no ¬q = smallestSorted y (insert x ys) (lemma ys p) IH
    where
    IH : IsSorted (insert x ys)
    IH = insertIsSorted x ys (tailSorted' p)
    y≤x : y ≤ x
    y≤x = P.rec (is-prop-valued y x) (⊎.rec (idfun _) (⊥.rec ∘ ¬q)) (is-total y x)
    lemma : ∀ zs -> IsSorted (y ∷ zs) -> ∀ z -> z ∈ insert x zs → y ≤ z
    lemma zs p z r = P.rec (is-prop-valued y z)
      (⊎.rec (λ z≡x -> subst (y ≤_) (sym z≡x) y≤x) (λ z∈zs -> ≤tail (L.inr z∈zs) p)) (insert∈ zs r)

  -- TODO: refactor this since IsSorted is a prop
  sortIsSorted' : ∀ xs -> ∥ IsSorted (sort xs) ∥₁
  sortIsSorted' = ElimProp.f squash₁ ∣ sorted-nil ∣₁
    λ x -> P.rec squash₁ λ p -> ∣ (insertIsSorted x _ p) ∣₁

  sortIsSorted : ∀ xs -> IsSorted (sort xs)
  sortIsSorted xs = P.rec (isPropSorted (sort xs)) (idfun _) (sortIsSorted' xs)

  sortIsSorted'' : ∀ xs -> isSorted sort xs -> ∥ IsSorted xs ∥₁
  sortIsSorted'' xs = P.rec squash₁ λ (ys , p) ->
    P.map (subst IsSorted p) (sortIsSorted' ys)

  -- Step 1. show both sort xs and sort->order->sort xs give sorted list
  -- Step 2. apply this lemma
  -- Step 3. get sort->order->sort = sort
  uniqueSorted : ∀ xs ys -> list→slist xs ≡ list→slist ys -> IsSorted xs -> IsSorted ys -> xs ≡ ys
  uniqueSorted [] [] p xsSorted ysSorted = refl
  uniqueSorted [] (y ∷ ys) p xsSorted ysSorted = ⊥.rec (znots (congS S.length p))
  uniqueSorted (x ∷ xs) [] p xsSorted ysSorted = ⊥.rec (snotz (congS S.length p))
  uniqueSorted (x ∷ xs) (y ∷ ys) p xsSorted ysSorted =
    cong₂ _∷_ x≡y (uniqueSorted xs ys xs≡ys (tailSorted' xsSorted) (tailSorted' ysSorted))
    where
    x≤y : x ≤ y
    x≤y = ≤tail (∈*→∈ y (x ∷ xs) (subst (y ∈*_) (sym p) (L.inl refl))) xsSorted
    y≤x : y ≤ x
    y≤x = ≤tail (∈*→∈ x (y ∷ ys) (subst (x ∈*_) p (L.inl refl))) ysSorted
    x≡y : x ≡ y
    x≡y = is-antisym x y x≤y y≤x
    xs≡ys : list→slist xs ≡ list→slist ys
    xs≡ys =
      list→slist xs ≡⟨ remove1-≡-lemma isDiscreteA (list→slist xs) refl ⟩
      remove1 isDiscreteA x (list→slist (x ∷ xs)) ≡⟨ congS (remove1 isDiscreteA x) p ⟩
      remove1 isDiscreteA x (list→slist (y ∷ ys)) ≡⟨ sym (remove1-≡-lemma isDiscreteA (list→slist ys) x≡y) ⟩
      list→slist ys ∎

  uniqueSort : ∀ f -> isSort' f -> f ≡ sort
  uniqueSort f (fIsPermute , fIsSorted) = funExt λ xs ->
    P.rec2 (isOfHLevelList 0 is-set _ _)
      (uniqueSorted (f xs) (sort xs) (fIsPermute xs ∙ sym (sortIsPermute xs)))
      (fIsSorted xs)
      (sortIsSorted' xs)

  uniqueSort' : ∀ f xs -> isSort' f -> f xs ≡ sort xs
  uniqueSort' f xs p = congS (λ g -> g xs) (uniqueSort f p)

  private
    sort→orderLemma : ∀ x y xs -> isSorted sort (x ∷ y ∷ xs) -> x ≤ y
    sort→orderLemma x y xs = P.rec (is-prop-valued x y) (uncurry lemma)
      where
      lemma : ∀ ys p -> x ≤ y
      lemma ys p = insert≤ x y (sort tail) xs (congS sort tailProof ∙ p)
        where
        tail : SList A
        tail = list→slist xs
        tailProof : x ∷* y ∷* tail ≡ ys
        tailProof = sym (congS list→slist p) ∙ sortIsPermute ys

    sort→order : ∀ x y xs -> isSorted sort (x ∷ xs) -> y ∈ (x ∷ xs) -> x ≤ y
    sort→order x y [] p y∈xs = subst (_≤ y) (x∈[y]→x≡y y x y∈xs) (is-refl y)
    sort→order x y (z ∷ zs) p y∈x∷z∷zs with isDiscreteA x y
    ... | yes x≡y = subst (x ≤_) x≡y (is-refl x)
    ... | no ¬x≡y =
      P.rec (is-prop-valued x y) (⊎.rec (⊥.rec ∘ ¬x≡y ∘ sym) lemma) y∈x∷z∷zs
      where
      lemma : y ∈ (z ∷ zs) -> x ≤ y
      lemma y∈z∷zs = is-trans x z y
        (sort→orderLemma x z zs p)
        (sort→order z y zs (tailIsSorted x (z ∷ zs) p) y∈z∷zs)

  sortIsHeadLeast : isHeadLeast sort
  sortIsHeadLeast x y xs p y∈xs = ∣ (x ∷* y ∷* []* , insertβ1 x y [] (sort→order x y xs p y∈xs)) ∣₁

  sortIsSortSection : isSortSection sort
  sortIsSortSection = sortIsPermute , sortIsHeadLeast , tailIsSorted

  -- counter example that obeys isHeadLeast and not tail-sort

  swap12 : List A -> List A
  swap12 [] = []
  swap12 (x ∷ []) = x ∷ []
  swap12 (x ∷ y ∷ xs) = y ∷ x ∷ xs

  swap12Id : ∀ xs -> swap12 (swap12 xs) ≡ xs
  swap12Id [] = refl
  swap12Id (x ∷ []) = refl
  swap12Id (x ∷ y ∷ xs) = refl

  swap23 : List A -> List A
  swap23 [] = []
  swap23 (x ∷ xs) = x ∷ swap12 xs

  swap23Id : ∀ xs -> swap23 (swap23 xs) ≡ xs
  swap23Id [] = refl
  swap23Id (x ∷ xs) = congS (x ∷_) (swap12Id xs)

  swap23IsPermute : ∀ f -> isSection f -> isSection (swap23 ∘ f)
  swap23IsPermute f fIsPermute xs with f xs | inspect f xs
  ... | [] | [ p ]ᵢ = sym (congS list→slist p) ∙ fIsPermute xs
  ... | x ∷ [] | [ p ]ᵢ = sym (congS list→slist p) ∙ fIsPermute xs
  ... | x ∷ y ∷ [] | [ p ]ᵢ = sym (congS list→slist p) ∙ fIsPermute xs
  ... | x ∷ y ∷ z ∷ ys | [ p ]ᵢ =
    x ∷* z ∷* y ∷* list→slist ys ≡⟨ congS (x ∷*_) (swap z y (list→slist ys)) ⟩
    x ∷* y ∷* z ∷* list→slist ys ≡⟨ sym (congS list→slist p) ⟩
    list→slist (f xs) ≡⟨ fIsPermute xs ⟩
    xs ∎

  isHeadLeastOnly : SList A -> List A
  isHeadLeastOnly = swap23 ∘ sort

  isHeadLeastOnlyIsPermute : isSection isHeadLeastOnly
  isHeadLeastOnlyIsPermute = swap23IsPermute sort sortIsPermute

  private
    isHeadLeastIsSameFor2 : ∀ u v -> isSorted sort (u ∷ v ∷ []) -> isSorted isHeadLeastOnly (u ∷ v ∷ [])
    isHeadLeastIsSameFor2 u v = P.map λ (ys , q) -> ys , congS swap23 q

    isHeadLeast→sorted : ∀ x xs -> isSorted isHeadLeastOnly (x ∷ xs) -> isSorted sort (x ∷ swap12 xs)
    isHeadLeast→sorted x [] =
      P.map λ (ys , q) -> ys , sym (swap23Id (sort ys)) ∙ congS swap23 q
    isHeadLeast→sorted x (y ∷ []) =
      P.map λ (ys , q) -> ys , sym (swap23Id (sort ys)) ∙ congS swap23 q
    isHeadLeast→sorted x (y ∷ z ∷ xs) =
      P.map λ (ys , q) -> ys , sym (swap23Id (sort ys)) ∙ congS swap23 q

    swap12∈ : ∀ x xs -> x ∈ xs -> x ∈ swap12 xs
    swap12∈ x [] x∈ = x∈
    swap12∈ x (y ∷ []) x∈ = x∈
    swap12∈ x (y ∷ z ∷ xs) = P.rec squash₁
      (⊎.rec (L.inr ∘ L.inl) (P.rec squash₁ (⊎.rec L.inl (L.inr ∘ L.inr))))

    swap23∈ : ∀ x xs -> x ∈ xs -> x ∈ swap23 xs
    swap23∈ x (y ∷ xs) = P.rec squash₁ (⊎.rec L.inl (L.inr ∘ swap12∈ x xs))

    isSorted→≤ : ∀ {x y} -> isSorted sort (x ∷ y ∷ []) -> x ≤ y
    isSorted→≤ {x} {y} p = P.rec (is-prop-valued x y)
      (≤tail {ys = y ∷ []} (L.inr (L.inl refl)))
      (sortIsSorted'' (x ∷ y ∷ []) p)

    isHeadLeastTailSort→x≡y : ∀ x y -> isTailSorted isHeadLeastOnly -> x ≤ y -> x ≡ y
    isHeadLeastTailSort→x≡y x y hTailSort x≤y =
      is-antisym x y x≤y (isSorted→≤ (lemma1 ∣ x ∷* x ∷* y ∷* []* , lemma2 ∣₁))
      where
      -- [1, 2, 3] sorted by sort -> [1, 3, 2] sorted by isHeadLeast -> [3, 2] sorted by isHeadLeast -> [3, 2] sorted by sort
      lemma1 : isSorted sort (x ∷ x ∷ y ∷ []) -> isSorted sort (y ∷ x ∷ [])
      lemma1 = P.rec squash₁ λ (ys , q) -> isHeadLeast→sorted y [ x ] (hTailSort x _ ∣ ys , congS swap23 q ∣₁)
      lemma2 : sort (x ∷* x ∷* [ y ]*) ≡ x ∷ x ∷ y ∷ []
      lemma2 =
        insert x (insert x [ y ]) ≡⟨ congS (insert x) (insertβ1 x y [] x≤y) ⟩
        insert x (x ∷ y ∷ []) ≡⟨ insertβ1 x x [ y ] (is-refl x) ⟩
        x ∷ x ∷ [ y ] ∎

  isHeadLeastOnlyIsHeadLeast : isHeadLeast isHeadLeastOnly
  isHeadLeastOnlyIsHeadLeast x y xs p y∈xs = isHeadLeastIsSameFor2 x y
    (sortIsHeadLeast x y (swap12 xs) (isHeadLeast→sorted x xs p) (swap23∈ y (x ∷ xs) y∈xs))

  isHeadLeastTailSort→isPropA : isTailSorted isHeadLeastOnly -> isProp A
  isHeadLeastTailSort→isPropA hTailSort x y = P.rec (is-set _ _)
    (⊎.rec (isHeadLeastTailSort→x≡y x y hTailSort) (sym ∘ (isHeadLeastTailSort→x≡y y x hTailSort)))
    (is-total x y)

module Order→Sort-Example where

  ≤ℕ-isToset : IsToset _≤ℕ_
  ≤ℕ-isToset = istoset isSetℕ
    (λ _ _ -> isProp≤)
    (λ _ -> ≤-refl)
    (λ _ _ _ -> ≤-trans)
    (λ _ _ -> ≤-antisym)
    lemma
    where
    <→≤ : ∀ {n m} -> n <ℕ m -> n ≤ℕ m
    <→≤ (k , p) = suc k , sym (+-suc k _) ∙ p
    lemma : BinaryRelation.isTotal _≤ℕ_
    lemma x y = ∣ ⊎.rec ⊎.inl (_⊎_.inr ∘ <→≤) (splitℕ-≤ x y) ∣₁

  open Order→Sort _≤ℕ_ ≤ℕ-isToset ≤Dec public

  _ : sort (4 ∷* 6 ∷* 1 ∷* 2 ∷* []*) ≡ (1 ∷ 2 ∷ 4 ∷ 6 ∷ [])
  _ = refl
