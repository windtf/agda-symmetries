module Cubical.Structures.Semilattices where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary
open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Functions.Logic hiding (¬_; inl; inr)
import Cubical.Functions.Logic as L
import Cubical.Data.Empty as ⊥
import Cubical.HITs.PropositionalTruncation as P
import Cubical.Data.Sum as ⊎ 


private
  variable
    ℓ ℓ' : Level
    A B : Type ℓ

⋀Totality : ∀ {A : Type ℓ} (_⋀_ : A -> A -> A) (a b : A) -> Type ℓ
⋀Totality _⋀_ a b = (a ⋀ b ≡ a) ⊎ (b ⋀ a ≡ b)

record IsTotalMeetSemiLatticeStr {A : Type ℓ} (_⋀_ : A -> A -> A) : Type ℓ where
  no-eta-equality
  constructor isTotalMeetSemiLatticeStr

  field
    ⋀isCarrierSet : isSet A
    ⋀isIdempotent : ∀ a -> a ⋀ a ≡ a
    ⋀isAssociative : ∀ a b c -> (a ⋀ b) ⋀ c ≡ a ⋀ (b ⋀ c)
    ⋀isCommutative : ∀ a b -> a ⋀ b ≡ b ⋀ a
    ⋀isTotal : ∀ a b -> ∥ ⋀Totality _⋀_ a b ∥₁

module _ (_⋀_ : A -> A -> A) where
  open IsTotalMeetSemiLatticeStr

  isPropIsTotalMeetSemiLatticeStr : isProp (IsTotalMeetSemiLatticeStr _⋀_)
  isPropIsTotalMeetSemiLatticeStr p q i .⋀isCarrierSet =
    isPropIsSet (⋀isCarrierSet p) (⋀isCarrierSet q) i
  isPropIsTotalMeetSemiLatticeStr p q i .⋀isIdempotent x =
    (isPropIsSet (⋀isCarrierSet p) (⋀isCarrierSet q) i (x ⋀ x) x)
      (⋀isIdempotent p x) (⋀isIdempotent q x) i
  isPropIsTotalMeetSemiLatticeStr p q i .IsTotalMeetSemiLatticeStr.⋀isAssociative a b c =
    (isPropIsSet (⋀isCarrierSet p) (⋀isCarrierSet q) i ((a ⋀ b) ⋀ c) (a ⋀ (b ⋀ c)))
      (⋀isAssociative p a b c) (⋀isAssociative q a b c) i
  isPropIsTotalMeetSemiLatticeStr p q i .IsTotalMeetSemiLatticeStr.⋀isCommutative a b =
    (isPropIsSet (⋀isCarrierSet p) (⋀isCarrierSet q) i (a ⋀ b) (b ⋀ a))
      (⋀isCommutative p a b) (⋀isCommutative q a b) i
  isPropIsTotalMeetSemiLatticeStr p q i .IsTotalMeetSemiLatticeStr.⋀isTotal a b =
    P.squash₁ (⋀isTotal p a b) (⋀isTotal q a b) i

record TotalMeetSemiLatticeStr (A : Type ℓ) : Type ℓ where
  constructor isTotalMeetSemiLattice

  field
    _⋀_ : A -> A -> A
    ⋀TotalMeetSemiLattice : IsTotalMeetSemiLatticeStr _⋀_

module Toset {ℓ : Level} {A : Type ℓ} where
  open import Cubical.Relation.Binary.Order
  open import Cubical.Data.Sigma as S
  open import Cubical.Data.Sum as ⊎
  open import Cubical.Functions.Logic using (_⊔′_)

  IsDecOrder : (A -> A -> Type ℓ) -> Type _
  IsDecOrder _≤_ = IsToset _≤_ × (∀ x y -> Dec (x ≤ y))

  isPropIsDecOrder : ∀ R -> isProp (IsDecOrder R)
  isPropIsDecOrder R =
    isOfHLevelΣ 1 (isPropIsToset R) λ isToset -> isPropΠ2 λ x y -> isPropDec (IsToset.is-prop-valued isToset x y)

  IsDecStrictTotalOrder : (A -> A -> Type ℓ) -> Type _
  IsDecStrictTotalOrder _>_ = IsLoset _>_ × (∀ x y -> Dec (x > y))

  isPropIsDecStrictTotalOrder : ∀ R -> isProp (IsDecStrictTotalOrder R)
  isPropIsDecStrictTotalOrder R =
    isOfHLevelΣ 1 (isPropIsLoset R) λ isLoset -> isPropΠ2 λ x y -> isPropDec (IsLoset.is-prop-valued isLoset x y)

  IsDecTotalMeetSemiLattice : (A -> A -> A) -> Type _
  IsDecTotalMeetSemiLattice _⋀_ = (IsTotalMeetSemiLatticeStr _⋀_) × (∀ a b -> ⋀Totality _⋀_ a b)

  HasDecOrder : Type _
  HasDecOrder = Σ _ IsDecOrder

  HasDecStrictOrder : Type _
  HasDecStrictOrder = Σ _ IsDecStrictTotalOrder

  HasDecTotalMeetSemiLattice : Type _
  HasDecTotalMeetSemiLattice = Σ _ IsDecTotalMeetSemiLattice

  HasDecOrder≃HasDecStrictOrder : HasDecOrder ≃ HasDecStrictOrder
  HasDecOrder≃HasDecStrictOrder = isoToEquiv (iso fwd inv sec ret)
    where
    fwd : _
    fwd (_ , isOrd , isDec) =
      _ , isToset→isLosetIrreflKernel isOrd isDec , isTosetDecidable→isLosetDecidable isOrd isDec
    inv : _
    inv (_ , isOrd , isDec) =
      _ , isLoset→isTosetReflClosure isOrd isDec , isLosetDecidable→isTosetDecidable isOrd isDec
    ireflRefl : ∀ {A B : Type ℓ} -> (A -> ¬ B) -> (A ⊎ B) × (¬ B) ≡ A
    ireflRefl {A = A} {B = B} a→¬b = ua (isoToEquiv (iso fwd' inv' (λ b -> refl) ret'))
      where
      fwd' : (A ⊎ B) × (¬ B) -> A
      fwd' (inl x , notB) = x
      fwd' (inr x , notB) = ⊥.rec (notB x)
      inv' : A → (A ⊎ B) × (¬ B)
      inv' x = inl x , a→¬b x
      ret' : retract fwd' inv'
      ret' (inl x , notB) = Σ≡Prop (λ _ -> isProp¬ _) refl
      ret' (inr x , notB) = ⊥.rec (notB x)
    sec : _
    sec (R , isOrd , isDec) = Σ≡Prop isPropIsDecStrictTotalOrder
      (funExt λ a -> funExt λ b -> ireflRefl λ rab a≡b →
        IsLoset.is-irrefl isOrd a (subst (R a) (sym a≡b) rab))
    ret : _
    ret (R , isOrd , isDec) = Σ≡Prop isPropIsDecOrder
      (funExt λ a -> funExt λ b -> ua (isoToEquiv
        (iso (fwd' a b) (inv' a b) (sec' a b) (rec' a b))))
      where
      fwd' : ∀ a b -> ((R a b) × (¬ a ≡ b)) ⊎ (a ≡ b) -> R a b
      fwd' a b = rec fst λ a≡b -> subst (R a) a≡b (IsToset.is-refl isOrd a)
      inv' : ∀ a b -> R a b -> ((R a b) × (¬ a ≡ b)) ⊎ (a ≡ b)
      inv' a b rab with isTosetDecidable→Discrete isOrd isDec a b
      ... | yes a≡b = inr a≡b
      ... | no ¬a≡b = inl (rab , ¬a≡b)
      sec' : ∀ a b -> section (fwd' a b) (inv' a b)
      sec' a b rab with isTosetDecidable→Discrete isOrd isDec a b
      ... | yes p = IsToset.is-prop-valued isOrd a b _ rab
      ... | no ¬p = refl
      rec' : ∀ a b -> retract (fwd' a b) (inv' a b)
      rec' a b (inl (rab , ¬a≡b)) with isTosetDecidable→Discrete isOrd isDec a b
      ... | yes p = ⊥.rec (¬a≡b p)
      ... | no ¬p = congS (λ x -> (inl (rab , x))) (isProp¬ _ _ _)
      rec' a b (inr a≡b) with isTosetDecidable→Discrete isOrd isDec a b
      ... | yes p = congS inr (IsToset.is-set isOrd a b p a≡b)
      ... | no ¬p = ⊥.rec (¬p a≡b)

  open IsToset
  decOrd→disc : (_≤_ : A -> A -> Type ℓ) -> IsDecOrder (_≤_) -> Discrete A
  decOrd→disc _≤_ (tosetA , _≤?_) x y with x ≤? y | y ≤? x
  ... | yes p | yes q = yes (tosetA .is-antisym x y p q)
  ... | yes p | no ¬q = no λ r -> ¬q (subst (_≤ x) r (tosetA .is-refl x))
  ... | no ¬p | yes q = no λ r -> ¬p (subst (x ≤_) r (tosetA .is-refl x))
  ... | no ¬p | no ¬q = ⊥.rec (P.rec ⊥.isProp⊥ (⊎.rec ¬p ¬q) (tosetA .is-total x y))

  module _ (isDisc : Discrete A) (_⋀_ : A -> A -> A) (lattice : IsTotalMeetSemiLatticeStr _⋀_) where
    open IsTotalMeetSemiLatticeStr lattice

    abstract
      ⋀TotalDec : ∀ a b -> ⋀Totality _⋀_ a b
      ⋀TotalDec a b with isDisc (a ⋀ b) a | isDisc (b ⋀ a) b
      ... | yes p | _ = inl p
      ... | no ¬p | yes q = inr q
      ... | no ¬p | no ¬q = ⊥.rec (P.rec ⊥.isProp⊥ (⊎.rec ¬p ¬q) (⋀isTotal a b))

    disc→decLattice : IsDecTotalMeetSemiLattice _⋀_
    disc→decLattice = lattice , ⋀TotalDec

  toset≰→≤ : (_≤_ : A -> A -> Type ℓ) -> IsToset (_≤_) -> ∀ x y -> ¬ (x ≤ y) -> (y ≤ x)
  toset≰→≤ _≤_ tosetA x y ¬p =
    P.rec (tosetA .is-prop-valued y x)
          (⊎.rec (λ x≤y -> ⊥.rec (¬p x≤y)) (λ y≤x -> y≤x))
          (tosetA .is-total x y)

  module Toset⋀ (isSetA : isSet A) (_≤_ : A -> A -> Type ℓ) (tosetA : IsToset _≤_) where

    ⋀F : (a b : A) -> (a ≤ b) ⊎ (b ≤ a) -> A
    ⋀F a b = ⊎.rec (λ a≤b -> a) (λ b≤a -> b)

    ⋀FConst : (a b : A) -> 2-Constant (⋀F a b)
    ⋀FConst a b =
      ⊎.elim (λ a≤b -> ⊎.elim (λ _ -> refl) (λ b≤a -> tosetA .is-antisym a b a≤b b≤a))
             (λ b≤a -> ⊎.elim (λ a≤b -> tosetA .is-antisym b a b≤a a≤b) (λ _ -> refl))

    _⋀_ : A -> A -> A
    a ⋀ b = P.rec→Set isSetA (⋀F a b) (⋀FConst a b) (tosetA .is-total a b)

    ⋀Β₁ : ∀ {a b} -> a ≤ b -> (a ⋀ b) ≡ a
    ⋀Β₁ {a = a} {b = b} a≤b =
      P.SetElim.helper isSetA (⋀F a b) (⋀FConst a b) (tosetA .is-total a b) P.∣ inl a≤b ∣₁

    ⋀Β₂ : ∀ {a b} -> b ≤ a -> (a ⋀ b) ≡ b
    ⋀Β₂ {a = a} {b = b} b≤a =
      P.SetElim.helper isSetA (⋀F a b) (⋀FConst a b) (tosetA .is-total a b) P.∣ inr b≤a ∣₁

    ⋀Π₁ : ∀ {a b} -> (a ⋀ b) ≤ a
    ⋀Π₁ {a = a} {b = b} =
      P.rec (tosetA .is-prop-valued (a ⋀ b) a) (⊎.rec (λ a≤b -> subst (_≤ a) (sym (⋀Β₁ a≤b)) (tosetA .is-refl a))
                                                      (λ b≤a -> subst (_≤ a) (sym (⋀Β₂ b≤a)) b≤a))
            (tosetA .is-total a b)

    ⋀Π₂ : ∀ {a b} -> (a ⋀ b) ≤ b
    ⋀Π₂ {a = a} {b = b} =
      P.rec (tosetA .is-prop-valued (a ⋀ b) b) (⊎.rec (λ a≤b -> subst (_≤ b) (sym (⋀Β₁ a≤b)) a≤b)
                                                      (λ b≤a -> subst (_≤ b) (sym (⋀Β₂ b≤a)) (tosetA .is-refl b)))
            (tosetA .is-total a b)

    ⋀Η₁ : ∀ {a b} -> (a ⋀ b) ≡ a -> a ≤ b
    ⋀Η₁ {a = a} {b = b} =
      P.rec (isProp→ (tosetA .is-prop-valued a b))
            (⊎.rec (λ a≤b _ -> a≤b) (λ b≤a ϕ -> subst (_≤ b) ϕ ⋀Π₂))
            (tosetA .is-total a b)

    ⋀UnivFwd : ∀ {x a b} -> x ≤ (a ⋀ b) -> (x ≤ a) × (x ≤ b)
    ⋀UnivFwd {x = x} {a = a} {b = b} ϕ =
      tosetA .is-trans x (a ⋀ b) a ϕ ⋀Π₁ , tosetA .is-trans x (a ⋀ b) b ϕ ⋀Π₂

    ⋀UnivBwd : ∀ {x a b} -> (x ≤ a) × (x ≤ b) -> x ≤ (a ⋀ b)
    ⋀UnivBwd {x = x} {a = a} {b = b} (ϕ , ψ) =
      P.rec (tosetA .is-prop-valued x (a ⋀ b))
            (⊎.rec (λ a≤b -> subst (x ≤_) (sym (⋀Β₁ a≤b)) ϕ)
                   (λ b≤a -> subst (x ≤_) (sym (⋀Β₂ b≤a)) ψ))
            (tosetA .is-total a b)

    ⋀Univ : ∀ {x a b} -> (x ≤ (a ⋀ b)) ≃ (x ≤ a) × (x ≤ b)
    ⋀Univ = propBiimpl→Equiv (tosetA .is-prop-valued _ _) (isProp× (tosetA .is-prop-valued _ _) (tosetA .is-prop-valued _ _)) ⋀UnivFwd ⋀UnivBwd

    ⋀Idem : ∀ a -> a ⋀ a ≡ a
    ⋀Idem a = ⋀Β₁ (tosetA .is-refl a)

    よ≡ : ∀ a b -> (∀ x -> x ≤ a ≃ x ≤ b) -> a ≡ b
    よ≡ a b f = tosetA .is-antisym a b (f a .fst (tosetA .is-refl a)) (invEq (f b) (tosetA .is-refl b))

    ⋀Comm : ∀ a b -> a ⋀ b ≡ b ⋀ a
    ⋀Comm a b = よ≡ (a ⋀ b) (b ⋀ a) λ x -> compEquiv ⋀Univ (compEquiv Σ-swap-≃ (invEquiv ⋀Univ))

    ⋀AssocR : ∀ a b c -> (a ⋀ b) ⋀ c ≡ a ⋀ (b ⋀ c)
    ⋀AssocR a b c =
      よ≡ ((a ⋀ b) ⋀ c) (a ⋀ (b ⋀ c))
        λ x -> compEquiv ⋀Univ
                         (compEquiv (Σ-cong-equiv ⋀Univ (λ _ -> idEquiv (x ≤ c)))
                                    (compEquiv Σ-assoc-≃ (compEquiv (Σ-cong-equiv (idEquiv (x ≤ a)) λ _ -> invEquiv ⋀Univ)
                                                                                  (invEquiv ⋀Univ))))

    ⋀Total : ∀ a b -> (a ⋀ b ≡ a) ⊔′ (b ⋀ a ≡ b)
    ⋀Total a b = P.map (⊎.map ⋀Β₁ ⋀Β₁) (tosetA .is-total a b)

    ⋀SemiLattice : TotalMeetSemiLatticeStr A
    ⋀SemiLattice .TotalMeetSemiLatticeStr._⋀_ = _⋀_
    ⋀SemiLattice .TotalMeetSemiLatticeStr.⋀TotalMeetSemiLattice .IsTotalMeetSemiLatticeStr.⋀isCarrierSet = isSetA  
    ⋀SemiLattice .TotalMeetSemiLatticeStr.⋀TotalMeetSemiLattice .IsTotalMeetSemiLatticeStr.⋀isIdempotent = ⋀Idem  
    ⋀SemiLattice .TotalMeetSemiLatticeStr.⋀TotalMeetSemiLattice .IsTotalMeetSemiLatticeStr.⋀isAssociative = ⋀AssocR
    ⋀SemiLattice .TotalMeetSemiLatticeStr.⋀TotalMeetSemiLattice .IsTotalMeetSemiLatticeStr.⋀isCommutative = ⋀Comm
    ⋀SemiLattice .TotalMeetSemiLatticeStr.⋀TotalMeetSemiLattice .IsTotalMeetSemiLatticeStr.⋀isTotal = ⋀Total

  module Toset⋁ (isSetA : isSet A) (_≤_ : A -> A -> Type ℓ) (tosetA : IsToset _≤_) where

    ⋁F : (a b : A) -> (a ≤ b) ⊎ (b ≤ a) -> A
    ⋁F a b = ⊎.rec (λ a≤b -> b) (λ b≤a -> a)

    ⋁FConst : (a b : A) -> 2-Constant (⋁F a b)
    ⋁FConst a b = ⊎.elim (λ a≤b -> ⊎.elim (λ _ -> refl) λ b≤a -> tosetA .is-antisym b a b≤a a≤b)
                            (λ b≤a -> ⊎.elim (λ a≤b -> tosetA .is-antisym a b a≤b b≤a) λ _ -> refl)

    _⋁_ : A -> A -> A
    a ⋁ b = P.rec→Set isSetA (⋁F a b) (⋁FConst a b) (tosetA .is-total a b)

    ⋁Β₁ : ∀ {a b} -> a ≤ b -> (a ⋁ b) ≡ b
    ⋁Β₁ {a = a} {b = b} a≤b = P.SetElim.helper isSetA (⋁F a b) (⋁FConst a b) (tosetA .is-total a b) P.∣ inl a≤b ∣₁

    ⋁Β₂ : ∀ {a b} -> b ≤ a -> (a ⋁ b) ≡ a
    ⋁Β₂ {a = a} {b = b} b≤a = P.SetElim.helper isSetA (⋁F a b) (⋁FConst a b) (tosetA .is-total a b) P.∣ inr b≤a ∣₁

    ⋁Π₁ : ∀ {a b} -> a ≤ (a ⋁ b)
    ⋁Π₁ {a = a} {b = b} = P.rec (tosetA .is-prop-valued a (a ⋁ b))
                                  (⊎.rec (λ a≤b -> subst (a ≤_) (sym (⋁Β₁ a≤b)) a≤b)
                                         (λ b≤a -> subst (a ≤_) (sym (⋁Β₂ b≤a)) (is-refl tosetA a)))
                                  (tosetA .is-total a b)

    ⋁Π₂ : ∀ {a b} -> b ≤ (a ⋁ b)
    ⋁Π₂ {a = a} {b = b} = P.rec (tosetA .is-prop-valued b (a ⋁ b))
                                  (⊎.rec (λ a≤b -> subst (b ≤_) (sym (⋁Β₁ a≤b)) (is-refl tosetA b))
                                         (λ b≤a -> subst (b ≤_) (sym (⋁Β₂ b≤a)) b≤a))
                                 (tosetA .is-total a b)

    ⋁Η₂ : ∀ {a b} -> (a ⋁ b) ≡ b -> a ≤ b
    ⋁Η₂ {a = a} {b = b} =
      P.rec (isProp→ (tosetA .is-prop-valued a b))
            (⊎.rec (λ a≤b _ -> a≤b)
                   (λ b≤a ϕ -> subst (a ≤_) ϕ ⋁Π₁))
            (tosetA .is-total a b)

    ⋁UnivFwd : ∀ {x a b} -> (a ⋁ b) ≤ x -> (a ≤ x) × (b ≤ x)
    ⋁UnivFwd {x = x} {a = a} {b = b} ϕ =
      tosetA .is-trans a (a ⋁ b) x ⋁Π₁ ϕ , tosetA .is-trans b (a ⋁ b) x ⋁Π₂ ϕ

    ⋁UnivBwd : ∀ {x a b} -> (a ≤ x) × (b ≤ x) -> (a ⋁ b) ≤ x
    ⋁UnivBwd {x = x} {a = a} {b = b} (ϕ , ψ) =
      P.rec (tosetA .is-prop-valued (a ⋁ b) x)
            (⊎.rec (λ a≤b -> subst (_≤ x) (sym (⋁Β₁ a≤b)) ψ)
                   (λ b≤a -> subst (_≤ x) (sym (⋁Β₂ b≤a)) ϕ))
            (tosetA .is-total a b)

    ⋁Univ : ∀ {x a b} -> ((a ⋁ b) ≤ x) ≃ (a ≤ x) × (b ≤ x)
    ⋁Univ = propBiimpl→Equiv (tosetA .is-prop-valued _ _) (isProp× (tosetA .is-prop-valued _ _) (tosetA .is-prop-valued _ _)) ⋁UnivFwd ⋁UnivBwd

    ⋁Idem : ∀ a -> a ⋁ a ≡ a
    ⋁Idem a = ⋁Β₁ (tosetA .is-refl a)

    よ≡ : ∀ a b -> (∀ x -> a ≤ x ≃ b ≤ x) -> a ≡ b
    よ≡ a b f = tosetA .is-antisym a b (invEq (f b) (tosetA .is-refl b)) (f a .fst (is-refl tosetA a))

    ⋁Comm : ∀ a b -> a ⋁ b ≡ b ⋁ a
    ⋁Comm a b = よ≡ (a ⋁ b) (b ⋁ a) λ x -> compEquiv ⋁Univ (compEquiv Σ-swap-≃ (invEquiv ⋁Univ))

    ⋁AssocR : ∀ a b c -> (a ⋁ b) ⋁ c ≡ a ⋁ (b ⋁ c)
    ⋁AssocR a b c =
      よ≡ ((a ⋁ b) ⋁ c) (a ⋁ (b ⋁ c))
        λ x -> compEquiv ⋁Univ
                         (compEquiv (Σ-cong-equiv ⋁Univ λ _ -> idEquiv (c ≤ x))
                                    (compEquiv Σ-assoc-≃ (compEquiv (Σ-cong-equiv (idEquiv (a ≤ x)) λ _ -> invEquiv ⋁Univ)
                                                                                  (invEquiv ⋁Univ))))

    ⋁Total : ∀ a b -> (a ⋁ b ≡ b) ⊔′ (b ⋁ a ≡ a)
    ⋁Total a b = P.map (⊎.map ⋁Β₁ ⋁Β₁) (tosetA .is-total a b)

    ⋁SemiLattice : TotalMeetSemiLatticeStr A
    ⋁SemiLattice .TotalMeetSemiLatticeStr._⋀_ = _⋁_
    ⋁SemiLattice .TotalMeetSemiLatticeStr.⋀TotalMeetSemiLattice .IsTotalMeetSemiLatticeStr.⋀isCarrierSet = isSetA
    ⋁SemiLattice .TotalMeetSemiLatticeStr.⋀TotalMeetSemiLattice .IsTotalMeetSemiLatticeStr.⋀isIdempotent = ⋁Idem
    ⋁SemiLattice .TotalMeetSemiLatticeStr.⋀TotalMeetSemiLattice .IsTotalMeetSemiLatticeStr.⋀isAssociative = ⋁AssocR
    ⋁SemiLattice .TotalMeetSemiLatticeStr.⋀TotalMeetSemiLattice .IsTotalMeetSemiLatticeStr.⋀isCommutative = ⋁Comm
    ⋁SemiLattice .TotalMeetSemiLatticeStr.⋀TotalMeetSemiLattice .IsTotalMeetSemiLatticeStr.⋀isTotal a b = P.map swap (⋁Total a b)
      where
      swap : ((a ⋁ b) ≡ b) ⊎ ((b ⋁ a) ≡ a) -> ((a ⋁ b) ≡ a) ⊎ ((b ⋁ a) ≡ b)
      swap (inl a⋁b≡b) = inr (⋁Comm b a ∙ a⋁b≡b)
      swap (inr b⋁a≡a) = inl (⋁Comm a b ∙ b⋁a≡a)
      
  module ⋀Toset (semiLattice : TotalMeetSemiLatticeStr A) where
    open TotalMeetSemiLatticeStr semiLattice public
    open IsTotalMeetSemiLatticeStr ⋀TotalMeetSemiLattice public
  
    _≤_ : A -> A -> Type ℓ
    a ≤ b = (a ⋀ b) ≡ a
  
    tosetA : IsToset _≤_
    tosetA .is-set = ⋀isCarrierSet
    tosetA .is-prop-valued a b = ⋀isCarrierSet (a ⋀ b) a
    tosetA .is-refl = ⋀isIdempotent
    tosetA .is-trans a b c a∧b≡a b∧c≡b =
      a ⋀ c ≡⟨ congS (_⋀ c) (sym a∧b≡a) ⟩
      ((a ⋀ b) ⋀ c) ≡⟨ ⋀isAssociative a b c ⟩
      (a ⋀ (b ⋀ c)) ≡⟨ congS (a ⋀_) b∧c≡b ⟩
      a ⋀ b ≡⟨ a∧b≡a ⟩
      a ∎
    tosetA .is-antisym a b a∧b≡a b∧a≡a =
      a ≡⟨ sym a∧b≡a ⟩
      a ⋀ b ≡⟨ ⋀isCommutative a b ⟩
      b ⋀ a ≡⟨ b∧a≡a ⟩
      b ∎
    tosetA .is-total = ⋀isTotal
  
  module _ where
    private
      fwd : TotalMeetSemiLatticeStr A -> TosetStr ℓ A
      fwd semiLattice .TosetStr._≤_ = ⋀Toset._≤_ semiLattice
      fwd semiLattice .TosetStr.isToset = ⋀Toset.tosetA semiLattice 

      inv : TosetStr ℓ A -> TotalMeetSemiLatticeStr A
      inv (tosetstr _≤_ isToset) =
        Toset⋀.⋀SemiLattice (is-set isToset) _≤_ isToset  

      sec' : section fwd inv
      sec' (tosetstr _≤_ tosetA) = cong₂ tosetstr
        (funExt λ a -> funExt λ b -> sym (ua (eq a b)))
        (toPathP (isPropIsToset _ _ _))
        where
        module Tos⋀ = Toset⋀ (is-set tosetA) _≤_ tosetA
        module ⋀Tos = ⋀Toset (inv (tosetstr _≤_ tosetA))
        eq : (a b : A) -> _ ≃ _
        eq a b = propBiimpl→Equiv (tosetA .is-prop-valued a b) (is-set tosetA _ _) Tos⋀.⋀Β₁ Tos⋀.⋀Η₁  

      ret' : retract fwd inv
      ret' (isTotalMeetSemiLattice _⋀_ ⋀TotalMeetSemiLattice) =
        cong₂ isTotalMeetSemiLattice (funExt (λ a -> funExt λ b -> eq a b))
          (toPathP (isPropIsTotalMeetSemiLatticeStr _ _ _))
        where
        module ⋀Tos = ⋀Toset (isTotalMeetSemiLattice _⋀_ ⋀TotalMeetSemiLattice)
        module Tos⋀ = Toset⋀ (⋀Tos.⋀isCarrierSet) (fwd (isTotalMeetSemiLattice _⋀_ ⋀TotalMeetSemiLattice) .TosetStr._≤_) (fwd (isTotalMeetSemiLattice _⋀_ ⋀TotalMeetSemiLattice) .TosetStr.isToset)
        _⋀'_ : _
        _⋀'_ = (⋀Tos.⋀isCarrierSet Toset⋀.⋀ ⋀Tos._≤_) ⋀Tos.tosetA
        prf : ∀ a b x -> Toset⋀.⋀F ⋀Tos.⋀isCarrierSet ⋀Tos._≤_ ⋀Tos.tosetA a b x ≡ (a ⋀ b)
        prf a b (inl a⋀b≡a) = sym a⋀b≡a
        prf a b (inr b⋀a≡b) =
          b ≡⟨ sym b⋀a≡b ⟩
          b ⋀ a ≡⟨ ⋀Tos.⋀isCommutative b a ⟩
          a ⋀ b ∎
        eq : (a b : A) -> a ⋀' b ≡ a ⋀ b
        eq a b =  P.elim {P = λ x -> P.rec→Set ⋀Tos.⋀isCarrierSet (Tos⋀.⋀F a b) (Tos⋀.⋀FConst a b) x ≡ (a ⋀ b)}
          (λ x -> ⋀Tos.⋀isCarrierSet _ (a ⋀ b))
          (λ x -> prf a b x)
          (⋀Tos.⋀isTotal a b)

    TotalMeetSemiLatticeStr≃TosetStr : TotalMeetSemiLatticeStr A ≃ TosetStr ℓ A
    TotalMeetSemiLatticeStr≃TosetStr = isoToEquiv (iso fwd inv sec' ret')

    HasDecOrder→HasDecTotalMeetSemiLattice : HasDecOrder -> HasDecTotalMeetSemiLattice
    HasDecOrder→HasDecTotalMeetSemiLattice (_≤_ , toset , decTotal) =
      _⋀_ , ⋀TotalMeetSemiLattice , ⋀DecTotal
      where
      _⋀_ : A -> A -> A
      _⋀_ = inv (tosetstr _≤_ toset) .TotalMeetSemiLatticeStr._⋀_
      ⋀TotalMeetSemiLattice : IsTotalMeetSemiLatticeStr _⋀_
      ⋀TotalMeetSemiLattice = inv (tosetstr _≤_ toset) .TotalMeetSemiLatticeStr.⋀TotalMeetSemiLattice
      ⋀DecTotal : ∀ a b -> ⋀Totality _⋀_ a b
      ⋀DecTotal = ⋀TotalDec (decOrd→disc _≤_ (toset , decTotal)) _⋀_ ⋀TotalMeetSemiLattice

    HasDecOrder≃DecTotalMeetSemiLattice : Discrete A -> TotalMeetSemiLatticeStr A ≃ HasDecOrder
    HasDecOrder≃DecTotalMeetSemiLattice discA = isoToEquiv (iso fwd' inv' sec'' ret'')
      where
      isSetA : isSet A
      isSetA = Discrete→isSet discA
      fwd' : TotalMeetSemiLatticeStr A -> HasDecOrder
      fwd' semiLattice =
        let tosetstr _≤_ isToset = fwd semiLattice
        in _≤_ , isToset , λ x y -> discA ((semiLattice ⋀Toset.⋀ x) y) x
      inv' : HasDecOrder -> TotalMeetSemiLatticeStr A
      inv' (_≤_ , toset , _) = inv (tosetstr _≤_ toset)
      sec'' : section fwd' inv'
      sec'' (_≤_ , toset , decOrd) =
        Σ≡Prop isPropIsDecOrder (congS TosetStr._≤_ (sec' (tosetstr _≤_ toset)))
      ret'' : retract fwd' inv'
      ret'' semiLattice =
        cong₂ isTotalMeetSemiLattice (cong TotalMeetSemiLatticeStr._⋀_ (ret' semiLattice)) (toPathP (isPropIsTotalMeetSemiLatticeStr _ _ _))