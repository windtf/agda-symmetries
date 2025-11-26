module Cubical.Structures.Semilattices where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Relation.Nullary.Base
import Cubical.Data.Empty as ⊥
import Cubical.HITs.PropositionalTruncation as P

private
  variable
    ℓ : Level
    A : Type ℓ

module Toset {ℓ : Level} {A : Type ℓ} where
  open import Cubical.Relation.Binary.Order
  open import Cubical.Data.Sigma as S
  open import Cubical.Data.Sum as ⊎
  open import Cubical.Functions.Logic using (_⊔′_)

  IsDecOrder : (A -> A -> Type ℓ) -> Type _
  IsDecOrder _≤_ = IsToset _≤_ × (∀ x y -> Dec (x ≤ y))

  IsDecStrictOrder : (A -> A -> Type ℓ) -> Type _
  IsDecStrictOrder _>_ = IsLoset _>_ × (∀ x y -> Dec (x > y))

  HasDecOrder : Type _
  HasDecOrder = Σ _ IsDecOrder

  HasDecStrictOrder : Type _
  HasDecStrictOrder = Σ _ IsDecStrictOrder
  
  HasDecOrder→HasDecStrictOrder : HasDecOrder -> HasDecStrictOrder
  HasDecOrder→HasDecStrictOrder (_ , isOrd , isDec) =
    _ , isToset→isLosetIrreflKernel isOrd isDec , isTosetDecidable→isLosetDecidable isOrd isDec

  HasDecStrictOrder→HasDecOrder : HasDecStrictOrder -> HasDecOrder
  HasDecStrictOrder→HasDecOrder (_ , isOrd , isDec) =
    _ , isLoset→isTosetReflClosure isOrd isDec , isLosetDecidable→isTosetDecidable isOrd isDec

  open IsToset
  decOrd→disc : (_≤_ : A -> A -> Type ℓ) -> IsDecOrder (_≤_) -> Discrete A
  decOrd→disc _≤_ (tosetA , _≤?_) x y with x ≤? y | y ≤? x
  ... | yes p | yes q = yes (tosetA .is-antisym x y p q)
  ... | yes p | no ¬q = no λ r -> ¬q (subst (_≤ x) r (tosetA .is-refl x))
  ... | no ¬p | yes q = no λ r -> ¬p (subst (x ≤_) r (tosetA .is-refl x))
  ... | no ¬p | no ¬q = ⊥.rec (P.rec ⊥.isProp⊥ (⊎.rec ¬p ¬q) (tosetA .is-total x y))

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

  module ⋀Toset (isSetA : isSet A) (_⋀_ : A -> A -> A)
                 (⋀Idem : ∀ a -> a ⋀ a ≡ a) (⋀Comm : ∀ a b -> a ⋀ b ≡ b ⋀ a)
                 (⋀AssocR : ∀ a b c -> (a ⋀ b) ⋀ c ≡ a ⋀ (b ⋀ c)) (⋀Total : ∀ a b -> (a ⋀ b ≡ a) ⊔′ (b ⋀ a ≡ b)) where

    _≤_ : A -> A -> Type ℓ
    a ≤ b = (a ⋀ b) ≡ a

    tosetA : IsToset _≤_
    tosetA .is-set = isSetA
    tosetA .is-prop-valued a b = isSetA (a ⋀ b) a
    tosetA .is-refl = ⋀Idem
    tosetA .is-trans a b c a∧b≡a b∧c≡b = congS (_⋀ c) (sym a∧b≡a) ∙ ⋀AssocR a b c ∙ congS (a ⋀_) b∧c≡b ∙ a∧b≡a
    tosetA .is-antisym a b a∧b≡a b∧a≡a = sym a∧b≡a ∙ ⋀Comm a b ∙ b∧a≡a
    tosetA .is-total = ⋀Total

  module Toset⋀Toset (isSetA : isSet A) (_≤_ : A -> A -> Type ℓ) (tosetA : IsToset _≤_) where

    module Tos⋀ = Toset⋀ isSetA _≤_ tosetA
    module ⋀Tos = ⋀Toset isSetA Tos⋀._⋀_ Tos⋀.⋀Idem Tos⋀.⋀Comm Tos⋀.⋀AssocR Tos⋀.⋀Total

    eq : TosetEquiv (toset A _≤_ tosetA) (toset A ⋀Tos._≤_ ⋀Tos.tosetA)
    eq .fst = idEquiv ⟨ toset A _≤_ tosetA ⟩
    eq .snd = istosetequiv λ a b -> propBiimpl→Equiv (tosetA .is-prop-valued a b) (isSetA _ _) Tos⋀.⋀Β₁ Tos⋀.⋀Η₁