module Cubical.Structures.Free where

open import Cubical.Structures.Prelude

open import Cubical.Data.List as L
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Functions.Image
open import Cubical.Foundations.Univalence

open import Cubical.Categories.Monad.Base
open import Cubical.Categories.Functor renaming (𝟙⟨_⟩ to funcId)
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets

open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.HITs.SetQuotients as Q

open import Cubical.Reflection.RecordEquiv

open import Cubical.Structures.Sig
open import Cubical.Structures.Str
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq

-- defines a free structure on a signature and equations
module Definition {f a e n s : Level} (σ : Sig f a) (τ : EqSig e (ℓ-max n s)) (ε : sysEq {n = ℓ-max n s} σ τ) where
  ns : Level
  ns = ℓ-max n s

  record Free (ℓ ℓ' : Level) (h : HLevel) : Type (ℓ-suc (ℓ-max ℓ' (ℓ-max ℓ (ℓ-max f (ℓ-max a (ℓ-max e ns)))))) where
    field
      F : (X : Type ℓ) -> Type (ℓ-max ℓ ns)
      η : {X : Type ℓ} -> X -> F X
      α : {X : Type ℓ} -> sig σ (F X) -> F X
      sat : {X : Type ℓ} -> < F X , α > ⊨ ε
      trunc : {X : Type ℓ} -> isOfHLevel h X -> isOfHLevel h (F X)
      isFree : {X : Type ℓ}
        {𝔜 : struct (ℓ-max ℓ' ns) σ}
        (H : isOfHLevel h (𝔜 .car)) (ϕ : 𝔜 ⊨ ε)
        -> isEquiv (\(f : structHom {x = ℓ-max ℓ ns} < F X , α > 𝔜) -> f .fst ∘ η)

    σStruct : Type ℓ -> _
    σStruct X = < F X , α >

    ext : {X : Type ℓ} {𝔜 : struct (ℓ-max ℓ' ns) σ}
          (H : isOfHLevel h (𝔜 .car)) (ϕ : 𝔜 ⊨ ε)
       -> (hom : X -> 𝔜 .car) -> structHom < F X , α > 𝔜
    ext H ϕ = invIsEq (isFree H ϕ)

    ext-β : {X : Type ℓ} {𝔜 : struct (ℓ-max ℓ' ns) σ}
            (H : isOfHLevel h (𝔜 .car)) (ϕ : 𝔜 ⊨ ε) (Hom : structHom < F X , α > 𝔜)
         -> ext H ϕ (Hom .fst ∘ η) ≡ Hom
    ext-β H ϕ = retIsEq (isFree H ϕ)

    ext-η : {X : Type ℓ} {𝔜 : struct (ℓ-max ℓ' ns) σ}
            (H : isOfHLevel h (𝔜 .car)) (ϕ : 𝔜 ⊨ ε) (h : X -> 𝔜 .car)
         -> (ext H ϕ h .fst) ∘ η ≡ h
    ext-η H ϕ = secIsEq (isFree H ϕ)

    hom≡ : {X : Type ℓ} {𝔜 : struct (ℓ-max ℓ' ns) σ}
        -> (H : isOfHLevel h (𝔜 .car)) (ϕ : 𝔜 ⊨ ε)
        -> (H1 H2 : structHom < F X , α > 𝔜)
        -> H1 .fst ∘ η ≡ H2 .fst ∘ η
        -> H1 ≡ H2
    hom≡ H ϕ H1 H2 α = sym (ext-β H ϕ H1) ∙ cong (ext H ϕ) α ∙ ext-β H ϕ H2

  open Free
  module _ {ℓ} {A : Type ℓ} (𝔛 : Free ℓ ℓ 2) (𝔜 : Free ℓ ℓ 2) (isSetA : isSet A) where
    private
      str𝔛 : struct (ℓ-max (ℓ-max n s) ℓ) σ
      str𝔛 = < 𝔛 .F A , 𝔛 .α >

      str𝔜 : struct (ℓ-max (ℓ-max n s) ℓ) σ
      str𝔜 = < 𝔜 .F A , 𝔜 .α >

      isSet𝔜 : isSet (𝔜 .F A)
      isSet𝔜 = 𝔜 .trunc isSetA

      isSet𝔛 : isSet (𝔛 .F A)
      isSet𝔛 = 𝔛 .trunc isSetA

      ϕ1 : structHom str𝔛 str𝔜
      ϕ1 = ext 𝔛 isSet𝔜 (𝔜 .sat) (𝔜 .η)

      ϕ2 : structHom str𝔜 str𝔛
      ϕ2 = ext 𝔜 isSet𝔛 (𝔛 .sat) (𝔛 .η)

      ϕ1∘ϕ2 : structHom str𝔜 str𝔜
      ϕ1∘ϕ2 = structHom∘ str𝔜 str𝔛 str𝔜 ϕ1 ϕ2

      ϕ2∘ϕ1 : structHom str𝔛 str𝔛
      ϕ2∘ϕ1 = structHom∘ str𝔛 str𝔜 str𝔛 ϕ2 ϕ1

      ϕ1∘ϕ2≡ : ϕ1∘ϕ2 .fst ∘ 𝔜 .η ≡ idHom str𝔜 .fst ∘ 𝔜 .η
      ϕ1∘ϕ2≡ =
          ϕ1 .fst ∘ ((ext 𝔜 isSet𝔛 (𝔛 .sat) (𝔛 .η) .fst) ∘ 𝔜 .η)
        ≡⟨ congS (ϕ1 .fst ∘_) (ext-η 𝔜 isSet𝔛 (𝔛 .sat) (𝔛 .η)) ⟩
          ext 𝔛 isSet𝔜 (𝔜 .sat) (𝔜 .η) .fst ∘ 𝔛 .η
        ≡⟨ ext-η 𝔛 isSet𝔜 (𝔜 .sat) (𝔜 .η) ⟩
          𝔜 .η ∎

      ϕ2∘ϕ1≡ : ϕ2∘ϕ1 .fst ∘ 𝔛 .η ≡ idHom str𝔛 .fst ∘ 𝔛 .η
      ϕ2∘ϕ1≡ =
          ϕ2 .fst ∘ ((ext 𝔛 isSet𝔜 (𝔜 .sat) (𝔜 .η) .fst) ∘ 𝔛 .η)
        ≡⟨ congS (ϕ2 .fst ∘_) (ext-η 𝔛 isSet𝔜 (𝔜 .sat) (𝔜 .η)) ⟩
          ext 𝔜 isSet𝔛 (𝔛 .sat) (𝔛 .η) .fst ∘ 𝔜 .η
        ≡⟨ ext-η 𝔜 isSet𝔛 (𝔛 .sat) (𝔛 .η) ⟩
          𝔛 .η ∎

    freeIso : Iso (𝔛 .F A) (𝔜 .F A)
    freeIso = iso (ϕ1 .fst) (ϕ2 .fst)
      (λ x -> congS (λ f -> f .fst x) (hom≡ 𝔜 isSet𝔜 (𝔜 .sat) ϕ1∘ϕ2 (idHom str𝔜) ϕ1∘ϕ2≡))
      (λ x -> congS (λ f -> f .fst x) (hom≡ 𝔛 isSet𝔛 (𝔛 .sat) ϕ2∘ϕ1 (idHom str𝔛) ϕ2∘ϕ1≡))

    freeIsoFunHom : structIsHom str𝔛 str𝔜 (Iso.fun freeIso)
    freeIsoFunHom = ϕ1 .snd

    freeIsoInvHom : structIsHom str𝔜 str𝔛 (Iso.inv freeIso)
    freeIsoInvHom = ϕ2 .snd

    free≡ : 𝔛 .F A ≡ 𝔜 .F A
    free≡ = ua (isoToEquiv freeIso)

    η≡ : ∀ x -> PathP (λ i -> free≡ i) (𝔛 .η x) (𝔜 .η x)
    η≡ x = toPathP $
      transport free≡ (𝔛 .η x) ≡⟨⟩
      transport (λ i -> 𝔜 .F A) (ϕ1 .fst (𝔛 .η x)) ≡⟨ sym (transport-filler refl (ϕ1 .fst (𝔛 .η x))) ⟩
      ϕ1 .fst (𝔛 .η x) ≡⟨ cong (λ f -> f x) (ext-η 𝔛 isSet𝔜 (𝔜 .sat) (𝔜 .η)) ⟩
      η 𝔜 x ∎

  -- Alternative definition where F is paramterized, used for transporting Free proofs
  record FreeAux (ℓ ℓ' : Level) (h : HLevel) (F : (X : Type ℓ) -> Type (ℓ-max ℓ ns)) : Type (ℓ-suc (ℓ-max ℓ' (ℓ-max ℓ (ℓ-max f (ℓ-max a (ℓ-max e ns)))))) where
    field
      η : {X : Type ℓ} -> X -> F X
      α : {X : Type ℓ} -> sig σ (F X) -> F X
      sat : {X : Type ℓ} -> < F X , α > ⊨ ε
      trunc : {X : Type ℓ} -> isOfHLevel h X -> isOfHLevel h (F X)
      isFree : {X : Type ℓ}
        {𝔜 : struct (ℓ-max ℓ' ns) σ}
        (H : isOfHLevel h (𝔜 .car)) (ϕ : 𝔜 ⊨ ε)
        -> isEquiv (\(f : structHom {x = ℓ-max ℓ ns} < F X , α > 𝔜) -> f .fst ∘ η)

  isoAux : {ℓ ℓ' : Level} {h : HLevel} ->
           Iso (Σ[ F ∈ ((X : Type ℓ) -> Type (ℓ-max ℓ ns)) ] FreeAux ℓ ℓ' h F) (Free ℓ ℓ' h)
  isoAux {ℓ = ℓ} {ℓ' = ℓ'} {h = h} = iso to from (λ _ -> refl) (λ _ -> refl)
    where
    to : Σ[ F ∈ ((X : Type ℓ) -> Type (ℓ-max ℓ ns)) ] FreeAux ℓ ℓ' h F -> Free ℓ ℓ' h
    Free.F (to (F , aux)) = F
    Free.η (to (F , aux)) = FreeAux.η aux
    Free.α (to (F , aux)) = FreeAux.α aux
    Free.sat (to (F , aux)) = FreeAux.sat aux
    Free.isFree (to (F , aux)) = FreeAux.isFree aux
    Free.trunc (to (F , aux)) = FreeAux.trunc aux

    from : Free ℓ ℓ' h -> Σ[ F ∈ ((X : Type ℓ) -> Type (ℓ-max ℓ ns)) ] FreeAux ℓ ℓ' h F
    fst (from free) = Free.F free
    FreeAux.η (snd (from free)) = Free.η free
    FreeAux.α (snd (from free)) = Free.α free
    FreeAux.sat (snd (from free)) = Free.sat free
    FreeAux.isFree (snd (from free)) = Free.isFree free
    FreeAux.trunc (snd (from free)) = Free.trunc free

module SameLevel {ℓ' f a e n s : Level} (σ : Sig f a) (τ : EqSig e (ℓ-max n s)) (ε : sysEq {n = ℓ-max n s} σ τ) where
  open Definition {n = n} {s = s} σ τ ε

  ℓ : Level
  ℓ = ℓ-max ℓ' ns

  module Equalities {h : HLevel} (freeDef : Free ℓ ℓ' h) where
    open Free freeDef

    ext-η-id : {X : Type ℓ}
      -> (isHX : isOfHLevel h X)
      -> ext (trunc isHX) sat η ≡ idHom (σStruct X)
    ext-η-id isHX = ext-β (trunc isHX) sat (idHom (σStruct _))

    ext-∘ : ∀ {A B C : Type ℓ} (isHB : isOfHLevel h B) (isHC : isOfHLevel h C)
            (f : A -> F B) (g : B -> F C)
         -> ext (trunc isHC) sat (ext (trunc isHC) sat g .fst ∘ f) ≡ structHom∘ (σStruct A) (σStruct B) (σStruct C) (ext (trunc isHC) sat g) (ext (trunc isHB) sat f)
    ext-∘ isHB isHC f g = hom≡ (trunc isHC) sat _ _ $
        ext (trunc isHC) sat (ext (trunc isHC) sat g .fst ∘ f) .fst ∘ η
      ≡⟨ ext-η (trunc isHC) sat _ ⟩
        ext (trunc isHC) sat g .fst ∘ f
      ≡⟨ sym (congS (ext (trunc isHC) sat g .fst ∘_) (ext-η (trunc isHB) sat f)) ⟩
        ext (trunc isHC) sat g .fst ∘ ext (trunc isHB) sat f .fst ∘ η ∎

  module Categories (freeDef : Free ℓ ℓ' 2) where
    open Free freeDef
    open Equalities freeDef
    open Functor

    EndofunctorOnSet : Type _
    EndofunctorOnSet = Functor (SET ℓ) (SET ℓ)

    module _ (F G : EndofunctorOnSet) where
      PreNatTransOnSet : Type _
      PreNatTransOnSet = ∀ X -> F .F-ob X .fst -> G .F-ob X .fst

      NatTransSatSquare : PreNatTransOnSet -> Type _
      NatTransSatSquare η = ∀ X Y f -> η Y ∘ F .F-hom f ≡ G .F-hom f ∘ η X

      isPropNatTransSatSquare : ∀ η -> isProp (NatTransSatSquare η)
      isPropNatTransSatSquare η = isPropΠ3 λ X Y f ->
        isSetΠ (λ _ -> G .F-ob Y .snd) (η Y ∘ F .F-hom f) (G .F-hom f ∘ η X)

      NatTransSetΣ : Type _
      NatTransSetΣ = Σ PreNatTransOnSet NatTransSatSquare

      setNaturalTrans : ∀ η (square : NatTransSatSquare η) -> NatTrans F G
      setNaturalTrans η square .NatTrans.N-ob = η
      setNaturalTrans η square .NatTrans.N-hom {x = X} {y = Y} f = square X Y f

      NatTransSetIso : Iso NatTransSetΣ (NatTrans F G)
      NatTransSetIso = iso (uncurry setNaturalTrans) (λ nat -> NatTrans.N-ob nat , λ X Y -> NatTrans.N-hom nat)
        (λ (natTrans N-ob N-hom) -> refl)
        (λ (N-ob , N-hom) -> refl)

      NatTransSet≡ : ∀ (η1 η2 : NatTrans F G) -> NatTrans.N-ob η1 ≡ NatTrans.N-ob η2 -> η1 ≡ η2
      NatTransSet≡ (natTrans N-ob1 N-hom1) (natTrans N-ob2 N-hom2) eq≡ =
        isoInvInjective NatTransSetIso (natTrans N-ob1 N-hom1) (natTrans N-ob2 N-hom2) (Σ≡Prop isPropNatTransSatSquare eq≡)

    algFunctor : EndofunctorOnSet
    algFunctor .Functor.F-ob (A , isSetA) =
      F A , trunc isSetA
    algFunctor .Functor.F-hom {y = Yset} f =
      ext (trunc (Yset .snd)) sat (η ∘ f) .fst
    algFunctor .Functor.F-id {x = Xset} =
      congS fst (ext-β (trunc (Xset .snd)) sat (idHom (σStruct _)))
    algFunctor .Functor.F-seq {x = Xset} {y = Yset} {z = Zset} f g = congS fst $
      hom≡ (trunc (Zset .snd)) sat
        (ext (trunc (Zset .snd)) sat (η ∘ g ∘ f))
        (structHom∘ (σStruct (Xset .fst)) (σStruct (Yset .fst)) (σStruct (Zset .fst)) (ext (trunc (Zset .snd)) sat (η ∘ g)) (ext (trunc (Yset .snd)) sat (η ∘ f))) $ sym $
          ext (trunc (Zset .snd)) sat (η ∘ g) .fst ∘ ext (trunc (Yset .snd)) sat (η ∘ f) .fst ∘ η
        ≡⟨ congS (ext (trunc (Zset .snd)) sat (η ∘ g) .fst ∘_) (ext-η (trunc (Yset .snd)) sat (η ∘ f)) ⟩
          ext (trunc (Zset .snd)) sat (η ∘ g) .fst ∘ η ∘ f
        ≡⟨ congS (_∘ f) (ext-η (trunc (Zset .snd)) sat (η ∘ g)) ⟩
          η ∘ g ∘ f
        ≡⟨ sym (ext-η (trunc (Zset .snd)) sat (η ∘ g ∘ f)) ⟩
          ext (trunc (Zset .snd)) sat (η ∘ g ∘ f) .fst ∘ η ∎

    algIsMonad : IsMonad algFunctor
    algIsMonad .IsMonad.η =
      setNaturalTrans _ _ (λ X x -> η x) (λ X Y f -> sym (ext-η (trunc _) sat (η ∘ f)))
    algIsMonad .IsMonad.μ =
      setNaturalTrans _ _ (λ X fx -> ext (trunc (X .snd)) sat (idfun _) .fst fx) λ X Y f -> congS fst $
        hom≡ (trunc (Y .snd)) sat
          (structHom∘ (σStruct (F _)) (σStruct (F (Y .fst))) (σStruct (Y .fst)) (ext (trunc (Y .snd)) sat (idfun _)) (ext (trunc (trunc (Y .snd))) sat (η ∘ ext (trunc (Y .snd)) sat (η ∘ f) .fst)))
          (structHom∘ (σStruct (F _)) (σStruct (X .fst)) (σStruct (Y .fst)) (ext (trunc (Y .snd)) sat (η ∘ f)) (ext (trunc (X .snd)) sat (idfun _))) $
          ext (trunc _) sat (idfun _) .fst ∘ (ext _ sat (η ∘ ext (trunc _) sat (η ∘ f) .fst) .fst) ∘ η
        ≡⟨ congS (ext (trunc (Y .snd)) sat (idfun _) .fst ∘_) (ext-η (trunc (trunc (Y .snd))) sat (η ∘ ext (trunc _) sat (η ∘ f) .fst)) ⟩
          ext (trunc (Y .snd)) sat (idfun _) .fst ∘ η ∘ ext (trunc (Y .snd)) sat (η ∘ f) .fst
        ≡⟨ congS (_∘ ext (trunc (Y .snd)) sat (η ∘ f) .fst) (ext-η (trunc (Y .snd)) sat (idfun _)) ⟩
          ext (trunc (Y .snd)) sat (η ∘ f) .fst
        ≡⟨ congS (ext (trunc (Y .snd)) sat (η ∘ f) .fst ∘_) (sym (ext-η (trunc (X .snd)) sat (idfun _))) ⟩
          ext (trunc (Y .snd)) sat (η ∘ f) .fst ∘ ext (trunc (X .snd)) sat (idfun _) .fst ∘ η ∎
    algIsMonad .IsMonad.idl-μ = toPathP $ NatTransSet≡ _ _ _ _ $
        transport refl (λ X -> ext (trunc (X .snd)) sat (idfun _) .fst ∘ η)
      ≡⟨ transportRefl _ ⟩
        (λ X -> ext (trunc (X .snd)) sat (idfun _) .fst ∘ η)
      ≡⟨ funExt (λ X -> ext-η (trunc (X .snd)) sat (idfun _)) ⟩
        (λ X -> idfun _) ∎
    algIsMonad .IsMonad.idr-μ = toPathP $ NatTransSet≡ _ _ _ _ $
        transport refl (λ X → ext (trunc (X .snd)) sat (idfun _) .fst ∘ ext (trunc (trunc (X .snd))) sat (η ∘ η) .fst)
      ≡⟨ transportRefl _ ⟩
        (λ X -> ext (trunc (X .snd)) sat (idfun _) .fst ∘ ext (trunc (trunc (X .snd))) sat (η ∘ η) .fst)
      ≡⟨ funExt (λ X -> sym (congS fst (ext-∘ (trunc (X .snd)) (X .snd) (η ∘ η) (idfun _)))) ⟩
        (λ X -> ext (trunc (X .snd)) sat (ext (trunc (X .snd)) sat (idfun _) .fst ∘ η ∘ η) .fst)
      ≡⟨ funExt (λ X -> congS (λ f -> ext (trunc (X .snd)) sat (f ∘ η) .fst) (ext-η (trunc (X .snd)) sat (idfun _))) ⟩
        (λ X -> ext (trunc (X .snd)) sat η .fst)
      ≡⟨ funExt (λ X -> congS fst (ext-η-id (X .snd))) ⟩
        (λ X -> idfun _) ∎
    algIsMonad .IsMonad.assoc-μ = {!   !}