module Cubical.Structures.Free where

open import Cubical.Structures.Prelude

open import Cubical.Data.List as L
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Functions.Image
open import Cubical.Foundations.Univalence

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

  module _ {ℓ : Level} {h : HLevel} (freeDef : Free ℓ ℓ h) where
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

    -- η≡ : ∀ x -> PathP (λ i -> free≡ i) (𝔛 .η x) (𝔜 .η x)
    -- η≡ x = toPathP $
    --   transport free≡ (𝔛 .η x) ≡⟨⟩
    --   transport (λ i -> 𝔜 .F A) (ϕ1 .fst (𝔛 .η x)) ≡⟨ sym (transport-filler refl (ϕ1 .fst (𝔛 .η x))) ⟩
    --   ϕ1 .fst (𝔛 .η x) ≡⟨⟩
    --   {!   !}

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
