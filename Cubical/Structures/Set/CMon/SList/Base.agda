module Cubical.Structures.Set.CMon.SList.Base where

open import Cubical.Structures.Prelude

open import Cubical.Data.Empty as ⊥
import Cubical.Data.List as L
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma

open import Cubical.Induction.WellFounded

import Cubical.Structures.Set.CMon.Desc as M
import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity
open import Cubical.HITs.FiniteMultiset public renaming (FMSet to SList; comm to swap)

pattern [_] a = a ∷ []

private
  variable
    ℓ : Level
    A : Type ℓ

slistAlpha : ∀ {n : Level} {X : Type n} -> sig M.MonSig (SList X) -> SList X
slistAlpha (M.`e , i) = []
slistAlpha (M.`⊕ , i) = i fzero ++ i fone

module Free {x y : Level} {A : Type x} {𝔜 : struct y M.MonSig} (isSet𝔜 : isSet (𝔜 .car)) (𝔜Cmon : 𝔜 ⊨ M.CMonSEq) where
  module 𝔜 = M.CMonSEq 𝔜 𝔜Cmon

  𝔛 : M.CMonStruct
  𝔛 = < SList A , slistAlpha >

  module _ (f : A -> 𝔜 .car) where
    _♯ : SList A -> 𝔜 .car
    _♯ = Elim.f 𝔜.e
      (λ x xs -> (f x) 𝔜.⊕ xs)
      (λ a b xs i ->
        ( sym (𝔜.assocr (f a) (f b) xs)
        ∙ cong (𝔜._⊕ xs) (𝔜.comm (f a) (f b))
        ∙ 𝔜.assocr (f b) (f a) xs
        ) i
      )
      (λ _ -> isSet𝔜)

    -- export these for computation
    ♯⊕ : ∀ xs ys -> (xs ++ ys) ♯ ≡ (xs ♯) 𝔜.⊕ (ys ♯)
    ♯⊕ = ElimProp.f (isPropΠ λ _ -> isSet𝔜 _ _)
      (λ ys -> sym (𝔜.unitl (ys ♯)))
      (λ a {xs} p ys ->
        f a 𝔜.⊕ ((xs ++ ys) ♯) ≡⟨ cong (f a 𝔜.⊕_) (p ys) ⟩
        f a 𝔜.⊕ ((xs ♯) 𝔜.⊕ (ys ♯)) ≡⟨ sym (𝔜.assocr (f a) (xs ♯) (ys ♯)) ⟩
        _
      ∎)

    ♯-∷ : ∀ x xs -> (x ∷ xs) ♯ ≡ (f x) 𝔜.⊕ (xs ♯)
    ♯-∷ x xs = ♯⊕ [ x ] xs ∙ congS (𝔜._⊕ (xs ♯)) (𝔜.unitr (f x))

    ♯IsMonHom : structHom 𝔛 𝔜
    fst ♯IsMonHom = _♯
    snd ♯IsMonHom M.`e i = 𝔜.eEta
    snd ♯IsMonHom M.`⊕ i = 𝔜.⊕Eta i _♯ ∙ sym (♯⊕ (i fzero) (i fone))

  private
    slistEquivLemma : (g : structHom 𝔛 𝔜) -> (x : SList A) -> g .fst x ≡ ((g .fst ∘ [_]) ♯) x
    slistEquivLemma (g , homMonWit) = ElimProp.f (isSet𝔜 _ _)
      (sym (homMonWit M.`e (lookup L.[])) ∙ 𝔜.eEta)
      (λ x {xs} p ->
        g (x ∷ xs) ≡⟨ sym (homMonWit M.`⊕ (lookup ([ x ] L.∷ xs L.∷ L.[]))) ⟩
        _ ≡⟨ 𝔜.⊕Eta (lookup ([ x ] L.∷ xs L.∷ L.[])) g ⟩
        _ ≡⟨ cong (g [ x ] 𝔜.⊕_) p ⟩
        _ ∎
      )

    slistEquivLemmaβ : (g : structHom 𝔛 𝔜) -> g ≡ ♯IsMonHom (g .fst ∘ [_])
    slistEquivLemmaβ g = structHom≡ 𝔛 𝔜 g (♯IsMonHom (g .fst ∘ [_])) isSet𝔜 (funExt (slistEquivLemma g))

  slistMonEquiv : structHom 𝔛 𝔜 ≃ (A -> 𝔜 .car)
  slistMonEquiv =
    isoToEquiv (iso (λ g -> g .fst ∘ [_]) ♯IsMonHom (λ g -> funExt (𝔜.unitr ∘ g)) (sym ∘ slistEquivLemmaβ))

module SListDef = F.Definition M.MonSig M.CMonEqSig M.CMonSEq

slistSat : ∀ {n} {X : Type n} -> < SList X , slistAlpha > ⊨ M.CMonSEq
slistSat (M.`mon M.`unitl) ρ = unitl-++ (ρ fzero)
slistSat (M.`mon M.`unitr) ρ = unitr-++ (ρ fzero)
slistSat (M.`mon M.`assocr) ρ = sym (assoc-++ (ρ fzero) (ρ fone) (ρ ftwo))
slistSat M.`comm ρ = comm-++ (ρ fzero) (ρ fone)

slistDef : ∀ {ℓ ℓ'} -> SListDef.Free ℓ ℓ' 2
F.Definition.Free.F slistDef = SList
F.Definition.Free.η slistDef = [_]
F.Definition.Free.α slistDef = slistAlpha
F.Definition.Free.sat slistDef = slistSat
F.Definition.Free.isFree slistDef isSet𝔜 satMon = (Free.slistMonEquiv isSet𝔜 satMon) .snd
