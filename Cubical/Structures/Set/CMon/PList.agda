-- Definition taken from https://drops.dagstuhl.de/opus/volltexte/2023/18395/pdf/LIPIcs-ITP-2023-20.pdf
module Cubical.Structures.Set.CMon.PList where

open import Cubical.Structures.Prelude

open import Cubical.Data.List as L

import Cubical.Structures.Free as F
import Cubical.Structures.Set.CMon.Desc as M
import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Set.Mon.List as LM

open import Cubical.Structures.Eq
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Arity hiding (_/_)
open import Cubical.Structures.Set.CMon.QFreeMon

data Perm {ℓ : Level} {A : Type ℓ} : List A -> List A -> Type ℓ where
  permRefl : ∀ {xs} -> Perm xs xs
  permSwap : ∀ {x y xs ys zs} -> Perm (xs ++ x ∷ y ∷ ys) zs -> Perm (xs ++ y ∷ x ∷ ys) zs

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A B : Type ℓ

infixr 30 _∙ₚ_
_∙ₚ_ : ∀ {xs ys zs} -> Perm xs ys -> Perm ys zs -> Perm {A = A} xs zs
permRefl ∙ₚ q = q
(permSwap p) ∙ₚ q = permSwap (p ∙ₚ q)

permSym : ∀ {xs ys} -> Perm xs ys -> Perm {A = A} ys xs
permSym permRefl = permRefl
permSym (permSwap p) = permSym p ∙ₚ permSwap permRefl

permSubst : ∀ {xs ys} -> xs ≡ ys -> Perm {A = A} xs ys
permSubst {xs = xs} p = subst (Perm xs) p permRefl

permCons : ∀ {x xs ys} -> Perm xs ys -> Perm {A = A} (x ∷ xs) (x ∷ ys)
permCons permRefl = permRefl
permCons {x = x} (permSwap {xs = xs} p) = permSwap {xs = x ∷ xs} (permCons p)

permPrepend : (xs : List A) {ys zs : List A} -> Perm ys zs -> Perm (xs ++ ys) (xs ++ zs)
permPrepend [] p = p
permPrepend (x ∷ xs) p = permCons (permPrepend xs p)

permAppend : ∀ {xs ys} -> Perm xs ys -> (zs : List A) -> Perm (xs ++ zs) (ys ++ zs)
permAppend permRefl _ = permRefl
permAppend (permSwap {xs = xs} p) _ =
  permSubst (++-assoc xs _ _) ∙ₚ permSwap (permSubst (sym (++-assoc xs _ _)) ∙ₚ permAppend p _)

permMovehead : (x : A) (xs : List A) {ys : List A} -> Perm (x ∷ xs ++ ys) (xs ++ x ∷ ys)
permMovehead x [] = permRefl
permMovehead x (y ∷ xs) = permSwap {xs = []} (permCons (permMovehead x xs))

⊕Commₚ : (xs ys : List A) -> Perm (xs ++ ys) (ys ++ xs)
⊕Commₚ xs [] = permSubst (++-unit-r xs)
⊕Commₚ xs (y ∷ ys) = permSym (permMovehead y xs {ys = ys}) ∙ₚ permCons (⊕Commₚ xs ys)

module _ {ℓA ℓB} {A : Type ℓA} {𝔜 : struct ℓB M.MonSig} {isSet𝔜 : isSet (𝔜 .car)} (𝔜-cmon : 𝔜 ⊨ M.CMonSEq) (f : A -> 𝔜 .car) where
  module 𝔜 = M.CMonSEq 𝔜 𝔜-cmon

  f♯Hom = LM.Free.♯IsMonHom isSet𝔜 (M.cmonSatMon 𝔜-cmon) f

  f♯ : List A -> 𝔜 .car
  f♯ = f♯Hom .fst

  f♯Append : ∀ xs ys -> f♯ (xs ++ ys) ≡ f♯ xs 𝔜.⊕ f♯ ys
  f♯Append xs ys =
    f♯ (xs ++ ys) ≡⟨ sym ((f♯Hom .snd) M.`⊕ (lookup (xs ∷ ys ∷ []))) ⟩
    𝔜 .alg (M.`⊕ , (λ w -> f♯ (lookup (xs ∷ ys ∷ []) w))) ≡⟨ 𝔜.⊕-eta (lookup (xs ∷ ys ∷ [])) f♯ ⟩
    _ ∎

  f♯Swap : ∀ {x y : A} (xs ys : List A) -> f♯ (xs ++ x ∷ y ∷ ys) ≡ f♯ (xs ++ y ∷ x ∷ ys)
  f♯Swap {x} {y} [] ys =
    f♯ ((L.[ x ] ++ L.[ y ]) ++ ys) ≡⟨ f♯Append (L.[ x ] ++ L.[ y ]) ys  ⟩
    f♯ (L.[ x ] ++ L.[ y ]) 𝔜.⊕ f♯ ys ≡⟨ cong (𝔜._⊕ f♯ ys) (f♯Append L.[ x ] L.[ y ]) ⟩
    (f♯ L.[ x ] 𝔜.⊕ f♯ L.[ y ]) 𝔜.⊕ f♯ ys ≡⟨ cong (𝔜._⊕ f♯ ys) (𝔜.comm _ _) ⟩
    (f♯ L.[ y ] 𝔜.⊕ f♯ L.[ x ]) 𝔜.⊕ f♯ ys ≡⟨ cong (𝔜._⊕ f♯ ys) (sym (f♯Append L.[ y ] L.[ x ])) ⟩
    f♯ (L.[ y ] ++ L.[ x ]) 𝔜.⊕ f♯ ys ≡⟨ sym (f♯Append (L.[ y ] ++ L.[ x ]) ys) ⟩
    f♯ ((L.[ y ] ++ L.[ x ]) ++ ys) ∎
  f♯Swap {x} {y} (a ∷ as) ys =
    f♯ (L.[ a ] ++ (as ++ x ∷ y ∷ ys)) ≡⟨ f♯Append L.[ a ] (as ++ x ∷ y ∷ ys) ⟩
    f♯ L.[ a ] 𝔜.⊕ f♯ (as ++ x ∷ y ∷ ys) ≡⟨ cong (f♯ L.[ a ] 𝔜.⊕_) (f♯Swap as ys) ⟩
    f♯ L.[ a ] 𝔜.⊕ f♯ (as ++ y ∷ x ∷ ys) ≡⟨ sym (f♯Append L.[ a ] (as ++ y ∷ x ∷ ys)) ⟩
    f♯ (L.[ a ] ++ (as ++ y ∷ x ∷ ys)) ≡⟨⟩
    f♯ ((a ∷ as) ++ y ∷ x ∷ ys) ∎

  permRespf♯ : {a b : List A} -> Perm a b -> f♯ a ≡ f♯ b
  permRespf♯ permRefl = refl
  permRespf♯ (permSwap {xs = xs} {ys = ys} p) = f♯Swap xs ys ∙ permRespf♯ p

module _ {ℓ} (A : Type ℓ) where
  open import Cubical.Relation.Binary
  module P = BinaryRelation {A = List A} Perm
  open isPermRel

  isPermRelPerm : isPermRel LM.listDef (Perm {A = A})
  P.isEquivRel.reflexive (isEquivRel isPermRelPerm) _ = permRefl
  P.isEquivRel.symmetric (isEquivRel isPermRelPerm) _ _ = permSym
  P.isEquivRel.transitive (isEquivRel isPermRelPerm) _ _ _ = _∙ₚ_
  isCongruence isPermRelPerm {a} {b} {c} {d} p q = permPrepend a q ∙ₚ permAppend p d
  isCommutative isPermRelPerm {a} {b} = ⊕Commₚ a b
  respSharp isPermRelPerm {isSet𝔜 = isSet𝔜} 𝔜-cmon f p = permRespf♯ {isSet𝔜 = isSet𝔜} 𝔜-cmon f p

  PermRel : PermRelation LM.listDef A
  PermRel = Perm , isPermRelPerm

module PListDef = F.Definition M.MonSig M.CMonEqSig M.CMonSEq

plistFreeDef : ∀ {ℓ} -> PListDef.Free ℓ ℓ 2
plistFreeDef = qFreeMonDef (PermRel _)
