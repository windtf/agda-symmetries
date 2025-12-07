module Cubical.Structures.Set.CMon.Desc where

open import Cubical.Structures.Prelude

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.List
open import Cubical.Data.Nat hiding (min)
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Relation.Binary.Order.Toset

open import Cubical.Functions.Logic as L

open import Cubical.Structures.Arity as F public
open import Cubical.Structures.Eq
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree

import Cubical.Structures.Set.Mon.Desc as M

open M.MonSym

CMonSym = M.MonSym
CMonAr = M.MonAr
CMonFinSig = M.MonFinSig
CMonSig = M.MonSig

CMonStruct : ∀ {n} -> Type (ℓ-suc n)
CMonStruct {n} = struct n CMonSig

CMon→Mon : ∀ {ℓ} -> CMonStruct {ℓ} -> M.MonStruct {ℓ}
car (CMon→Mon 𝔛) = 𝔛 .car
alg (CMon→Mon 𝔛) = 𝔛 .alg

module CMonStruct {ℓ} (𝔛 : CMonStruct {ℓ}) where
  open M.MonStruct (CMon→Mon 𝔛) public

data CMonEq : Type where
  `mon : M.MonEq -> CMonEq
  `comm : CMonEq

CMonEqFree : CMonEq -> ℕ
CMonEqFree (`mon eqn) = M.MonEqFree eqn
CMonEqFree `comm = 2

CMonEqSig : EqSig ℓ-zero ℓ-zero
CMonEqSig = finEqSig (CMonEq , CMonEqFree)

cmonEqLhs : (eq : CMonEq) -> FinTree CMonFinSig (CMonEqFree eq)
cmonEqLhs (`mon eqn) = M.monEqLhs eqn
cmonEqLhs `comm = node (`⊕ , lookup (leaf fzero ∷ leaf fone ∷ []))

cmonEqRhs : (eq : CMonEq) -> FinTree CMonFinSig (CMonEqFree eq)
cmonEqRhs (`mon eqn) = M.monEqRhs eqn
cmonEqRhs `comm = node (`⊕ , lookup (leaf fone ∷ leaf fzero ∷ []))

CMonSEq : sysEq CMonSig CMonEqSig
CMonSEq n = cmonEqLhs n , cmonEqRhs n

cmonSatMon : ∀ {s} {str : struct s CMonSig} -> str ⊨ CMonSEq -> str ⊨ M.MonSEq
cmonSatMon {_} {str} cmonSat eqn ρ = cmonSat (`mon eqn) ρ

module CMonSEq {ℓ} (𝔛 : CMonStruct {ℓ}) (ϕ : 𝔛 ⊨ CMonSEq) where
  open M.MonSEq (CMon→Mon 𝔛) (cmonSatMon ϕ) public

  comm : ∀ m n -> m ⊕ n ≡ n ⊕ m
  comm m n =
      m ⊕ n
    ≡⟨⟩
      𝔛 .alg (`⊕ , lookup (m ∷ n ∷ []))
    ≡⟨ cong (λ z -> 𝔛 .alg (`⊕ , z)) (funExt lemma1) ⟩
      𝔛 .alg (`⊕ , (λ x -> sharp CMonSig 𝔛 (lookup (m ∷ n ∷ [])) (lookup (leaf fzero ∷ leaf fone ∷ []) x)))
    ≡⟨ ϕ `comm (lookup (m ∷ n ∷ [])) ⟩
      𝔛 .alg (`⊕ , (λ x -> sharp CMonSig 𝔛 (lookup (m ∷ n ∷ [])) (lookup (leaf fone ∷ leaf fzero ∷ []) x)))
    ≡⟨ cong (λ z -> 𝔛 .alg (`⊕ , z)) (sym (funExt lemma2)) ⟩
      𝔛 .alg (`⊕ , lookup (n ∷ m ∷ []))
    ≡⟨⟩
      n ⊕ m ∎
    where
      open import Cubical.Data.Nat.Order
      lemma1 : (w : CMonSig .arity `⊕) -> lookup (m ∷ n ∷ []) w ≡ sharp CMonSig 𝔛 (lookup (m ∷ n ∷ [])) (lookup (leaf fzero ∷ leaf fone ∷ []) w)
      lemma1 (zero , p) = refl
      lemma1 (suc zero , p) = refl
      lemma1 (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

      lemma2 : (w : CMonSig .arity `⊕) -> lookup (n ∷ m ∷ []) w ≡ sharp CMonSig 𝔛 (lookup (m ∷ n ∷ [])) (lookup (leaf fone ∷ leaf fzero ∷ []) w)
      lemma2 (zero , p) = refl
      lemma2 (suc zero , p) = refl
      lemma2 (suc (suc n) , p) = ⊥.rec (¬m+n<m {m = 2} p)

ℕCMonStr : CMonStruct
ℕCMonStr = M.ℕ-MonStr

ℕCMonStrMonSEq : ℕCMonStr ⊨ CMonSEq
ℕCMonStrMonSEq (`mon eqn) ρ = M.ℕ-MonStr-MonSEq eqn ρ
ℕCMonStrMonSEq `comm ρ = +-comm (ρ fzero) (ρ fone)

⊔MonStrCMonSEq : (ℓ : Level) -> M.⊔-MonStr ℓ ⊨ CMonSEq
⊔MonStrCMonSEq ℓ (`mon eqn) ρ = M.⊔-MonStr-MonSEq ℓ eqn ρ
⊔MonStrCMonSEq ℓ `comm ρ = ⊔-comm (ρ fzero) (ρ fone)

⊓MonStrCMonSEq : (ℓ : Level) -> M.⊓-MonStr ℓ ⊨ CMonSEq
⊓MonStrCMonSEq ℓ (`mon eqn) ρ = M.⊓-MonStr-MonSEq ℓ eqn ρ
⊓MonStrCMonSEq ℓ `comm ρ = ⊓-comm (ρ fzero) (ρ fone)

module Minimum {ℓ : Level} (A : Type ℓ) (AToset : TosetStr ℓ A) where
  import Cubical.Structures.Free as F
  import Cubical.Structures.Semilattices
  module FreeCMonDef = F.Definition M.MonSig CMonEqSig CMonSEq
  open TosetStr AToset
  open Toset.Toset⋀ is-set _≤_ isToset

  Maybe-CMonStr : CMonStruct
  Maybe-CMonStr .car = Maybe A
  Maybe-CMonStr .alg (`e , i) = nothing
  Maybe-CMonStr .alg (`⊕ , i) with i fzero | i fone
  ... | nothing | x = x
  ... | just x | nothing = just x
  ... | just x | just y  = just (x ⋀ y)

  Maybe-CMonStrCMonSEq : Maybe-CMonStr ⊨ CMonSEq
  Maybe-CMonStrCMonSEq (`mon M.`unitl) ρ = refl
  Maybe-CMonStrCMonSEq (`mon M.`unitr) ρ with ρ fzero
  ... | nothing = refl
  ... | just x  = refl
  Maybe-CMonStrCMonSEq (`mon M.`assocr) ρ with ρ fzero | ρ fone | ρ ftwo
  ... | nothing | _       | _ = refl
  ... | just x  | nothing | _ = refl
  ... | just x  | just y  | nothing = refl
  ... | just x  | just y  | just z  = congS just (⋀AssocR x y z)
  Maybe-CMonStrCMonSEq `comm ρ with ρ fzero | ρ fone
  ... | nothing | nothing = refl
  ... | nothing | just x  = refl
  ... | just x  | nothing = refl
  ... | just x  | just y  = congS just (⋀Comm x y)

  private
    isSetMaybeA : isSet (Maybe A)
    isSetMaybeA = isOfHLevelMaybe zero is-set

  module _ (freeCMonDef : ∀ {ℓ' ℓ''} -> FreeCMonDef.Free ℓ' ℓ'' 2) where
    minHom : structHom _ Maybe-CMonStr
    minHom = FreeCMonDef.Free.ext freeCMonDef isSetMaybeA Maybe-CMonStrCMonSEq just

    min : F.Definition.Free.F freeCMonDef A -> Maybe A
    min = minHom .fst
