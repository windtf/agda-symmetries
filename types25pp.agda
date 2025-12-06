module types25pp where

open import Cubical.Relation.Binary.Order
open import Cubical.Structures.Prelude

open import Cubical.Structures.Sig
open import Cubical.Structures.Str
open import Cubical.Structures.Free
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq


-- Section 2.1 Algebras
definition-1 : _
definition-1 = Sig

definition-3 : _
definition-3 = sig

definition-5 : _
definition-5 = struct

definition-7 : _
definition-7 = structHom

-- Section 2.2 Free Algebras
definition-9 : _
definition-9 = Definition.Free

definition-10 : _
definition-10 = Definition.Free.ext

proposition-11 : _
proposition-11 = Definition.freeIso

definition-14 : _
definition-14 = Tree

proposition-16 : _
proposition-16 = trEquiv

-- Section 2.3 Equations
definition-17 : _
definition-17 = EqSig

definition-19 : _
definition-19 = eqsig

definition-20 : _
definition-20 = sysEq

definition-22 : _
definition-22 = _⊨_

-- Section 3.1: Lists
open import Cubical.Data.List
import Cubical.Structures.Set.Mon.List as ListMon

definition-23 : _
definition-23 = List

proposition-26 : _
proposition-26 = ListMon.Free.♯IsMonHom

proposition-27 : _
proposition-27 = ListMon.listDef

-- Section 3.2: Arrays
import Cubical.Structures.Set.Mon.Array as ArrayMon

definition-28 : _
definition-28 = ArrayMon.Array

lemma-29 : _
lemma-29 = ArrayMon.eEta

definition-30 : _
definition-30 = ArrayMon._⊕_

proposition-31 : _
proposition-31 = ArrayMon.arraySat

lemma-32 : _
lemma-32 = ArrayMon.η+fsuc

lemma-33 : _
lemma-33 = ArrayMon.⊕Split

definition-34 : _
definition-34 = ArrayMon.Free._♯

proposition-35 : _
proposition-35 = ArrayMon.Free.♯IsMonHom

proposition-36 : _
proposition-36 = ArrayMon.arrayDef

-- Section 4.1: Free monoids quotiented by permutation relations
import Cubical.Structures.Set.CMon.QFreeMon as QFreeMon

definition-37 : _
definition-37 = QFreeMon.isPermRel

proposition-38 : _
proposition-38 = QFreeMon.QFreeMon.qFreeMonSat

definition-39 : _
definition-39 = QFreeMon.QFreeMon.IsFree._♯

proposition-40 : _
proposition-40 = QFreeMon.qFreeMonDef

-- Section 4.2: Lists quotiented by permutation relations
import Cubical.Structures.Set.CMon.PList as PList

definition-41 : _
definition-41 = PList.Perm

proposition-42 : _
proposition-42 = PList.permRespf♯

-- Section 4.3: Swap lists
definition-43 : _
definition-43 = SList

-- Section 4.4: Bag
import Cubical.Structures.Set.CMon.Bag as Bag

definition-46 : _
definition-46 = Bag.Bag

proposition-47 : _
proposition-47 = Bag.trans≈ -- TODO: × other properties of ≈

proposition-48 : _
proposition-48 = Bag.cong≈

proposition-49 : _
proposition-49 = Bag.comm≈

proposition-50 : _
proposition-50 = Bag.≈Respf♯

lemma-51 : _
lemma-51 = Bag.swapAut0≡0

lemma-52 : _
lemma-52 = Bag.punchOutZero≡fsuc

theorem-53 : _
theorem-53 = Bag.permuteInvariant

-- Section 5.1: Prelude
import Cubical.Structures.Set.CMon.SList as SList

definition-54 : _
definition-54 = SList.Membership*.よ

definition-55 : _
definition-55 = SList.Membership*.∈*Prop

definition-57 : _
definition-57 = ListMon.Head.Set.head

-- Section 5.2: Total orders
open import Cubical.Relation.Binary.Order
open import Cubical.Structures.Semilattices
open import Cubical.Structures.Set.CMon.SList.Sort.Base
open import Cubical.Structures.Set.CMon.SList.Sort.Sort
open import Cubical.Structures.Set.CMon.SList.Sort.Order
open import Cubical.Structures.Set.CMon.SList.Sort.Equiv

definition-58 : _
definition-58 = IsToset

proposition-59 : _
proposition-59 = Order→Sort.isDiscreteA

definition-60 : _
definition-60 = IsLoset

proposition-61 : _
proposition-61 = isTosetDecidable→Discrete

proposition-62 : _
proposition-62 = Toset.HasDecOrder≃HasDecLinearOrder

definition-63 : _
definition-63 = IsTotalMeetSemiLatticeStr

proposition-64 : _
proposition-64 = Toset.TotalMeetSemiLatticeStr≃TosetStr

proposition-64-a : _
proposition-64-a = Toset.HasDecOrder→HasDecTotalMeetSemiLattice

definition-65 : _
definition-65 = Sort→Order.least -- TODO: implement

-- Section 5.3.1: Section from Order
proposition-66 : _
proposition-66 = Sort↔Order.order→sort

-- Section 5.3.2: Section from Order
definition-67 : _
definition-67 = Sort→Order.least

proposition-68 : _
proposition-68 = Sort→Order.total≤

definition-70 : _
definition-70 = Sort.isSorted

proposition-71 : _
proposition-71 = Sort→Order.isSorted↔≤

definition-72 : _
definition-72 = Sort.isHeadLeast

proposition-73 : _
proposition-73 = Order→Sort.sortIsHeadLeast

proposition-74 : _
proposition-74 = Sort→Order.trans≤

-- Section 5.3.3: Embedding orders into sections
proposition-75 : _
proposition-75 = Sort↔Order.order→isHeadLeast→order

-- Section 5.3.4: Equivalence of order and sections
definition-77 : _
definition-77 = Sort.isTailSorted

definition-78 : _
definition-78 = ?

lemma-79 : _
lemma-79 = Order→Sort.uniqueSorted

proposition-80 : _
proposition-80 = Order→Sort.uniqueSort

proposition-81 : _
proposition-81 = Order→Sort.sortIsSorted

lemma-82 : _
lemma-82 = Sort↔Order.sort→order→sort

definition-83 : _
definition-83 = Sort↔Order.HasSortSectionAndIsDiscrete

theorem-84 : _
theorem-84 = Sort↔Order.sort≃order

corollary-85 : _
corollary-85 = Sort↔Order.sort≃linear-order

proposition-86 : _
proposition-86 = ?

---------------------------------
-- an exhaustive list of all modules:
import everything