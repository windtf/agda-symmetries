module types25pp where

open import Cubical.Relation.Binary.Order
open import Cubical.Structures.Prelude

open import Cubical.Structures.Sig
open import Cubical.Structures.Str
open import Cubical.Structures.Free
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq


-- Section 2.1 Algebras
definition-signature : _
definition-signature = Sig

definition-signature-functor : _
definition-signature-functor = sig

definition-structure : _
definition-structure = struct

definition-sig-homomorphism : _
definition-sig-homomorphism = structHom

-- Section 2.2 Free Algebras
definition-free-algebras : _
definition-free-algebras = Definition.Free

definition-universal-extension : _
definition-universal-extension = Definition.Free.ext

proposition-free-algebras-unique : _
proposition-free-algebras-unique = Definition.freeIso

definition-free-algebra-construction : _
definition-free-algebra-construction = Tree

proposition-free-algebra-construction-is : _
proposition-free-algebra-construction-is = trEquiv

-- Section 2.3 Equations
definition-equational-signature : _
definition-equational-signature = EqSig

definition-equational-signature-functor : _
definition-equational-signature-functor = eqsig

definition-system-of-equations : _
definition-system-of-equations = sysEq

definition-satisfaction : _
definition-satisfaction = _⊨_

-- Section 3.1: Lists
open import Cubical.Data.List
import Cubical.Structures.Set.Mon.List as ListMon

definition-lists : _
definition-lists = List

definition-list-concatenation : _
definition-list-concatenation = _++_

definition-list-universal-extension : _
definition-list-universal-extension = ListMon.Free._♯

proposition-ext-lifts-homomorphism : _
proposition-ext-lifts-homomorphism = ListMon.Free.♯IsMonHom

proposition-universal-property-for-list : _
proposition-universal-property-for-list = ListMon.listDef

-- Section 3.2: Arrays
import Cubical.Structures.Set.Mon.Array as ArrayMon

definition-arrays : _
definition-arrays = ArrayMon.Array

lemma-array-zero-is-id : _
lemma-array-zero-is-id = ArrayMon.eEta

definition-concatenation : _
definition-concatenation = ArrayMon._⊕_

proposition-arrays-monoid : _
proposition-arrays-monoid = ArrayMon.arraySat

lemma-array-eta-suc : _
lemma-array-eta-suc = ArrayMon.η+fsuc

lemma-array-split : _
lemma-array-split = ArrayMon.⊕Split

definition-array-universal-extension : _
definition-array-universal-extension = ArrayMon.Free._♯

proposition-array-ext-lifts-homomorphism : _
proposition-array-ext-lifts-homomorphism = ArrayMon.Free.♯IsMonHom

proposition-array-univ : _
proposition-array-univ = ArrayMon.arrayDef

-- Section 4.1: Free monoids quotiented by permutation relations
import Cubical.Structures.Set.CMon.QFreeMon as QFreeMon

definition-permutation-relation : _
definition-permutation-relation = QFreeMon.isPermRel

proposition-qfreemon-cmonoid : _
proposition-qfreemon-cmonoid = QFreeMon.QFreeMon.qFreeMonSat

definition-qfreemon-ext : _
definition-qfreemon-ext = QFreeMon.QFreeMon.IsFree._♯

proposition-qfreemon-univ : _
proposition-qfreemon-univ = QFreeMon.qFreeMonDef

-- Section 4.2: Lists quotiented by permutation relations
import Cubical.Structures.Set.CMon.PList as PList

definition-perm : _
definition-perm = PList.Perm

proposition-plist-resp-ext : _
proposition-plist-resp-ext = PList.permRespf♯

-- Section 4.3: Swap lists
import Cubical.Structures.Set.CMon.SList as SList

definition-slist : _
definition-slist = SList.SList

-- Section 4.4: Bag
import Cubical.Structures.Set.CMon.Bag as Bag

definition-bag : _
definition-bag = Bag.Bag

proposition-bag-equiv : _
proposition-bag-equiv = Bag.trans≈ -- TODO: × other properties of ≈

proposition-bag-cong : _
proposition-bag-cong = Bag.cong≈

proposition-bag-comm : _
proposition-bag-comm = Bag.comm≈

lemma-bag-tau : _
lemma-bag-tau = Bag.swapAut0≡0

lemma-bag-punch : _
lemma-bag-punch = Bag.punchOutZero≡fsuc

theorem-bag-perm-sat : _
theorem-bag-perm-sat = Bag.≈Respf♯

-- Section 5.1: Prelude
definition-length : _
definition-length = SList.Membership*.よ

definition-membership : _
definition-membership = SList.Membership*.∈*Prop

definition-head : _
definition-head = ListMon.Head.Set.head

-- Section 5.2: Total orders
open import Cubical.Relation.Binary.Order
open import Cubical.Structures.Semilattices
open import Cubical.Structures.Set.CMon.SList.Sort.Base
open import Cubical.Structures.Set.CMon.SList.Sort.Sort
open import Cubical.Structures.Set.CMon.SList.Sort.Order
open import Cubical.Structures.Set.CMon.SList.Sort.Equiv

definition-total-order : _
definition-total-order = IsToset

proposition-decidable-total-order : _
proposition-decidable-total-order = Order→Sort.isDiscreteA

definition-strict-total-order : _
definition-strict-total-order = IsLoset

proposition-decidable-strict-total-order : _
proposition-decidable-strict-total-order = isTosetDecidable→Discrete

proposition-decidable-strict-total-order-equiv : _
proposition-decidable-strict-total-order-equiv = Toset.HasDecOrder≃HasDecStrictOrder

definition-meet-semi-lattice : _
definition-meet-semi-lattice = IsTotalMeetSemiLatticeStr

proposition-discrete-meet-semi-lattice : _
proposition-discrete-meet-semi-lattice = Toset.disc→decLattice

proposition-total-order-meet-semi-lattice : _
proposition-total-order-meet-semi-lattice = Toset.TotalMeetSemiLatticeStr≃TosetStr

proposition-total-order-meet-semi-lattice-a : _
proposition-total-order-meet-semi-lattice-a = Toset.HasDecOrder→HasDecTotalMeetSemiLattice

definition-head-free-commutative-monoid : _
definition-head-free-commutative-monoid = Sort→Order.least -- TODO: implement

-- Section 5.3.1: Section from Order
proposition-sort-from-order : _
proposition-sort-from-order = Sort↔Order.order→sort

-- Section 5.3.2: Section from Order
definition-least : _
definition-least = Sort→Order.least

proposition-sort-almost-order : _
proposition-sort-almost-order = Sort→Order.total≤

definition-in-image : _
definition-in-image = Sort.isSorted

proposition-sort-to-order : _
proposition-sort-to-order = Sort→Order.isSorted↔≤

definition-head-least : _
definition-head-least = Sort.isHeadLeast

proposition-order-to-sort-head-least : _
proposition-order-to-sort-head-least = Order→Sort.sortIsHeadLeast

proposition-trans : _
proposition-trans = Sort→Order.trans≤

-- Section 5.3.3: Embedding orders into sections
proposition-o2s2o : _
proposition-o2s2o = Sort↔Order.order→isHeadLeast→order

-- Section 5.3.4: Equivalence of order and sections
definition-tail-sort : _
definition-tail-sort = Sort.isTailSorted

definition-is-sorted : _
definition-is-sorted = Order→Sort.IsSorted

lemma-is-sorted-unique : _
lemma-is-sorted-unique = Order→Sort.uniqueSorted

proposition-sort-uniq : _
proposition-sort-uniq = Order→Sort.uniqueSort

proposition-well-behave-sorts : _
proposition-well-behave-sorts = Order→Sort.sortIsSorted

lemma-s2o2s : _
lemma-s2o2s = Sort↔Order.sort→order→sort

definition-sorting-function : _
definition-sorting-function = Sort↔Order.HasSortSectionAndIsDiscrete

theorem-main : _
theorem-main = Sort↔Order.sort≃order

corollary-strict-order : _
corollary-strict-order = Sort↔Order.sort≃strict-order

corollary-lattice : _
corollary-lattice = Sort↔Order.sort≃lattice

---------------------------------
-- an exhaustive list of all modules:
import everything