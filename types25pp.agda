module types25pp where

open import Cubical.Relation.Binary.Order
open import Cubical.Structures.Prelude

open import Cubical.Structures.Sig

-- Definition 1 (Signature): A signature, denoted σ, is a (dependent) pair consisting of:
-- a set of operations, op : Set,
-- an arity function for each symbol, ar : op → Set.
definition-1 : _
definition-1 = Sig

-- Definition 3 (Signature functor Fσ : Set → Set):
-- X ↦ Σ(o : op) X^ar(o)
-- X → Y ↦ Σ(o : op) X^ar(o) (o,−◦ f) → Σ(o : op) Y^ar(o)
definition-3 : _
definition-3 = sig

open import Cubical.Structures.Str

-- Definition 5 (Structure): A σ-structure 𝔛 is an Fσ-algebra, that is, a pair consisting of:
-- a carrier set X, and
-- an algebra map αX : Fσ(X) → X.
definition-5 : _
definition-5 = struct

-- Definition 7 (Homomorphism): A homomorphism between two σ-structures 𝔛 and 𝔜 is a
-- morphism of Fσ-algebras, that is, a map f : X → Y such that the diagram commutes.
definition-7 : _
definition-7 = structHom

open import Cubical.Structures.Free
open import Cubical.Structures.Tree

-- Definition 9 (Free Algebras): A free σ-algebra construction consists of the following data:
-- a set F(X), for every set X,
-- a σ-structure on F(X), written as 𝔉(X),
-- a universal map ηX : X → F(X), for every X, such that,
-- for any σ-algebra 𝔜, the operation assigning to each homomorphism f : 𝔛 → 𝔜, the map
-- f ◦ ηX : X → Y (or, post-composition with ηX), is an equivalence.
definition-9 : _
definition-9 = Definition.Free

-- Definition 10 (Universal extension). The universal extension of a function f : X → Y to a
-- homomorphism out of the free σ-algebra on X is written as f ♯ : 𝔉(X) → 𝔜. It satisfies the
-- identities: f ♯ ◦ ηX = f , ηX ♯ = id𝔉(X) , and (g♯ ◦ f )♯ = g♯ ◦ f ♯.
definition-10 : _
definition-10 = Definition.Free.ext

-- Proposition 1. Suppose 𝔉(X) and 𝔊(X) are both free σ-algebras on X. Then 𝔉(X) ≃ 𝔊(X),
-- natural in X.
proposition-1 : _
proposition-1 = Definition.freeIso

-- Definition 11 (Construction of Free Algebras). The free σ-algebra on a type X is given by
-- the inductive type:
-- data Tree (X : U) : U where
-- leaf : X → Tree X
-- node : Fσ (Tree X) → Tree X
definition-11 : _
definition-11 = Tree

-- Proposition 2. (Tree(X),leaf) is the free σ-algebra on X.
proposition-2 : _
proposition-2 = trEquiv

open import Cubical.Structures.Eq

-- Definition 12 (Equational Signature). An equational signature, denoted ε, is a (dependent)
-- pair consisting of:
-- a set of names for equations, eq : Set,
-- an arity of free variables for each equation, fv : eq → Set.
definition-12 : _
definition-12 = EqSig

-- Definition 14 (Eq. Signature Functor Fε : Set → Set).
-- X ↦ Σ(e : eq) X^fv(e)
-- X → Y ↦ Σ(e : eq) X^ar(e) (e,−◦ f) → Σ(e : eq) Y^ar(e)
definition-14 : _
definition-14 = eqsig

-- Definition 15 (System of Equations). A system of equations over a signature (σ, ε), is a
-- pair of natural transformations: 𝓁, 𝓇 : Fε ⇒ 𝔉σ.
-- Concretely, for any set (of variables) V, this gives a pair of functions 𝓁V, 𝓇V : Fε(V) → 𝔉σ(V),
-- and naturality ensures correctness of renaming.
definition-15 : _
definition-15 = sysEq

-- Definition 17 (𝔛 ⊨ 𝑇). A σ-structure 𝔛 satisfies the system of equations 𝑇(σ, ε) if for every
-- set V, and every assignment ρ : V → X, ρ♯ is a (co)fork:
-- Fε(V) → 𝔉(V) → 𝔛
definition-17 : _
definition-17 = _⊨_

open import Cubical.Data.List

-- Definition 18 (Lists).
-- data List (A : U) : U where
-- [] : List A
-- _ :: _ : A → List A → List A
definition-18 : _
definition-18 = List

import Cubical.Structures.Set.Mon.List as ListMon

-- Proposition 3. (−)♯ lifts a function f : A → X to a monoid homomorphism f ♯ : List(A) → 𝔛.
proposition-3 : _
proposition-3 = ListMon.Free.♯-isMonHom

-- Proposition 4 (Universal property for List). (List(A), ηA) is the free monoid on A
proposition-4 : _
proposition-4 = ListMon.listDef

import Cubical.Structures.Set.Mon.Array as ArrayMon
import Cubical.Structures.Set.CMon.QFreeMon as QFreeMon
import Cubical.Structures.Set.CMon.PList as PList
import Cubical.Structures.Set.CMon.Bag as Bag
import Cubical.Structures.Set.CMon.SList.Sort.Sort
import Cubical.Structures.Set.CMon.SList as SList

-- Definition 19 (Arrays).
-- Array : U → U
-- Array A = Σ(n : Nat) (Fin n → A)
definition-19 : _
definition-19 = ArrayMon.Array

-- Lemma 1. Zero-length arrays (0, f) are contractible.
lemma-1 : _
lemma-1 = ArrayMon.e-eta

-- Definition 20 (Concatenation). The concatenation operation ++, is defined below, where
definition-20 : _
definition-20 = ArrayMon._⊕_

-- Proposition 5 (Array(A), ++) is a monoid.
proposition-5 : _
proposition-5 = ArrayMon.array-sat

-- Lemma 2 (Array cons). Any array (S(n), f) is equal to ηA(f(0)) ++ (n, f ∘ S).
lemma-2 : _
lemma-2 = ArrayMon.η+fsuc

-- Lemma 3 (Array split). For any array (S(n), f) and (m, g),
-- (n + m, (f ⊕ g) ∘ S) = (n, f ∘ S) ++ (m, g).
lemma-3 : _
lemma-3 = ArrayMon.⊕-split

-- Definition 21 (Universal extension). Given a monoid 𝔛, and a map f : A → X, we define
-- f ♯ : Array(A) → X, by induction on the length of the array:
-- f ♯ (0, g) = e
-- f ♯ (S(n), g) = f(g(0)) • f ♯ (n, g ∘ S)
definition-21 : _
definition-21 = ArrayMon.Free._♯

-- Proposition 6. (−)♯ lifts a function f : A → X to a monoid homomorphism f ♯ : Array(A) → 𝔛.
proposition-6 : _
proposition-6 = ArrayMon.Free.♯-isMonHom

-- Proposition 7 (Universal property for Array). (Array(A), ηA) is the free monoid on A
proposition-7 : _
proposition-7 = ArrayMon.arrayDef

-- Definition 22 (Permutation relation). A binary relation on a free monoid F(A) is a
-- permutation relation iff it:
-- is reflexive, symmetric, transitive (an equivalence),
-- is a congruence wrt •: a ≈ b → c ≈ d → a • c ≈ b • d,
-- is commutative: a • b ≈ b • a, and
-- respects (−)♯: ∀ f, a ≈ b → f ♯(a) = f ♯(b).
definition-22 : _
definition-22 = QFreeMon.isPermRel

-- Proposition 8. (𝔉(𝐴)≈, •, 𝑞(𝑒)) is a commutative monoid.
-- As a consequence, there is at most one permutation relation on 𝐹(𝐴).
-- For clarity, we will use c(−) to denote the extension operation of 𝐹(𝐴), and (−)♯ for the
-- extension operation of 𝐹(𝐴)≈.
proposition-8 : _
proposition-8 = QFreeMon.qFreeMonDef

-- Definition 23. Given a commutative monoid 𝔛 and a map 𝑓 : 𝐴 → 𝑋, we define
-- 𝑓♯ : 𝔉(𝐴)≈ → 𝔛 as follows: we first obtain b𝑓 : 𝔉(𝐴) → 𝔛 by universal property of 𝐹,
-- and lift it to 𝔉(𝐴)≈ → 𝔛, which is allowed since ≈ respects (−)♯.
definition-23 : _
definition-23 = QFreeMon.qFreeMonDef

-- Proposition 9 (Universal property for 𝔉(𝐴)≈). (𝔉(𝐴)≈, 𝜂𝐴 : 𝐴 𝜂𝐴
-- −−→ 𝔉(𝐴) 𝑞 −→ 𝔉(𝐴)≈) is the free comm. monoid on 𝐴.
proposition-9 : _
proposition-9 = QFreeMon.qFreeMonDef

-- Definition 24 (PList). PList A = List A Per
definition-24 : _
definition-24 = PList.plistFreeDef

-- Proposition 10. Let 𝔛 be a commutative monoid, and 𝑓 : 𝐴 → 𝑋. For 𝑥, 𝑦 : 𝐴 and
-- 𝑥𝑠, 𝑦𝑠 : PList(𝐴), 𝑓 ♯ (𝑥𝑠 ++ 𝑥 :: 𝑦 :: 𝑦𝑠) = 𝑓 ♯ (𝑥𝑠 ++ 𝑦 :: 𝑥 :: 𝑦𝑠). Hence, Perm respects (−)♯.
proposition-10 : _
proposition-10 = PList.isPermRelPerm

-- Definition 25 (Bag).
-- _≈_ : Array A → Array A → U
-- (n , f) ≈ (m , g) = Σ(𝜎 : Fin n ≃ Fin m) v = w ◦ 𝜎
-- Bag : U → U
-- Bag A = Array A _≈_
definition-25 : _
definition-25 = Bag.Bag

-- Proposition 11. ≈ is a equivalence relation.
proposition-11 : _
proposition-11 = Bag.isPermRelPerm

-- Proposition 12. ≈ is congruent wrt to ++
proposition-12 : _
proposition-12 = Bag.isPermRelPerm

-- Proposition 13. ≈ is commutative.
proposition-13 : _
proposition-13 = Bag.isPermRelPerm

-- Proposition 14. ≈ respects (−)♯ for arrays.
proposition-14 : _
proposition-14 = Bag.isPermRelPerm

-- Lemma 4. Given 𝜙 : FinS(n) ∼ −→ FinS(n) , there is a permutation 𝜏 : FinS(n) ∼ −→ FinS(n) such
-- that 𝜏(0) = 0, and 𝑓 ♯ (𝑆(𝑛), 𝑖 ◦ 𝜙) = 𝑓 ♯ (𝑆(𝑛), 𝑖 ◦ 𝜏).
lemma-4 : _
lemma-4 = Bag.swapAut

-- Lemma 5. Given 𝜏 : FinS(n) ∼ −→ FinS(n) where 𝜏(0) = 0, there is a 𝜓 : Finn ∼ −→ Finn such that
-- 𝜏 ◦ 𝑆 = 𝑆 ◦ 𝜓.
lemma-5 : _
lemma-5 = Bag.punchOutZero

-- Theorem 26 (Permutation invariance). For all 𝜙 : Finn ∼ −→ Finn, 𝑓 ♯ (𝑛, 𝑖) = 𝑓 ♯ (𝑛, 𝑖 ◦ 𝜙).
theorem-26 : _
theorem-26 = Bag.permuteInvariant

-- Definition 28 (∈). The membership predicate on a set 𝐴 for each element 𝑥 : 𝐴 is 𝑥 ∈ − ≔
-- よ𝐴(𝑥)♯ : F ( 𝐴) → hProp, where we define よ𝐴(𝑥) ≔ 𝜆𝑦. 𝑥 = 𝑦 : 𝐴 → hProp.
definition-28 : _
definition-28 = SList.Membership*.よ

-- Definition 29 (Any and All).
-- Any(𝑃) ≔ 𝑃♯ : F ( 𝐴) → (hProp, ⊥, ∨)
-- All(𝑃) ≔ 𝑃♯ : F ( 𝐴) → (hProp, ⊤, ∧)
definition-29 : _
definition-29 = SList.Membership*.∈*Prop

-- Definition 30 (head). The head homomorphism is defined as head ≔ inr♯ : L( 𝐴) → 1 + 𝐴,
-- where the monoid structure on 1 + 𝐴 has unit 𝑒 ≔ inl(★) : 1 + 𝐴, and multiplication picks the
-- leftmost element that is define
definition-30 : _
definition-30 = ListMon.Head.head

open import Cubical.Relation.Binary.Order
open import Cubical.Structures.Set.CMon.SList.Sort.Base
open import Cubical.Structures.Set.CMon.SList.Sort.Sort
open import Cubical.Structures.Set.CMon.SList.Sort.Order
open import Cubical.Structures.Set.CMon.SList.Sort.Equiv

-- Definition 31 (Total order). A total order on a set 𝐴 is a relation ≤ : 𝐴 → 𝐴 → hProp that
-- satisfies:
-- reflexivity: 𝑥 ≤ 𝑥,
-- transitivity: if 𝑥 ≤ 𝑦 and 𝑦 ≤ 𝑧, then 𝑥 ≤ 𝑧,
-- antisymmetry: if 𝑥 ≤ 𝑦 and 𝑦 ≤ 𝑥, then 𝑥 = 𝑦,
-- strong-connectedness: ∀𝑥, 𝑦, either 𝑥 ≤ 𝑦 or 𝑦 ≤ 𝑥.
definition-31 : _
definition-31 = IsToset

-- Proposition 17. Assume a decidable total order on 𝐴. There is a sort function 𝑠 : M ( 𝐴) →
-- L( 𝐴) which constructs a section to 𝑞 : L( 𝐴) ↠ M ( 𝐴)
proposition-17 : _
proposition-17 = Sort↔Order.order→sort

-- Definition 34. Given a section 𝑠, we define:
-- least(𝑥𝑠) ≔ head(𝑠(𝑥𝑠))
definition-34-a : _
definition-34-a = Sort→Order.least

-- 𝑥 ≼𝑠 𝑦 ≔ least(*𝑥, 𝑦+) = inr(𝑥)
definition-34-b : _
definition-34-b = Sort→Order._≤_

-- Proposition 18. ≼𝑠 is reflexive, antisymmetric, and total
proposition-18 : _
proposition-18 = Sort→Order.≤-isToset

-- Definition 35 (− ∈ im(𝑠)). The fiber of 𝑠 over 𝑥𝑠 : L( 𝐴) is given by fib𝑠 (𝑥𝑠) ≔
-- Í( 𝑦𝑠 : M ( 𝐴) ) 𝑠(𝑦𝑠) = 𝑥𝑠. The image of 𝑠 is given by im(𝑠) ≔ Í( 𝑥𝑠 : L ( 𝐴) ) ∥fib𝑠 (𝑥𝑠)∥−1.
-- Simplifying, we say that 𝑥𝑠 : L( 𝐴) is "in the image of 𝑠", or, 𝑥𝑠 ∈ im(𝑠), if there merely
-- exists a 𝑦𝑠 : M ( 𝐴) such that 𝑠(𝑦𝑠) = 𝑥𝑠.
definition-35 : _
definition-35 = Sort.is-sorted

-- Proposition 19. 𝑥 ≼𝑠 𝑦 iff [𝑥, 𝑦] ∈ im(𝑠)
proposition-19 : _
proposition-19 = Sort→Order.is-sorted↔≤

-- Definition 36 (im-cut). A section 𝑠 satisfies im-cut iff for all 𝑥, 𝑦, 𝑥𝑠:
-- 𝑦 ∈ 𝑥 :: 𝑥𝑠 ∧ 𝑥 :: 𝑥𝑠 ∈ im(𝑠) → [𝑥, 𝑦] ∈ im(𝑠) .
definition-36 : _
definition-36 = Sort.im-cut

-- Proposition 20. If 𝐴 has a total order ≤, insertion sort defined using ≤ satisfies im-cut.
proposition-20 : _
proposition-20 = Order→Sort.sort-im-cut

-- Proposition 21. If 𝑠 satisfies im-cut, ≼𝑠 is transitive.
proposition-21 : _
proposition-21 = Sort→Order.trans-≤

-- Proposition 22. Assume 𝐴 has a decidable total order ≤, we can construct a section 𝑠 that
-- satisfies im-cut, such that ≼𝑠 constructed from 𝑠 is equivalent to ≤
proposition-22 : _
proposition-22 = Sort↔Order.order→im-cut→order

-- Definition 37 (im-cons). A section 𝑠 satisfies im-cons iff for all 𝑥, 𝑥𝑠,
-- 𝑥 :: 𝑥𝑠 ∈ im(𝑠) → 𝑥𝑠 ∈ im(𝑠)
definition-37 : _
definition-37 = Sort.im-cons

-- Lemma 6. Given a total order ≤, for any 𝑥𝑠, 𝑦𝑠 : L( 𝐴), 𝑞(𝑥𝑠) = 𝑞(𝑦𝑠) ∧ Sorted≤ (𝑥𝑠) ∧
-- Sorted≤ (𝑦𝑠) → 𝑥𝑠 = 𝑦𝑠.
lemma-6 : _
lemma-6 = Order→Sort.unique-sorted-xs

-- Proposition 23. Given a total order ≤, if a section 𝑠 always produces sorted list, i.e.
-- ∀𝑥𝑠. Sorted≤ (𝑠(𝑥𝑠)), 𝑠 is equal to insertion sort by ≤.
proposition-23 : _
proposition-23 = Order→Sort.unique-sort

-- Proposition 24. Given a section 𝑠 that satisfies im-cut and im-cons, and ≼𝑠 the order
-- derived from 𝑠, then for all 𝑥𝑠 : M ( 𝐴), it holds that Sorted≼𝑠 (𝑠(𝑥𝑠)). Equivalently, for all lists
-- 𝑥𝑠 : L( 𝐴), it holds that 𝑥𝑠 ∈ im(𝑠) iff Sorted≼𝑠 (𝑥𝑠).
proposition-24 : _
proposition-24 = Order→Sort.sort-is-sorted

-- Lemma 7. Given a decidable total order ≤ on 𝐴, we can construct a section 𝑡≤ satisfying
-- im-cut and im-cons, such that, for the order ≼𝑠 derived from 𝑠, we have 𝑡≼𝑠 = 𝑠
lemma-7 : _
lemma-7 = Sort↔Order.sort→order→sort

-- Proposition 25. Assume 𝐴 has a decidable total order ≤, then 𝐴 has decidable equality.
proposition-25 : _
proposition-25 = Order→Sort.isDiscreteA

-- Definition 38 (Sorting function). A sorting function is a section 𝑠 : M ( 𝐴) → L( 𝐴) to the
-- canonical surjection 𝑞 : L( 𝐴) ↠ M ( 𝐴) satisfying two axioms:
-- im-cut: 𝑥 :: 𝑥𝑠 ∈ im(𝑠) ∧ 𝑦 ∈ 𝑥 :: 𝑥𝑠 → [𝑥, 𝑦] ∈ im(𝑠),
-- im-cons: 𝑥 :: 𝑥𝑠 ∈ im(𝑠) → 𝑥𝑠 ∈ im(𝑠).
definition-38 : _
definition-38 = Sort↔Order.HasSortSectionAndIsDiscrete

-- Theorem 39. Let DecTotOrd( 𝐴) be the set of decidable total orders on 𝐴, Sort( 𝐴) be the
-- set of sorting functions with carrier set 𝐴, and Discrete( 𝐴) be a predicate which states 𝐴 has
-- decidable equality. There is a map 𝑜2𝑠 : DecTotOrd( 𝐴) → Sort( 𝐴) × Discrete( 𝐴), which is an
-- equivalence.
theorem-39 : _
theorem-39 = Sort↔Order.sort≃order

---------------------------------
-- an exhaustive list of all modules:
import Everything
