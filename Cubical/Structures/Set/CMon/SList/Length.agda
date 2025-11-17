-- Taken from https://github.com/vikraman/generalised-species/
module Cubical.Structures.Set.CMon.SList.Length where

open import Cubical.Structures.Prelude

open import Cubical.Data.Empty as E
open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit

open import Cubical.Foundations.Univalence

open import Cubical.Functions.Embedding

open import Cubical.Structures.Set.CMon.SList.Base as SList

private
  variable
    ℓ : Level
    A B : Type ℓ
    ϕ : isSet A
    a x : A
    xs ys : SList A

disjNilCons : x ∷ xs ≡ [] -> ⊥
disjNilCons p = transport (λ i → fst (code (p i))) tt
  where code : SList A -> hProp ℓ-zero
        code = Elim.f (⊥ , isProp⊥)
          (λ _ _ -> Unit , isPropUnit)
          (λ _ _ _ _ -> Unit , isPropUnit)
          (λ _ -> isSetHProp)

disjConsNil : [] ≡ x ∷ xs -> ⊥
disjConsNil p = disjNilCons (sym p)

length : SList A → ℕ
length = Elim.f 0 (λ _ n -> suc n) (λ _ _ _ -> refl) (λ _ -> isSetℕ)

length-++ : (x y : SList A) → length (x ++ y) ≡ length x + length y
length-++ x y = ElimProp.f {B = λ xs → length (xs ++ y) ≡ length xs + length y}
  (isSetℕ _ _) refl (λ a p -> cong suc p) x

lenZeroOut : (xs : SList A) → length xs ≡ 0 → [] ≡ xs
lenZeroOut = ElimProp.f (isPropΠ λ _ → trunc _ _)
  (λ _ -> refl)
  (λ x p q -> E.rec (snotz q))

lenZeroEqv : (xs : SList A) → (length xs ≡ 0) ≃ ([] ≡ xs)
lenZeroEqv xs = propBiimpl→Equiv (isSetℕ _ _) (trunc _ _) (lenZeroOut xs) (λ p i → length (p (~ i)))

isSingPred : SList A → A → Type _
isSingPred xs a = [ a ] ≡ xs

isSingPredProp : (xs : SList A) (z : A) → isProp (isSingPred xs z)
isSingPredProp xs a = trunc [ a ] xs

isSing : SList A → Type _
isSing xs = Σ _ (isSingPred xs)

Sing : Type ℓ → Type ℓ
Sing A = Σ (SList A) isSing

[_]-isSing : (a : A) → isSing [ a ]
[ a ]-isSing = a , refl

sing=isProp : ∀ {x y : A} → isProp ([ x ] ≡ [ y ])
sing=isProp {x = x} {y = y} = trunc [ x ] [ y ]

sing=-in : ∀ {x y : A} → x ≡ y → [ x ] ≡ [ y ]
sing=-in p i = [ p i ]

sing=isContr : ∀ {x y : A} → x ≡ y → isContr ([ x ] ≡ [ y ])
sing=isContr p = sing=-in p , sing=isProp (sing=-in p)

lenOneDown : (x : A) (xs : SList A) → length (x ∷ xs) ≡ 1 → [] ≡ xs
lenOneDown x xs p = lenZeroOut xs (injSuc p)

lenOneCons : (x : A) (xs : SList A) → length (x ∷ xs) ≡ 1 → isSing (x ∷ xs)
lenOneCons x xs p =
  let q = lenOneDown x xs p
  in transport (λ i → isSing (x ∷ q i)) [ x ]-isSing

lenTwo-⊥ : (x y : A) (xs : SList A) → (length (y ∷ x ∷ xs) ≡ 1) ≃ ⊥
lenTwo-⊥ x y xs = (λ p → E.rec (snotz (injSuc p))) , record { equiv-proof = E.elim }

isContrlenTwo-⊥→X : (X : Type ℓ) (x y : A) (xs : SList A) → isContr (length (y ∷ x ∷ xs) ≡ 1 → X)
isContrlenTwo-⊥→X X x y xs = subst (λ Z → isContr (Z → X)) (sym (ua (lenTwo-⊥ x y xs))) (isContr⊥→A {A = X})

lenOneSwap : {A : Type ℓ} (x y : A) (xs : SList A)
            → PathP (λ i → length (SList.swap x y xs i) ≡ 1 → isSing (SList.swap x y xs i))
                    (λ p → lenOneCons x (y ∷ xs) p)
                    (λ p → lenOneCons y (x ∷ xs) p)
lenOneSwap {A = A} x y xs =
  transport (sym (PathP≡Path (λ i → length (SList.swap x y xs i) ≡ 1 → isSing (SList.swap x y xs i)) _ _))
            (isContr→isProp (isContrlenTwo-⊥→X _ x y xs) _ _)

lenOne : Type ℓ → Type _
lenOne A = Σ (SList A) (λ xs → length xs ≡ 1)

module _ {ϕ : isSet A} where

  isSingSet : (xs : SList A) → isSet (isSing xs)
  isSingSet xs = isSetΣ ϕ λ x → isProp→isSet (isSingPredProp xs x)

  lenOneOut : (xs : SList A) → length xs ≡ 1 → isSing xs
  lenOneOut = Elim.f (λ p → E.rec (znots p))
    (λ x {xs} f p → lenOneCons x xs p)
    (λ x y {xs} f → lenOneSwap x y xs)
    λ xs → isSetΠ (λ p → isSingSet xs)

  head : lenOne A → A
  head (xs , p) = lenOneOut xs p .fst

  -- not definitional due to lack of regularity
  head-β : (a : A) → head ([ a ] , refl) ≡ a
  head-β a i = transp (λ _ → A) i a

  lenOnePath : (a b : A) → Type _
  lenOnePath a b = Path (lenOne A) ([ a ] , refl) ([ b ] , refl)

  lenOnePath-in : {a b : A} → [ a ] ≡ [ b ] → lenOnePath a b
  lenOnePath-in = Σ≡Prop (λ xs → isSetℕ _ _)

  [-]-inj : {a b : A} → [ a ] ≡ [ b ] → a ≡ b
  [-]-inj {a = a} {b = b} p = aux (lenOnePath-in p)
    where aux : lenOnePath a b → a ≡ b
          aux p = sym (head-β a) ∙ cong head p ∙ head-β b

  isSingProp : (xs : SList A) → isProp (isSing xs)
  isSingProp xs (a , ψ) (b , ξ) = Σ≡Prop (isSingPredProp xs) ([-]-inj (ψ ∙ sym ξ))

  lenOneEqv : (xs : SList A) → (length xs ≡ 1) ≃ (isSing xs)
  lenOneEqv xs = propBiimpl→Equiv (isSetℕ _ _) (isSingProp xs) (lenOneOut xs) (λ χ → cong length (sym (χ .snd)))

  lenOne-set-eqv : lenOne A ≃ A
  lenOne-set-eqv = isoToEquiv (iso head g head-β g-f)
    where g : A → lenOne A
          g a = [ a ] , refl
          g-f : (as : lenOne A) → g (head as) ≡ as
          g-f (as , ϕ) =
            let (a , ψ) = lenOneOut as ϕ
            in Σ≡Prop (λ xs → isSetℕ _ _) {u = ([ a ] , refl)} {v = (as , ϕ)} ψ

  sing-set-eqv : Sing A ≃ A
  sing-set-eqv = isoToEquiv (iso f (λ a → [ a ] , [ a ]-isSing) (λ _ → refl) ret)
    where f : Sing A → A
          f s = s .snd .fst
          ret : (s : Sing A) → ([ f s ] , f s , refl) ≡ s
          ret (s , ψ) = Σ≡Prop isSingProp (ψ .snd)
