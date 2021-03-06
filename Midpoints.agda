{-# OPTIONS --safe --without-K #-}

module Midpoints where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Function.Base
open import Data.Maybe
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Level renaming (suc to lsuc)

-- Open dyadic interval

data D : Set where
  mid : D
  l : D → D
  r : D → D

-- Halving and midpoint operation
infix 10 _/2
_/2 : D → D
mid /2 = mid
l x /2 = l (r x)
r x /2 = r (l x)

infix 8 _⊕_
_⊕_ : D → D → D
mid ⊕ x = x /2
l x ⊕ mid = l x /2
l x ⊕ l y = l (x ⊕ y)
l x ⊕ r y = (x ⊕ y) /2
r x ⊕ mid = r x /2
r x ⊕ l y = (x ⊕ y) /2
r x ⊕ r y = r (x ⊕ y)

-- Midpoint properties for D

l-eq-lem : ∀ x y → l x ≡ l y → x ≡ y
l-eq-lem x .x refl = refl

⊕-idem : (x : D) → x ≡ x ⊕ x
⊕-idem mid = refl
⊕-idem (l x) = cong l (⊕-idem x)
⊕-idem (r x) = cong r (⊕-idem x)

⊕-mid : (x : D) → x /2 ≡ x ⊕ mid
⊕-mid mid = refl
⊕-mid (l x) = refl
⊕-mid (r x) = refl

/2-hom : (x y : D) → (x ⊕ y) /2 ≡ (x /2) ⊕ (y /2)
/2-hom mid mid = refl
/2-hom mid (l y) = refl
/2-hom mid (r y) = refl
/2-hom (l x) mid = refl
/2-hom (l x) (l y) = refl
/2-hom (l x) (r y) = refl
/2-hom (r x) mid = refl
/2-hom (r x) (l y) = refl
/2-hom (r x) (r y) = refl

⊕-comm : (x y : D) → x ⊕ y ≡ y ⊕ x
⊕-comm mid mid = refl
⊕-comm mid (l y) = refl
⊕-comm mid (r y) = refl
⊕-comm (l x) mid = refl
⊕-comm (l x) (l y) = cong l (⊕-comm x y)
⊕-comm (l x) (r y) = cong _/2 (⊕-comm x y)
⊕-comm (r x) mid = refl
⊕-comm (r x) (l y) = cong _/2 (⊕-comm x y)
⊕-comm (r x) (r y) = cong r (⊕-comm x y)

⊕-switch-l : (a b : D) → l a ⊕ (b /2) ≡ (a /2) ⊕ l b
⊕-switch-l mid mid = refl
⊕-switch-l mid (l b) = refl
⊕-switch-l mid (r b) = refl
⊕-switch-l (l a) mid = refl
⊕-switch-l (l a) (l b) = refl
⊕-switch-l (l a) (r b) = refl
⊕-switch-l (r a) mid = refl
⊕-switch-l (r a) (l b) = refl
⊕-switch-l (r a) (r b) = refl

⊕-switch-r : (a b : D) → r a ⊕ (b /2) ≡ (a /2) ⊕ r b
⊕-switch-r mid mid = refl
⊕-switch-r mid (l b) = refl
⊕-switch-r mid (r b) = refl
⊕-switch-r (l a) mid = refl
⊕-switch-r (l a) (l b) = refl
⊕-switch-r (l a) (r b) = refl
⊕-switch-r (r a) mid = refl
⊕-switch-r (r a) (l b) = refl
⊕-switch-r (r a) (r b) = refl

⊕-lem-l : (a b : D) → l a ⊕ (b /2) ≡ ((a ⊕ b) /2) ⊕ (l (a ⊕ b))
⊕-lem-l mid mid = refl
⊕-lem-l mid (l b) = cong (l ∘ r ∘ l) (⊕-idem b)
⊕-lem-l mid (r b) = cong (l ∘ r ∘ r) (⊕-idem b)
⊕-lem-l (l a) mid = cong (l ∘ r ∘ l) (⊕-idem a)
⊕-lem-l (l a) (l b) = cong (l ∘ _/2) (⊕-idem (a ⊕ b))
⊕-lem-l (l a) (r b) with (a ⊕ b)
... | mid = refl
... | l p = cong (l ∘ r ∘ l) (⊕-idem p)
... | r p = cong (l ∘ r ∘ r) (⊕-idem p)
⊕-lem-l (r a) mid = cong (l ∘ r ∘ r) (⊕-idem a)
⊕-lem-l (r a) (l b) with (a ⊕ b)
... | mid = refl
... | l p = cong (l ∘ r ∘ l) (⊕-idem p)
... | r p = cong (l ∘ r ∘ r) (⊕-idem p)
⊕-lem-l (r a) (r b) = cong (_/2 ∘ _/2) (⊕-idem (a ⊕ b))

⊕-lem-l-eq : (a b c d : D) → a ⊕ b ≡ c ⊕ d → l a ⊕ (b /2) ≡ (l c) ⊕ (d /2)
⊕-lem-l-eq a b c d p =
  (l a ⊕ (b /2)) ≡⟨ ⊕-lem-l a b ⟩
  ((a ⊕ b) /2) ⊕ l (a ⊕ b) ≡⟨ cong₂ (λ x y → (x /2) ⊕ l y) p p ⟩
  ((c ⊕ d) /2) ⊕ l (c ⊕ d) ≡˘⟨ ⊕-lem-l c d ⟩
  l c ⊕ (d /2) ∎

⊕-lem-r : (a b : D) → r a ⊕ (b /2) ≡ ((a ⊕ b) /2) ⊕ (r (a ⊕ b))
⊕-lem-r mid mid = refl
⊕-lem-r mid (l b) = cong (r ∘ l ∘ l) (⊕-idem b)
⊕-lem-r mid (r b) = cong (r ∘ l ∘ r) (⊕-idem b)
⊕-lem-r (l a) mid = cong (r ∘ l ∘ l) (⊕-idem a)
⊕-lem-r (l a) (l b) = cong (_/2 ∘ _/2) (⊕-idem (a ⊕ b))
⊕-lem-r (l a) (r b) with (a ⊕ b)
... | mid = refl
... | l p = cong (r ∘ l ∘ l) (⊕-idem p)
... | r p = cong (r ∘ l ∘ r) (⊕-idem p)
⊕-lem-r (r a) mid = cong (r ∘ l ∘ r) (⊕-idem a)
⊕-lem-r (r a) (l b) with (a ⊕ b)
... | mid = refl
... | l p = cong (r ∘ l ∘ l) (⊕-idem p)
... | r p = cong (r ∘ l ∘ r) (⊕-idem p)
⊕-lem-r (r a) (r b) = cong (r ∘ _/2) (⊕-idem (a ⊕ b))

⊕-lem-r-eq : (a b c d : D) → a ⊕ b ≡ c ⊕ d → r a ⊕ (b /2) ≡ (r c) ⊕ (d /2)
⊕-lem-r-eq a b c d p =
  (r a ⊕ (b /2)) ≡⟨ ⊕-lem-r a b ⟩
  ((a ⊕ b) /2) ⊕ r (a ⊕ b) ≡⟨ cong₂ (λ x y → (x /2) ⊕ r y) p p ⟩
  ((c ⊕ d) /2) ⊕ r (c ⊕ d) ≡˘⟨ ⊕-lem-r c d ⟩
  r c ⊕ (d /2) ∎

assocl : ∀ x y z → l x ⊕ (y ⊕ z) ≡ (x ⊕ y) ⊕ l z
assocr : ∀ x y z → r x ⊕ (y ⊕ z) ≡ (x ⊕ y) ⊕ r z

assocl mid mid mid = refl
assocl mid mid (l z) = refl
assocl mid mid (r z) = refl
assocl mid (l y) mid = refl
assocl mid (l y) (l z) = refl
assocl mid (l y) (r z) with y ⊕ z
... | mid = refl
... | l a = refl
... | r a = refl
assocl mid (r y) mid = refl
assocl mid (r y) (l z) with y ⊕ z
... | mid = refl
... | l a = refl
... | r a = refl
assocl mid (r y) (r z) = refl
assocl (l x) mid mid = refl
assocl (l x) mid (l z) = refl
assocl (l x) mid (r z) = refl
assocl (l x) (l y) mid = cong l (⊕-mid (x ⊕ y))
assocl (l x) (l y) (l z) = cong l (assocl x y z)
assocl (l x) (l y) (r z) = ⊕-lem-l-eq (l x) (y ⊕ z) (x ⊕ y) (l z) (assocl x y z)
assocl (l x) (r y) mid with x ⊕ y
... | mid = refl
... | l a = refl
... | r a = refl
assocl (l x) (r y) (l z) =
  l (l x) ⊕ (y ⊕ z) /2 ≡⟨ ⊕-lem-l-eq (l x) (y ⊕ z) (x ⊕ y) (l z) (assocl x y z) ⟩
  l (x ⊕ y) ⊕ l z /2 ≡⟨ ⊕-switch-l (x ⊕ y) (l z) ⟩
  (x ⊕ y) /2 ⊕ l (l z) ∎
assocl (l x) (r y) (r z) =
  (l x ⊕ (y ⊕ z)) /2 ≡⟨ cong _/2 (assocl x y z) ⟩
  ((x ⊕ y) ⊕ l z) /2 ≡⟨ /2-hom (x ⊕ y) (l z) ⟩
  ((x ⊕ y) /2 ⊕ l (r z)) ∎
assocl (r x) mid mid = refl
assocl (r x) mid (l z) = refl
assocl (r x) mid (r z) = refl
assocl (r x) (l y) mid with x ⊕ y
... | mid = refl
... | l a = refl
... | r a = refl
assocl (r x) (l y) (l z) =
  l x /2 ⊕ l (y ⊕ z) ≡˘⟨ ⊕-switch-l (l x) (y ⊕ z) ⟩
  l (l x) ⊕ (y ⊕ z) /2 ≡⟨ ⊕-lem-l-eq (l x) (y ⊕ z) (x ⊕ y) (l z) (assocl x y z) ⟩
  l (x ⊕ y) ⊕ l z /2 ≡⟨ ⊕-switch-l (x ⊕ y) (l z) ⟩
  (x ⊕ y) /2 ⊕ l (l z) ∎
assocl (r x) (l y) (r z) =
  l x /2 ⊕ (y ⊕ z) /2 ≡˘⟨ /2-hom (l x) (y ⊕ z) ⟩
  (l x ⊕ (y ⊕ z)) /2 ≡⟨ cong _/2 (assocl x y z) ⟩
  ((x ⊕ y) ⊕ l z) /2 ≡⟨ /2-hom (x ⊕ y) (l z) ⟩
  (x ⊕ y) /2 ⊕ l z /2 ∎
assocl (r x) (r y) mid = cong _/2 (⊕-mid (x ⊕ y))
assocl (r x) (r y) (l z) =
  l (r x) ⊕ (y ⊕ z) /2 ≡˘⟨ /2-hom (l x) (y ⊕ z) ⟩
  (l x ⊕ (y ⊕ z)) /2 ≡⟨ cong _/2 (assocl x y z) ⟩
  ((x ⊕ y) ⊕ l z) /2 ∎
assocl (r x) (r y) (r z) = cong _/2 (assocr x y z)

assocr mid mid mid = refl
assocr mid mid (l z) = refl
assocr mid mid (r z) = refl
assocr mid (l y) mid = refl
assocr mid (l y) (l z) = refl
assocr mid (l y) (r z) with y ⊕ z
... | mid = refl
... | l a = refl
... | r a = refl
assocr mid (r y) mid = refl
assocr mid (r y) (l z) with y ⊕ z
... | mid = refl
... | l a = refl
... | r a = refl
assocr mid (r y) (r z) = refl
assocr (l x) mid mid = refl
assocr (l x) mid (l z) = refl
assocr (l x) mid (r z) = refl
assocr (l x) (l y) mid = cong _/2 (⊕-mid (x ⊕ y))
assocr (l x) (l y) (l z) = cong _/2 (assocl x y z)
assocr (l x) (l y) (r z) =
  r x /2 ⊕ (y ⊕ z) /2 ≡˘⟨ /2-hom (r x) (y ⊕ z) ⟩
  (r x ⊕ (y ⊕ z)) /2 ≡⟨ cong _/2 (assocr x y z) ⟩
  ((x ⊕ y) ⊕ r z) /2 ∎
assocr (l x) (r y) mid with x ⊕ y
... | mid = refl
... | l a = refl
... | r a = refl
assocr (l x) (r y) (l z) =
  r x /2 ⊕ (y ⊕ z) /2 ≡˘⟨ /2-hom (r x) (y ⊕ z) ⟩
  (r x ⊕ (y ⊕ z)) /2 ≡⟨ cong _/2 (assocr x y z) ⟩
  ((x ⊕ y) ⊕ r z) /2 ≡⟨ /2-hom (x ⊕ y) (r z) ⟩
  (x ⊕ y) /2 ⊕ r z /2 ∎
assocr (l x) (r y) (r z) =
  r x /2 ⊕ r (y ⊕ z) ≡˘⟨ ⊕-switch-r (r x) (y ⊕ z) ⟩
  r (r x) ⊕ (y ⊕ z) /2 ≡⟨ ⊕-lem-r-eq (r x) (y ⊕ z) (x ⊕ y) (r z) (assocr x y z) ⟩
  r (x ⊕ y) ⊕ r z /2 ≡⟨ ⊕-switch-r (x ⊕ y) (r z) ⟩
  (x ⊕ y) /2 ⊕ r (r z) ∎
assocr (r x) mid mid = refl
assocr (r x) mid (l z) = refl
assocr (r x) mid (r z) = refl
assocr (r x) (l y) mid with x ⊕ y
... | mid = refl
... | l a = refl
... | r a = refl
assocr (r x) (l y) (l z) =
  (r x ⊕ (y ⊕ z)) /2 ≡⟨ cong _/2 (assocr x y z) ⟩
  ((x ⊕ y) ⊕ r z) /2 ≡⟨ /2-hom (x ⊕ y) (r z) ⟩
  (x ⊕ y) /2 ⊕ r z /2 ∎
assocr (r x) (l y) (r z) =
  r (r x) ⊕ (y ⊕ z) /2 ≡⟨ ⊕-lem-r-eq (r x) (y ⊕ z) (x ⊕ y) (r z) (assocr x y z) ⟩
  r (x ⊕ y) ⊕ r z /2 ≡⟨ ⊕-switch-r (x ⊕ y) (r z) ⟩
  (x ⊕ y) /2 ⊕ r (r z) ∎
assocr (r x) (r y) mid with x ⊕ y
... | mid = refl
... | l a = refl
... | r a = refl
assocr (r x) (r y) (l z) = ⊕-lem-r-eq (r x) (y ⊕ z) (x ⊕ y) (r z) (assocr x y z)
assocr (r x) (r y) (r z) = cong r (assocr x y z)

⊕-trans : ∀ a b c d → (a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)
⊕-trans a b c d = l-eq-lem ((a ⊕ b) ⊕ (c ⊕ d)) ((a ⊕ c) ⊕ (b ⊕ d)) γ
  where
    δ : (a ⊕ b) ⊕ l c ≡ (a ⊕ c) ⊕ l b
    δ = (a ⊕ b) ⊕ l c ≡˘⟨ assocl a b c ⟩
        l a ⊕ (b ⊕ c) ≡⟨ cong (l a ⊕_) (⊕-comm b c) ⟩
        l a ⊕ (c ⊕ b) ≡⟨ assocl a c b ⟩
        (a ⊕ c) ⊕ l b ∎

    γ : l ((a ⊕ b) ⊕ (c ⊕ d)) ≡ l ((a ⊕ c) ⊕ (b ⊕ d))
    γ = l ((a ⊕ b) ⊕ (c ⊕ d)) ≡⟨⟩
        l (a ⊕ b) ⊕ (l c ⊕ l d) ≡⟨ assocl (a ⊕ b) (l c) (l d) ⟩
        ((a ⊕ b) ⊕ l c) ⊕ l (l d) ≡⟨ cong (_⊕ l (l d)) δ ⟩
        ((a ⊕ c) ⊕ l b) ⊕ l (l d) ≡˘⟨ assocl (a ⊕ c) (l b) (l d) ⟩
        l (a ⊕ c) ⊕ (l b ⊕ l d) ≡⟨⟩
        l ((a ⊕ c) ⊕ (b ⊕ d)) ∎

-- To define the closed dyadics we do the following:
-- Take the open dyadics which look like
-- (------|------)
-- And we carve off the outer parts to get
-- ---[---|---]---

inSubinterval : D -> Set
inSubinterval mid = ⊤
inSubinterval (l mid) = ⊤
inSubinterval (l (l x)) = ⊥
inSubinterval (l (r x)) = ⊤
inSubinterval (r mid) = ⊤
inSubinterval (r (r x)) = ⊥
inSubinterval (r (l x)) = ⊤

inSubintervalHalfLem : ∀ x → inSubinterval (x /2)
inSubintervalHalfLem mid = tt
inSubintervalHalfLem (l x) = tt
inSubintervalHalfLem (r x) = tt

inSubintervalLemma : ∀ x y → inSubinterval x → inSubinterval y → inSubinterval (x ⊕ y)
inSubintervalLemma mid y pf1 pf2 = inSubintervalHalfLem y
inSubintervalLemma (l x) mid pf1 pf2 = tt
inSubintervalLemma (l mid) (l mid) pf1 pf2 = tt
inSubintervalLemma (l mid) (l (r y)) pf1 pf2 = tt
inSubintervalLemma (l (r x)) (l mid) pf1 pf2 = tt
inSubintervalLemma (l (r x)) (l (r y)) pf1 pf2 = tt
inSubintervalLemma (l x) (r y) pf1 pf2 = inSubintervalHalfLem (x ⊕ y)
inSubintervalLemma (r x) mid pf1 pf2 = tt
inSubintervalLemma (r x) (l y) pf1 pf2 = inSubintervalHalfLem (x ⊕ y)
inSubintervalLemma (r mid) (r mid) pf1 pf2 = tt
inSubintervalLemma (r mid) (r (l y)) pf1 pf2 = tt
inSubintervalLemma (r (l x)) (r mid) pf1 pf2 = tt
inSubintervalLemma (r (l x)) (r (l y)) pf1 pf2 = tt

-- D′ is the closed dyadics, i.e. all the dyadics that are in the subinterval
D′ : Set
D′ = Σ D inSubinterval

-- Midpoint respects being in the subinterval
infix 8 _⊕′_
_⊕′_ : D′ → D′ → D′
(x , xpf) ⊕′ (y , ypf) = (x ⊕ y) , (inSubintervalLemma x y xpf ypf)

-- being in the subinterval is a prop
inSubintervalProp : ∀ x → (pf1 pf2 : inSubinterval x) → pf1 ≡ pf2
inSubintervalProp mid pf1 pf2 = refl
inSubintervalProp (l mid) pf1 pf2 = refl
inSubintervalProp (l (r x)) pf1 pf2 = refl
inSubintervalProp (r mid) pf1 pf2 = refl
inSubintervalProp (r (l x)) pf1 pf2 = refl

-- And so equality between elements of D′ is determined by equality of the underlying elements of D
primeEqLemma : (x y : D′) → proj₁ x ≡ proj₁ y → x ≡ y
primeEqLemma (x , xpf) (.x , ypf) refl rewrite inSubintervalProp x xpf ypf = refl

-- Transport the midpoint properties
⊕′-comm : ∀ x y → x ⊕′ y ≡ y ⊕′ x
⊕′-comm x y = primeEqLemma (x ⊕′ y) (y ⊕′ x) (⊕-comm (proj₁ x) (proj₁ y))

⊕′-idem : ∀ x → x ≡ x ⊕′ x
⊕′-idem x = primeEqLemma x (x ⊕′ x) (⊕-idem (proj₁ x))

⊕′-trans : ∀ a b c d → (a ⊕′ b) ⊕′ (c ⊕′ d) ≡ (a ⊕′ c) ⊕′ (b ⊕′ d)
⊕′-trans a b c d = primeEqLemma ((a ⊕′ b) ⊕′ (c ⊕′ d)) ((a ⊕′ c) ⊕′ (b ⊕′ d)) (⊕-trans (proj₁ a) (proj₁ b) (proj₁ c) (proj₁ d))

-- D′ has actual endpoints
end-left : D′
end-left = (l mid) , tt

end-right : D′
end-right = (r mid) , tt

-- Define what a bipointed midpoint algebra is

record BiPointMidpointAlgebra (a : Level) : Set (lsuc a) where
  field
    CarrierM : Set a
    mp : CarrierM → CarrierM → CarrierM
    p1 p2 : CarrierM
    bpm-idem : ∀ x → x ≡ mp x x
    bpm-comm : ∀ x y → mp x y ≡ mp y x
    bpm-trans : ∀ a b c d → mp (mp a b) (mp c d) ≡ mp (mp a c) (mp b d)

open BiPointMidpointAlgebra

D′-is-bpm : BiPointMidpointAlgebra 0ℓ
D′-is-bpm .CarrierM = D′
D′-is-bpm .mp = _⊕′_
D′-is-bpm .p1 = end-left
D′-is-bpm .p2 = end-right
D′-is-bpm .bpm-idem = ⊕′-idem
D′-is-bpm .bpm-comm = ⊕′-comm
D′-is-bpm .bpm-trans = ⊕′-trans

-- Store the data for a binary system in a record
record BinarySystem (a : Level) : Set (lsuc a) where
  field
    Carrier : Set a
    el er : Carrier
    left right : Carrier → Carrier
    leftel : el ≡ left el
    righter : er ≡ right er
    centereq : right el ≡ left er

open BinarySystem

-- Any bipointed midpoint algebra is a binary system

bpm-is-bs : ∀ {a} → BiPointMidpointAlgebra a → BinarySystem a
bpm-is-bs A .Carrier = CarrierM A
bpm-is-bs A .el = p1 A
bpm-is-bs A .er = p2 A
bpm-is-bs A .left = mp A (p1 A)
bpm-is-bs A .right = mp A (p2 A)
bpm-is-bs A .leftel = bpm-idem A (p1 A)
bpm-is-bs A .righter = bpm-idem A (p2 A)
bpm-is-bs A .centereq = bpm-comm A (p2 A) (p1 A)

-- So D′ is a binary system
D′-is-bs : BinarySystem 0ℓ
D′-is-bs = bpm-is-bs D′-is-bpm

-- We can also define midpoint homomorphisms

record BiPointMidpointHom {a b} (A : BiPointMidpointAlgebra a) (B : BiPointMidpointAlgebra b) : Set (lsuc (a ⊔ b)) where
  field
    funcM : CarrierM A → CarrierM B
    p1-hom : funcM (p1 A) ≡ p1 B
    p2-hom : funcM (p2 A) ≡ p2 B
    mp-hom : ∀ x y → funcM (mp A x y) ≡ mp B (funcM x) (funcM y)

open BiPointMidpointHom

-- Also store homomorphisms as a record
record BinarySystemHom {a b} (A : BinarySystem a) (B : BinarySystem b) : Set (lsuc (a ⊔ b)) where
  field
    func : Carrier A → Carrier B
    left-end-hom : func (el A) ≡ el B
    right-end-hom : func (er A) ≡ er B
    left-hom : ∀ x → func (left A x) ≡ left B (func x)
    right-hom : ∀ x → func (right A x) ≡ right B (func x)

open BinarySystemHom

-- Further have a record for structures "like" D which have a central object and left and right maps
record OpenBinarySystem (a : Level) : Set (lsuc a) where
  field
    CarrierO : Set a
    c : CarrierO
    leftO rightO : CarrierO → CarrierO

open OpenBinarySystem

-- D is the obvious example of this
D-is-obs : OpenBinarySystem 0ℓ
D-is-obs .CarrierO = D
D-is-obs .c = mid
D-is-obs .leftO = l
D-is-obs .rightO = r

-- We also have maps between these
record OpenBinarySystemHom {a b} (A : OpenBinarySystem a) (B : OpenBinarySystem b) : Set (lsuc (a ⊔ b)) where
  field
    funcO : CarrierO A → CarrierO B
    c-hom : funcO (c A) ≡ c B
    left-homO : ∀ x → funcO (leftO A x) ≡ leftO B (funcO x)
    right-homO : ∀ x → funcO (rightO A x) ≡ rightO B (funcO x)

open OpenBinarySystemHom

-- Any binary system is an open-binary-system
bs-is-obs : ∀ {b} → BinarySystem b → OpenBinarySystem b
bs-is-obs B .CarrierO = Carrier B
bs-is-obs B .c = right B (el B)
bs-is-obs B .leftO = left B
bs-is-obs B .rightO = right B

-- We can embed D into any binary system
embedD : ∀ {b} → (B : OpenBinarySystem b) → D → CarrierO B
embedD B mid = c B
embedD B (l x) = leftO B (embedD B x)
embedD B (r x) = rightO B (embedD B x)

-- And show this is a homomorphism
embedD-is-hom : ∀ {b} → (B : OpenBinarySystem b) → OpenBinarySystemHom D-is-obs B
embedD-is-hom B .funcO = embedD B
embedD-is-hom B .c-hom = refl
embedD-is-hom B .left-homO x = refl
embedD-is-hom B .right-homO x = refl

-- And further that D is the initial open binary system
at-most-one-open-hom : ∀ {b} → (B : OpenBinarySystem b) → (f g : OpenBinarySystemHom D-is-obs B) → ∀ x → funcO f x ≡ funcO g x
at-most-one-open-hom B f g mid =
  funcO f mid ≡⟨ c-hom f ⟩
  c B ≡˘⟨ c-hom g ⟩
  funcO g mid ∎
at-most-one-open-hom B f g (l x) =
  funcO f (l x) ≡⟨ left-homO f x ⟩
  leftO B (funcO f x) ≡⟨ cong (leftO B) (at-most-one-open-hom B f g x) ⟩
  leftO B (funcO g x) ≡˘⟨ left-homO g x ⟩
  funcO g (l x) ∎
at-most-one-open-hom B f g (r x) =
  funcO f (r x) ≡⟨ right-homO f x ⟩
  rightO B (funcO f x) ≡⟨ cong (rightO B) (at-most-one-open-hom B f g x) ⟩
  rightO B (funcO g x) ≡˘⟨ right-homO g x ⟩
  funcO g (r x) ∎

-- We can also show that D′ embeds into any binary system
embedD′ : ∀ {b} → (B : BinarySystem b) → D′ → Carrier B
embedD′ B (mid , tt) = right B (el B)
embedD′ B (l mid , tt) = el B
embedD′ B (l (r x) , tt) = left B (embedD (bs-is-obs B) x)
embedD′ B (r mid , tt) = er B
embedD′ B (r (l x) , tt) = right B (embedD (bs-is-obs B) x)

embedD′-left-hom : ∀ {b} → (B : BinarySystem b) → ∀ x → embedD′ B (end-left ⊕′ x) ≡ left B (embedD′ B x)
embedD′-left-hom B (mid , tt) = refl
embedD′-left-hom B (l mid , tt) = leftel B
embedD′-left-hom B (l (r x) , tt) = refl
embedD′-left-hom B (r mid , tt) = centereq B
embedD′-left-hom B (r (l x) , tt) = refl

embedD′-right-hom : ∀ {b} → (B : BinarySystem b) → ∀ x → embedD′ B (end-right ⊕′ x) ≡ right B (embedD′ B x)
embedD′-right-hom B (mid , tt) = refl
embedD′-right-hom B (l mid , tt) = refl
embedD′-right-hom B (l (r x) , tt) = refl
embedD′-right-hom B (r mid , tt) = righter B
embedD′-right-hom B (r (l x) , tt) = refl

exists-hom : ∀ {b} → (B : BinarySystem b) → BinarySystemHom D′-is-bs B
exists-hom B .func = embedD′ B
exists-hom B .left-end-hom = refl
exists-hom B .right-end-hom = refl
exists-hom B .left-hom = embedD′-left-hom B
exists-hom B .right-hom = embedD′-right-hom B

-- We now notice that D′ contains a copy of D that has been shrunk
-- This can be used to get a morphism from D to a Binary system from a
-- morphism from D′ to that binary system. We do this by halfing the
-- element of D and then passing it through the original function

D′-open-hom : ∀ {b} →
              (B : BinarySystem b) →
              (f : BinarySystemHom D′-is-bs B) →
              OpenBinarySystemHom D-is-obs (bs-is-obs B)
D′-open-hom B f .funcO x = func f ((x /2) , (inSubintervalHalfLem x))
D′-open-hom B f .c-hom =
  func f (end-left ⊕′ end-right) ≡⟨ right-hom f end-left ⟩
  right B (func f end-left) ≡⟨ cong (right B) (left-end-hom f) ⟩
  right B (el B) ∎
D′-open-hom B f .left-homO mid = left-hom f (mid , tt)
D′-open-hom B f .left-homO (l x) = left-hom f (l (r x) , tt)
D′-open-hom B f .left-homO (r x) = left-hom f (r (l x) , tt)
D′-open-hom B f .right-homO mid = right-hom f (mid , tt)
D′-open-hom B f .right-homO (l x) = right-hom f (l (r x) , tt)
D′-open-hom B f .right-homO (r x) = right-hom f (r (l x) , tt)

-- This can be shown that D′ is initial by reusing the proof that D is initial
at-most-one-hom : ∀ {b} →
                  (B : BinarySystem b) →
                  (f g : BinarySystemHom D′-is-bs B) →
                  ∀ x → func f x ≡ func g x
at-most-one-hom B f g (mid , tt) =
  func f (end-left ⊕′ end-right) ≡⟨ right-hom f end-left ⟩
  right B (func f end-left) ≡⟨ cong (right B) (left-end-hom f) ⟩
  right B (el B) ≡˘⟨ cong (right B) (left-end-hom g) ⟩
  right B (func g end-left) ≡˘⟨ right-hom g end-left ⟩
  func g (end-left ⊕′ end-right) ∎
at-most-one-hom B f g (l mid , tt) =
  func f end-left ≡⟨ left-end-hom f ⟩
  el B ≡˘⟨ left-end-hom g ⟩
  func g end-left ∎
at-most-one-hom B f g (l (r x) , tt) =
  at-most-one-open-hom (bs-is-obs B) (D′-open-hom B f) (D′-open-hom B g) (l x)
at-most-one-hom B f g (r mid , tt) =
  func f end-right ≡⟨ right-end-hom f ⟩
  er B ≡˘⟨ right-end-hom g ⟩
  func g end-right ∎
at-most-one-hom B f g (r (l x) , tt) =
  at-most-one-open-hom (bs-is-obs B) (D′-open-hom B f) (D′-open-hom B g) (r x)

-- Now we want to show D′ is the initial midpoint algebra

-- any bipointed midpoint homomorphism is a binary system morphism
bpm-hom-to-bs-hom : ∀ {a b} (A : BiPointMidpointAlgebra a) (B : BiPointMidpointAlgebra b)
                    → BiPointMidpointHom A B → BinarySystemHom (bpm-is-bs A) (bpm-is-bs B)
bpm-hom-to-bs-hom A B f .func = funcM f
bpm-hom-to-bs-hom A B f .left-end-hom = p1-hom f
bpm-hom-to-bs-hom A B f .right-end-hom = p2-hom f
bpm-hom-to-bs-hom A B f .left-hom x =
  funcM f (mp A (p1 A) x) ≡⟨ mp-hom f (p1 A) x ⟩
  mp B (funcM f (p1 A)) (funcM f x) ≡⟨ cong (λ y → mp B y (funcM f x)) (p1-hom f) ⟩
  mp B (p1 B) (funcM f x) ∎
bpm-hom-to-bs-hom A B f .right-hom x =
  funcM f (mp A (p2 A) x) ≡⟨ mp-hom f (p2 A) x ⟩
  mp B (funcM f (p2 A)) (funcM f x) ≡⟨ cong (λ y → mp B y (funcM f x)) (p2-hom f) ⟩
  mp B (p2 B) (funcM f x) ∎

-- We can use this to show there is at most one bipointed midpoint homomorphism from D′
at-most-one-bpm-hom : ∀ {a} (A : BiPointMidpointAlgebra a)
                    → (f g : BiPointMidpointHom D′-is-bpm A)
                    → ∀ x → funcM f x ≡ funcM g x
at-most-one-bpm-hom A f g =
  at-most-one-hom (bpm-is-bs A)
                  (bpm-hom-to-bs-hom D′-is-bpm A f)
                  (bpm-hom-to-bs-hom D′-is-bpm A g)

-- Helpful distributivity lemma
bpm-dist : ∀ {a} (A : BiPointMidpointAlgebra a)
           → ∀ x y z → mp A x (mp A y z) ≡ mp A (mp A x y) (mp A x z)
bpm-dist A x y z =
  mp A x (mp A y z) ≡⟨ cong (λ a → mp A a (mp A y z)) (bpm-idem A x) ⟩
  mp A (mp A x x) (mp A y z) ≡⟨ bpm-trans A x x y z ⟩
  mp A (mp A x y) (mp A x z) ∎

-- A crucial lemma to manipulate embedD′
embedD′/2-is-embedD : ∀ {b} →
                      (B : BinarySystem b) →
                      ∀ x → embedD′ B (x /2 , inSubintervalHalfLem x) ≡ embedD (bs-is-obs B) x
embedD′/2-is-embedD B = at-most-one-open-hom (bs-is-obs B) (D′-open-hom B (exists-hom B)) (embedD-is-hom (bs-is-obs B))

-- Then we need a lemma on embedD

embedD-/2-lem : ∀ {a} (A : BiPointMidpointAlgebra a)
                → ∀ x → embedD (bs-is-obs (bpm-is-bs A)) (x /2) ≡ mp A (mp A (p2 A) (p1 A)) (embedD (bs-is-obs (bpm-is-bs A))x)
embedD-/2-lem A mid = bpm-idem A (mp A (p2 A) (p1 A))
embedD-/2-lem A (l x) =
  mp A (p1 A) (mp A (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) x)) ≡⟨ bpm-dist A (p1 A) (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) x) ⟩
  mp A (mp A (p1 A) (p2 A))
    (mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) x)) ≡⟨ cong (λ a → mp A a (mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) x))) (bpm-comm A (p1 A) (p2 A)) ⟩
  mp A (mp A (p2 A) (p1 A)) (mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) x)) ∎
embedD-/2-lem A (r x) = bpm-dist A (p2 A) (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) x)

embedD-mp-hom : ∀ {a} (A : BiPointMidpointAlgebra a)
                → ∀ x y → embedD (bs-is-obs (bpm-is-bs A)) (x ⊕ y) ≡ mp A (embedD (bs-is-obs (bpm-is-bs A)) x) (embedD (bs-is-obs (bpm-is-bs A)) y)
embedD-mp-hom A mid mid = bpm-idem A (mp A (p2 A) (p1 A))
embedD-mp-hom A mid (l y) =
  mp A (p1 A)
      (mp A (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) y)) ≡⟨ bpm-dist A (p1 A) (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) y) ⟩
  mp A (mp A (p1 A) (p2 A))
    (mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) y)) ≡⟨ cong (λ a → mp A a (mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) y))) (bpm-comm A (p1 A) (p2 A)) ⟩
  mp A (mp A (p2 A) (p1 A))
      (mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) y)) ∎
embedD-mp-hom A mid (r y) = bpm-dist A (p2 A) (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) y)
embedD-mp-hom A (l x) mid =
  mp A (p1 A)
    (mp A (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) x)) ≡⟨ bpm-dist A (p1 A) (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) x) ⟩
  mp A (mp A (p1 A) (p2 A))
    (mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) x)) ≡⟨ bpm-comm A (mp A (p1 A) (p2 A)) (mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) x)) ⟩
  mp A (mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) x))
    (mp A (p1 A) (p2 A)) ≡⟨ cong (mp A (mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) x))) (bpm-comm A (p1 A) (p2 A)) ⟩
  mp A (mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) x))
    (mp A (p2 A) (p1 A)) ∎
embedD-mp-hom A (l x) (l y) =
  mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) (x ⊕ y)) ≡⟨ cong (mp A (p1 A)) (embedD-mp-hom A x y) ⟩
  mp A (p1 A) (mp A (embedD (bs-is-obs (bpm-is-bs A)) x)
                (embedD (bs-is-obs (bpm-is-bs A)) y)) ≡⟨ bpm-dist A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) x) (embedD (bs-is-obs (bpm-is-bs A)) y) ⟩
  mp A (mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) x))
      (mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) y)) ∎
embedD-mp-hom A (l x) (r y) =
  embedD (bs-is-obs (bpm-is-bs A)) ((x ⊕ y) /2) ≡⟨ embedD-/2-lem A (x ⊕ y) ⟩
  mp A (mp A (p2 A) (p1 A)) (embedD (bs-is-obs (bpm-is-bs A)) (x ⊕ y)) ≡⟨ cong₂ (mp A) (bpm-comm A (p2 A) (p1 A)) (embedD-mp-hom A x y) ⟩
  mp A (mp A (p1 A) (p2 A))
    (mp A (embedD (bs-is-obs (bpm-is-bs A)) x)
     (embedD (bs-is-obs (bpm-is-bs A)) y)) ≡⟨ bpm-trans A (p1 A) (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) x) (embedD (bs-is-obs (bpm-is-bs A)) y) ⟩
  mp A (mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) x))
      (mp A (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) y)) ∎
embedD-mp-hom A (r x) mid =
  mp A (p2 A)
      (mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) x)) ≡⟨ bpm-dist A (p2 A) (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) x) ⟩
  mp A (mp A (p2 A) (p1 A))
    (mp A (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) x)) ≡⟨ bpm-comm A (mp A (p2 A) (p1 A)) (mp A (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) x)) ⟩
  mp A (mp A (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) x))
      (mp A (p2 A) (p1 A)) ∎
embedD-mp-hom A (r x) (l y) =
  embedD (bs-is-obs (bpm-is-bs A)) ((x ⊕ y) /2) ≡⟨ embedD-/2-lem A (x ⊕ y) ⟩
  mp A (mp A (p2 A) (p1 A)) (embedD (bs-is-obs (bpm-is-bs A)) (x ⊕ y)) ≡⟨ cong₂ (mp A) (bpm-comm A (p2 A) (p1 A)) (embedD-mp-hom A x y) ⟩
  mp A (mp A (p1 A) (p2 A))
    (mp A (embedD (bs-is-obs (bpm-is-bs A)) x)
     (embedD (bs-is-obs (bpm-is-bs A)) y)) ≡⟨ cong (λ a → mp A a (mp A (embedD (bs-is-obs (bpm-is-bs A)) x)
     (embedD (bs-is-obs (bpm-is-bs A)) y))) (bpm-comm A (p1 A) (p2 A)) ⟩
  mp A (mp A (p2 A) (p1 A))
    (mp A (embedD (bs-is-obs (bpm-is-bs A)) x)
     (embedD (bs-is-obs (bpm-is-bs A)) y)) ≡⟨ bpm-trans A (p2 A) (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) x) (embedD (bs-is-obs (bpm-is-bs A)) y) ⟩
  mp A (mp A (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) x))
      (mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) y)) ∎
embedD-mp-hom A (r x) (r y) =
  mp A (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) (x ⊕ y)) ≡⟨ cong (mp A (p2 A)) (embedD-mp-hom A x y) ⟩
  mp A (p2 A) (mp A (embedD (bs-is-obs (bpm-is-bs A)) x)
                (embedD (bs-is-obs (bpm-is-bs A)) y)) ≡⟨ bpm-dist A (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) x) (embedD (bs-is-obs (bpm-is-bs A)) y) ⟩
  mp A (mp A (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) x))
      (mp A (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) y)) ∎

-- We need this lemma
embedD′-mp-hom : ∀ {a} (A : BiPointMidpointAlgebra a)
               → ∀ x y → embedD′ (bpm-is-bs A) (x ⊕′ y) ≡ mp A (embedD′ (bpm-is-bs A) x) (embedD′ (bpm-is-bs A) y)
embedD′-mp-hom A (mid , tt) (mid , tt) = bpm-idem A (mp A (p2 A) (p1 A))
embedD′-mp-hom A (mid , tt) (l mid , tt) = bpm-comm A (p1 A) (mp A (p2 A) (p1 A))
embedD′-mp-hom A (mid , tt) (l (r y) , tt) =
  mp A (p1 A) (mp A (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) y)) ≡⟨ bpm-dist A (p1 A) (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) y) ⟩
  mp A (mp A (p1 A) (p2 A)) (mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) y)) ≡⟨ cong (λ x → mp A x ((mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) y)))) (bpm-comm A (p1 A) (p2 A)) ⟩
  mp A (mp A (p2 A) (p1 A)) (mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) y)) ∎
embedD′-mp-hom A (mid , tt) (r mid , tt) = bpm-comm A (p2 A) (mp A (p2 A) (p1 A))
embedD′-mp-hom A (mid , tt) (r (l y) , tt) = bpm-dist A (p2 A) (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) y)
embedD′-mp-hom A (l mid , tt) (mid , tt) = refl
embedD′-mp-hom A (l (r x) , tt) (mid , tt) =
  mp A (p1 A) (mp A (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) x)) ≡⟨ bpm-dist A (p1 A) (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) x) ⟩
  mp A (mp A (p1 A) (p2 A)) (mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) x)) ≡⟨ cong (λ a → mp A a (mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) x))) (bpm-comm A (p1 A) (p2 A)) ⟩
  mp A (mp A (p2 A) (p1 A)) (mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) x)) ≡⟨ bpm-comm A (mp A (p2 A) (p1 A)) (mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) x)) ⟩
  mp A (mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) x)) (mp A (p2 A) (p1 A)) ∎
embedD′-mp-hom A (l mid , tt) (l mid , tt) = bpm-idem A (p1 A)
embedD′-mp-hom A (l mid , tt) (l (r y) , tt) = refl
embedD′-mp-hom A (l (r x) , tt) (l mid , tt) = bpm-comm A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) (l x))
embedD′-mp-hom A (l (r x) , tt) (l (r y) , tt) =
  mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) (x ⊕ y)) ≡⟨ cong (mp A (p1 A)) (embedD-mp-hom A x y) ⟩
  mp A (p1 A)
    (mp A (embedD (bs-is-obs (bpm-is-bs A)) x)
     (embedD (bs-is-obs (bpm-is-bs A)) y)) ≡⟨ bpm-dist A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) x) (embedD (bs-is-obs (bpm-is-bs A)) y) ⟩
  mp A (mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) x))
    (mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) y)) ∎
embedD′-mp-hom A (l mid , tt) (r mid , tt) = bpm-comm A (p2 A) (p1 A)
embedD′-mp-hom A (l mid , tt) (r (l y) , tt) = refl
embedD′-mp-hom A (l (r x) , tt) (r mid , tt) = bpm-comm A (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) (l x))
embedD′-mp-hom A (l (r x) , tt) (r (l y) , tt) =
  embedD′ (bpm-is-bs A)
      (((x ⊕ y) /2) /2 , inSubintervalHalfLem ((x ⊕ y) /2)) ≡⟨ embedD′/2-is-embedD (bpm-is-bs A) ((x ⊕ y) /2) ⟩
  embedD (bs-is-obs (bpm-is-bs A)) ((x ⊕ y) /2) ≡⟨ embedD-/2-lem A (x ⊕ y) ⟩
  mp A (mp A (p2 A) (p1 A))
    (embedD (bs-is-obs (bpm-is-bs A)) (x ⊕ y)) ≡⟨ cong₂ (mp A) (bpm-comm A (p2 A) (p1 A)) (embedD-mp-hom A x y) ⟩
  mp A (mp A (p1 A) (p2 A))
    (mp A (embedD (bs-is-obs (bpm-is-bs A)) x)
     (embedD (bs-is-obs (bpm-is-bs A)) y)) ≡⟨ bpm-trans A (p1 A) (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) x) (embedD (bs-is-obs (bpm-is-bs A)) y) ⟩
  mp A (mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) x))
      (mp A (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) y)) ∎
embedD′-mp-hom A (r mid , tt) (mid , tt) = refl
embedD′-mp-hom A (r (l x) , tt) (mid , tt) =
  mp A (p2 A) (mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) x)) ≡⟨ bpm-dist A (p2 A) (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) x) ⟩
  mp A (mp A (p2 A) (p1 A)) (mp A (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) x)) ≡⟨ bpm-comm A (mp A (p2 A) (p1 A)) (mp A (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) x)) ⟩
  mp A (mp A (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) x)) (mp A (p2 A) (p1 A)) ∎
embedD′-mp-hom A (r mid , tt) (l mid , tt) = refl
embedD′-mp-hom A (r mid , tt) (l (r y) , tt) = refl
embedD′-mp-hom A (r (l x) , tt) (l mid , tt) = bpm-comm A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) (r x))
embedD′-mp-hom A (r (l x) , tt) (l (r y) , tt) =
  embedD′ (bpm-is-bs A)
      (((x ⊕ y) /2) /2 , inSubintervalHalfLem ((x ⊕ y) /2)) ≡⟨ embedD′/2-is-embedD (bpm-is-bs A) ((x ⊕ y) /2) ⟩
  embedD (bs-is-obs (bpm-is-bs A)) ((x ⊕ y) /2) ≡⟨ embedD-/2-lem A (x ⊕ y) ⟩
  mp A (mp A (p2 A) (p1 A))
    (embedD (bs-is-obs (bpm-is-bs A)) (x ⊕ y)) ≡⟨ cong (mp A (mp A (p2 A) (p1 A))) (embedD-mp-hom A x y) ⟩
  mp A (mp A (p2 A) (p1 A))
    (mp A (embedD (bs-is-obs (bpm-is-bs A)) x)
     (embedD (bs-is-obs (bpm-is-bs A)) y)) ≡⟨ bpm-trans A (p2 A) (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) x) (embedD (bs-is-obs (bpm-is-bs A)) y) ⟩
  mp A (mp A (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) x))
      (mp A (p1 A) (embedD (bs-is-obs (bpm-is-bs A)) y)) ∎
embedD′-mp-hom A (r mid , tt) (r mid , tt) = bpm-idem A (p2 A)
embedD′-mp-hom A (r mid , tt) (r (l y) , tt) = refl
embedD′-mp-hom A (r (l x) , tt) (r mid , tt) = bpm-comm A (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) (r x))
embedD′-mp-hom A (r (l x) , tt) (r (l y) , tt) =
  mp A (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) (x ⊕ y)) ≡⟨ cong (mp A (p2 A)) (embedD-mp-hom A x y) ⟩
  mp A (p2 A)
    (mp A (embedD (bs-is-obs (bpm-is-bs A)) x)
     (embedD (bs-is-obs (bpm-is-bs A)) y)) ≡⟨ bpm-dist A (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) x) (embedD (bs-is-obs (bpm-is-bs A)) y) ⟩
  mp A (mp A (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) x))
    (mp A (p2 A) (embedD (bs-is-obs (bpm-is-bs A)) y)) ∎

exists-bpm-hom : ∀ {a} (A : BiPointMidpointAlgebra a)
               → BiPointMidpointHom D′-is-bpm A
exists-bpm-hom A .funcM = embedD′ (bpm-is-bs A)
exists-bpm-hom A .p1-hom = refl
exists-bpm-hom A .p2-hom = refl
exists-bpm-hom A .mp-hom = embedD′-mp-hom A
