{-# OPTIONS --safe --without-K --postfix-projections #-}

module Test where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Function.Base
open import Data.Maybe
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Level renaming (suc to lsuc)

data D : Set where
  mid : D
  l : D → D
  r : D → D

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

nameGoesHere : D -> Set
nameGoesHere mid = ⊤
nameGoesHere (l mid) = ⊤
nameGoesHere (l (l x)) = ⊥
nameGoesHere (l (r x)) = ⊤
nameGoesHere (r mid) = ⊤
nameGoesHere (r (r x)) = ⊥
nameGoesHere (r (l x)) = ⊤

nameGoesHereHalfLem : ∀ x → nameGoesHere (x /2)
nameGoesHereHalfLem mid = tt
nameGoesHereHalfLem (l x) = tt
nameGoesHereHalfLem (r x) = tt

nameGoesHereLemma : ∀ x y → nameGoesHere x → nameGoesHere y → nameGoesHere (x ⊕ y)
nameGoesHereLemma mid y pf1 pf2 = nameGoesHereHalfLem y
nameGoesHereLemma (l x) mid pf1 pf2 = tt
nameGoesHereLemma (l mid) (l mid) pf1 pf2 = tt
nameGoesHereLemma (l mid) (l (r y)) pf1 pf2 = tt
nameGoesHereLemma (l (r x)) (l mid) pf1 pf2 = tt
nameGoesHereLemma (l (r x)) (l (r y)) pf1 pf2 = tt
nameGoesHereLemma (l x) (r y) pf1 pf2 = nameGoesHereHalfLem (x ⊕ y)
nameGoesHereLemma (r x) mid pf1 pf2 = tt
nameGoesHereLemma (r x) (l y) pf1 pf2 = nameGoesHereHalfLem (x ⊕ y)
nameGoesHereLemma (r mid) (r mid) pf1 pf2 = tt
nameGoesHereLemma (r mid) (r (l y)) pf1 pf2 = tt
nameGoesHereLemma (r (l x)) (r mid) pf1 pf2 = tt
nameGoesHereLemma (r (l x)) (r (l y)) pf1 pf2 = tt

D′ : Set
D′ = Σ D nameGoesHere

infix 8 _⊕′_
_⊕′_ : D′ → D′ → D′
(x , xpf) ⊕′ (y , ypf) = (x ⊕ y) , (nameGoesHereLemma x y xpf ypf)

nameGoesHereProp : ∀ x → (pf1 pf2 : nameGoesHere x) → pf1 ≡ pf2
nameGoesHereProp mid pf1 pf2 = refl
nameGoesHereProp (l mid) pf1 pf2 = refl
nameGoesHereProp (l (r x)) pf1 pf2 = refl
nameGoesHereProp (r mid) pf1 pf2 = refl
nameGoesHereProp (r (l x)) pf1 pf2 = refl

primeEqLemma : (x y : D′) → proj₁ x ≡ proj₁ y → x ≡ y
primeEqLemma (x , xpf) (.x , ypf) refl rewrite nameGoesHereProp x xpf ypf = refl

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

⊕′-comm : ∀ x y → x ⊕′ y ≡ y ⊕′ x
⊕′-comm x y = primeEqLemma (x ⊕′ y) (y ⊕′ x) (⊕-comm (proj₁ x) (proj₁ y))

⊕′-idem : ∀ x → x ≡ x ⊕′ x
⊕′-idem x = primeEqLemma x (x ⊕′ x) (⊕-idem (proj₁ x))

⊕′-trans : ∀ a b c d → (a ⊕′ b) ⊕′ (c ⊕′ d) ≡ (a ⊕′ c) ⊕′ (b ⊕′ d)
⊕′-trans a b c d = primeEqLemma ((a ⊕′ b) ⊕′ (c ⊕′ d)) ((a ⊕′ c) ⊕′ (b ⊕′ d)) (⊕-trans (proj₁ a) (proj₁ b) (proj₁ c) (proj₁ d))

end-left : D′
end-left = (l mid) , tt

end-right : D′
end-right = (r mid) , tt

record BinarySystem (a : Level) : Set (lsuc a) where
  field
    Carrier : Set a
    el er : Carrier
    left right : Carrier → Carrier
    leftel : el ≡ left el
    righter : er ≡ right er
    centereq : right el ≡ left er

open BinarySystem

D′-is-binary-system : BinarySystem 0ℓ
D′-is-binary-system .Carrier = D′
D′-is-binary-system .el = end-left
D′-is-binary-system .er = end-right
D′-is-binary-system .left = _⊕′ end-left
D′-is-binary-system .right = _⊕′ end-right
D′-is-binary-system .leftel = ⊕′-idem (end-left)
D′-is-binary-system .righter = ⊕′-idem (end-right)
D′-is-binary-system .centereq = ⊕′-comm end-left end-right

record BinarySystemHom {a b} (A : BinarySystem a) (B : BinarySystem b) : Set (lsuc (a ⊔ b)) where
  field
    func : Carrier A → Carrier B
    left-end-hom : func (el A) ≡ el B
    right-end-hom : func (er A) ≡ er B
    left-hom : ∀ x → func (left A x) ≡ left B (func x)
    right-hom : ∀ x → func (right A x) ≡ right B (func x)

open BinarySystemHom

record OpenBinarySystem (a : Level) : Set (lsuc a) where
  field
    CarrierO : Set a
    c : CarrierO
    leftO rightO : CarrierO → CarrierO

open OpenBinarySystem


left-OBS : ∀ {b} → (OpenBinarySystem b) → OpenBinarySystem b
left-OBS B .CarrierO = CarrierO B
left-OBS B .c = leftO B (c B)
left-OBS B .leftO = leftO B
left-OBS B .rightO = rightO B

right-OBS : ∀ {b} → (OpenBinarySystem b) → OpenBinarySystem b
right-OBS B .CarrierO = CarrierO B
right-OBS B .c = rightO B (c B)
right-OBS B .leftO = leftO B
right-OBS B .rightO = rightO B

D-is-open-binary-system : OpenBinarySystem 0ℓ
D-is-open-binary-system .CarrierO = D
D-is-open-binary-system .c = mid
D-is-open-binary-system .leftO = l
D-is-open-binary-system .rightO = r

record OpenBinarySystemHom {a b} (A : OpenBinarySystem a) (B : OpenBinarySystem b) : Set (lsuc (a ⊔ b)) where
  field
    funcO : CarrierO A → CarrierO B
    c-hom : funcO (c A) ≡ c B
    left-homO : ∀ x → funcO (leftO A x) ≡ leftO B (funcO x)
    right-homO : ∀ x → funcO (rightO A x) ≡ rightO B (funcO x)

open OpenBinarySystemHom

binary-system-is-open-binary-system : ∀ {b} → BinarySystem b → OpenBinarySystem b
binary-system-is-open-binary-system B .CarrierO = Carrier B
binary-system-is-open-binary-system B .c = right B (el B)
binary-system-is-open-binary-system B .leftO = left B
binary-system-is-open-binary-system B .rightO = right B

at-most-one-open-hom : ∀ {b} → (B : OpenBinarySystem b) → (f g : OpenBinarySystemHom D-is-open-binary-system B) → ∀ x → funcO f x ≡ funcO g x
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

embedD : ∀ {b} → (B : OpenBinarySystem b) → D → CarrierO B
embedD B mid = c B
embedD B (l x) = leftO B (embedD B x)
embedD B (r x) = rightO B (embedD B x)

D′-open-hom : ∀ {b} → (B : BinarySystem b) → (f : BinarySystemHom D′-is-binary-system B) → OpenBinarySystemHom D-is-open-binary-system (binary-system-is-open-binary-system B)
D′-open-hom B f .funcO x = func f ((x /2) , (nameGoesHereHalfLem x))
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

at-most-one-hom : ∀ {b} → (B : BinarySystem b) → (f g : BinarySystemHom D′-is-binary-system B) → ∀ x → func f x ≡ func g x
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
at-most-one-hom B f g (l (r x) , tt) = at-most-one-open-hom (binary-system-is-open-binary-system B) (D′-open-hom B f) (D′-open-hom B g) (l x)
at-most-one-hom B f g (r mid , tt) =
  func f end-right ≡⟨ right-end-hom f ⟩
  er B ≡˘⟨ right-end-hom g ⟩
  func g end-right ∎
at-most-one-hom B f g (r (l x) , tt) = at-most-one-open-hom (binary-system-is-open-binary-system B) (D′-open-hom B f) (D′-open-hom B g) (r x)

embedD′ : ∀ {b} → (B : BinarySystem b) → D′ → Carrier B
embedD′ B (mid , tt) = right B (el B)
embedD′ B (l mid , tt) = el B
embedD′ B (l (r x) , tt) = left B (embedD (binary-system-is-open-binary-system B) x)
embedD′ B (r mid , tt) = er B
embedD′ B (r (l x) , tt) = right B (embedD (binary-system-is-open-binary-system B) x)

embedD′-left-hom : ∀ {b} → (B : BinarySystem b) → ∀ x → embedD′ B (x ⊕′ end-left) ≡ left B (embedD′ B x)
embedD′-left-hom B (mid , tt) = refl
embedD′-left-hom B (l mid , tt) = leftel B
embedD′-left-hom B (l (r x) , tt) = refl
embedD′-left-hom B (r mid , tt) = centereq B
embedD′-left-hom B (r (l x) , tt) = refl

embedD′-right-hom : ∀ {b} → (B : BinarySystem b) → ∀ x → embedD′ B (x ⊕′ end-right) ≡ right B (embedD′ B x)
embedD′-right-hom B (mid , tt) = refl
embedD′-right-hom B (l mid , tt) = refl
embedD′-right-hom B (l (r x) , tt) = refl
embedD′-right-hom B (r mid , tt) = righter B
embedD′-right-hom B (r (l x) , tt) = refl

exists-hom : ∀ {b} → (B : BinarySystem b) → BinarySystemHom D′-is-binary-system B
exists-hom B .func = embedD′ B
exists-hom B .left-end-hom = refl
exists-hom B .right-end-hom = refl
exists-hom B .left-hom = embedD′-left-hom B
exists-hom B .right-hom = embedD′-right-hom B
