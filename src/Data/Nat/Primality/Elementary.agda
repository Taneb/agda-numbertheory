{-# OPTIONS --safe --without-K #-}
-- A definition of primality in terms of Euclid's lemma
module Data.Nat.Primality.Elementary where

open import Data.Empty
open import Data.Fin using (toℕ; fromℕ<)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ<n)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Divisibility.Extra
open import Data.Nat.GCD
open import Data.Nat.Primality
open import Data.Product
open import Data.Sum
open import Function
open import Relation.Unary
open import Relation.Binary.PropositionalEquality

-- n is prime if it is not 0 or 1, and if n ∣ x * y then either n ∣ x or n ∣ y
-- this is roughly, the definition used for a prime element of a ring, and in
-- many rings it is a stronger property than that n is irreducable
Prime″ : Pred ℕ _
Prime″ 0 = ⊥
Prime″ 1 = ⊥
Prime″ (suc (suc n)) = ∀ x y → 2 + n ∣ x * y → 2 + n ∣ x ⊎ 2 + n ∣ y

-- This is commonly called Euclid's lemma
Prime⇒Prime″ : Prime ⊆′ Prime″
Prime⇒Prime″ (suc (suc n)) 2+n-prime a b 2+n∣ab with Bézout.lemma (2 + n) a
-- If gcd (2 + n) a ≡ 0, then 2 + n ≡ 0 which is a contradiction
... | Bézout.result 0 g id = case 0∣⇒≡0 (proj₁ (GCD.commonDivisor g)) of λ {()}
-- If 2 + n and a are coprime, then there exists s, r ∈ ℤ with 1 ≡ r * (2 + n) + s * a
-- multiply both sides by b to get b ≡ r * (2 + n) * b + s * a * b
-- we know 2 + n ∣ r * (2 + n) * b and 2 + n ∣  s * a b
-- so 2 + n ∣ b
-- Because we're working in ℕ things are slightly trickier. We need a case for when
-- s is positive and r is negative, and for when s is negative and r is positive.
... | Bézout.result 1 g (Bézout.+- s r eq) = inj₂ (∣m+n∣m⇒∣n (subst (λ k → 2 + n ∣ k) (trans (cong (_* b) (sym eq)) (+-comm b (r * a * b))) (∣m⇒∣m*n b (n∣m*n s))) (subst (λ k → 2 + n ∣ k) (sym (*-assoc r a b)) (∣n⇒∣m*n r 2+n∣ab)))
... | Bézout.result 1 g (Bézout.-+ s r eq) = inj₂ (∣m+n∣m⇒∣n (subst (λ k → 2 + n ∣ k) (trans (sym (*-assoc r a b)) (trans (cong (_* b) (sym eq)) (+-comm b (s * (2 + n) * b)))) ((∣n⇒∣m*n r 2+n∣ab))) (∣m⇒∣m*n b (n∣m*n s)))
-- If gcd (2 + n) a ≥ 2, then either the gcd is less than 2 + n, or it is 2 + n
... | Bézout.result (suc (suc d)) g id with m≤n⇒m<n∨m≡n (∣⇒≤ (proj₁ (GCD.commonDivisor g)))
-- If it is less than 2 + n, then 2 + n has a proper divisor, so it isn't prime, contradiction
... | inj₁ (s≤s (s≤s d<n)) = ⊥-elim (2+n-prime (fromℕ< d<n) (subst (λ x → 2 + x ∣ 2 + n) (sym (toℕ-fromℕ< d<n)) (proj₁ (GCD.commonDivisor g))))
-- If it is equal to 2 + n, then 2 + n divides a
... | inj₂ refl = inj₁ (proj₂ (GCD.commonDivisor g))

-- Every prime element is irreducible. There is an equivalent to this in any integral domain
Prime″⇒Prime : Prime″ ⊆′ Prime
Prime″⇒Prime (suc (suc n)) p i 2+i∣2+n with p (quotient 2+i∣2+n) (2 + toℕ i) (∣-reflexive (_∣_.equality 2+i∣2+n))
... | inj₁ 2+n∣quotient = <⇒≢ (subst (λ x → quotient 2+i∣2+n < x) (sym (_∣_.equality 2+i∣2+n)) (m<m*n (n≢0⇒n>0 λ { refl → case 0∣⇒≡0 (∣-swap 2+i∣2+n) of λ {()}}) (s≤s 0<1+n))) (∣-antisym (∣-swap 2+i∣2+n) 2+n∣quotient)
... | inj₂ 2+n∣2+i = <⇒≢ (s≤s (s≤s (toℕ<n i))) (∣-antisym 2+i∣2+n 2+n∣2+i)

