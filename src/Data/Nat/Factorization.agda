{-# OPTIONS --without-K --safe #-}
module Data.Nat.Factorization where

open import Data.Fin using (toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.List using ([]; _∷_)
import Data.List as List
open import Data.Nat
open import Data.Nat.Divisibility
open import Data.Nat.Induction
open import Data.Nat.Primality
open import Data.Nat.Primality.Compositeness
open import Data.Nat.Properties
open import Data.Product
open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

infixr 4 _[_]∷_

data PrimeFactorization : ℕ → Set where
  [] : PrimeFactorization 1
  _[_]∷_ : ∀ p {n} → Prime p → PrimeFactorization n → PrimeFactorization (p * n)

_++_ : ∀ {m n} → PrimeFactorization m → PrimeFactorization n → PrimeFactorization (m * n)
[] ++ y = subst PrimeFactorization (sym (*-identityˡ _)) y
(p [ prime ]∷ x) ++ y = subst PrimeFactorization (sym (*-assoc p _ _)) (p [ prime ]∷ (x ++ y))

toList : ∀ {n} → PrimeFactorization n → List.List ℕ
toList [] = []
toList (p [ _ ]∷ ps) = p ∷ toList ps

private
  6-factorization : PrimeFactorization 6
  6-factorization = 2 [ (λ ()) ]∷ 3 [ from-yes (prime? 3) ]∷ []

  42-factorization : PrimeFactorization 42
  42-factorization = 2 [ (λ ()) ]∷ 3 [ from-yes (prime? 3) ]∷ 7 [ from-yes (prime? 7) ]∷ []

-- This could be faster. Currently it's performing very naive trial division.
-- If we carry around a witness that the number has no factors below a certain
-- amount it could be significantly faster.
-- Further optimizations include stopping at the square root of the number under
-- consideration, and hooking up a prime sieve and only checking prime factors.
primeFactorization : (n : ℕ) → PrimeFactorization (suc n)
primeFactorization = <-rec (PrimeFactorization ∘ suc) primeFactorization′
  where
    primeFactorization′ : ∀ x → (∀ y → y < x → PrimeFactorization (suc y)) → PrimeFactorization (suc x)
    primeFactorization′ zero p = []
    primeFactorization′ (suc n) p with composite? (suc (suc n))
    ... | yes (i , 2+i∣2+n) =
      let
        -- we should use ∸ to compute this, it'd be compiled better most likely.
        -- introspecting a ≤″ is generally a bad idea if efficiency is the goal.
        pq×spq≡q : ∃[ pq ] 2 + pq ≡ quotient 2+i∣2+n
        pq×spq≡q = case ≤⇒≤″ (*-cancelʳ-< 1 (quotient 2+i∣2+n) (subst₂ _<_ (sym (*-identityˡ _)) (_∣_.equality 2+i∣2+n) (s≤s (s≤s (toℕ<n i))))) of λ { (less-than-or-equal {k} p) → k , p }
      in subst PrimeFactorization (trans (cong (_* suc (suc (toℕ i))) (proj₂ pq×spq≡q)) (sym (_∣_.equality 2+i∣2+n))) (p (suc (proj₁ pq×spq≡q)) (+-cancelˡ-< 1 (subst₂ _<_ (sym (proj₂ pq×spq≡q)) (sym (_∣_.equality 2+i∣2+n)) (m<m*n (subst (0 <_) (proj₂ (pq×spq≡q)) (s≤s z≤n)) (s≤s (s≤s z≤n))))) ++ p (suc (toℕ i)) (s≤s (toℕ<n i)))
    ... | no ¬r = subst PrimeFactorization (*-identityʳ (2 + n)) (suc (suc n) [ Prime′⊆Prime (2 + n) ¬r ]∷ [])

