{-# OPTIONS --safe --without-K #-}
-- A definition of primality in terms of compositeness.
module Data.Nat.Primality.Compositeness where

open import Data.Fin.Base using (Fin; toℕ)
open import Data.Fin.Properties using (any?)
open import Data.Nat.Base using (ℕ; suc; _+_) 
open import Data.Nat.Divisibility using (_∣_; _∣?_)
open import Data.Nat.Primality
open import Data.Product using (_,_; Σ-syntax)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary
open import Relation.Unary

-- 0 and 1 are composite. A number greater than 1 is composite if and only if it
-- has a proper divisor.
Composite : Pred ℕ _
Composite 0 = ⊤
Composite 1 = ⊤
Composite (suc (suc n)) = Σ[ i ∈ Fin n ] 2 + toℕ i ∣ 2 + n

-- A natural number is prime exactly when it is not composite.
Prime′ : Pred ℕ _
Prime′ = ∁ Composite

-- We can check whether a number is composite by trial division.
composite? : Decidable Composite
composite? 0 = yes tt
composite? 1 = yes tt
composite? (suc (suc n)) = any? λ _ → _ ∣? _

-- This definition of primality is equivalent to the one in Data.Nat.Primality
Prime⊆Prime′ : Prime ⊆′ Prime′
Prime⊆Prime′ (suc (suc n)) n-prime (i , 2+i∣2+n) = n-prime i 2+i∣2+n

Prime′⊆Prime : Prime′ ⊆′ Prime
Prime′⊆Prime 0 0-prime = 0-prime tt
Prime′⊆Prime 1 1-prime = 1-prime tt
Prime′⊆Prime (suc (suc n)) n-prime i 2+i∣2+n = n-prime (i , 2+i∣2+n)
