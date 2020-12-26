{-# OPTIONS --safe --without-K #-}
module Data.Nat.Divisibility.Extra where

open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (*-comm)
open import Data.Nat.Divisibility public
open import Relation.Binary.PropositionalEquality using (trans)

∣-swap : {x y : ℕ} → (p : x ∣ y) → quotient p ∣ y
∣-swap {x} p = divides x (trans (_∣_.equality p) (*-comm (quotient p) _))

