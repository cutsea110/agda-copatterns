{-# OPTIONS --guardedness #-}
module tutorial where

open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Data.Product using (_×_; _,_)

record Stream (A : Set) : Set where
  coinductive
  field
    hd : A
    tl : Stream A

open Stream

record _≈_ {A} (xs : Stream A) (ys : Stream A) : Set where
  coinductive
  field
    hd-≡ : hd xs ≡ hd ys
    tl-≈ : tl xs ≈ tl ys

open _≈_

even : ∀ {A} → Stream A → Stream A
hd (even xs) = hd xs
tl (even xs) = even (tl (tl xs))

odd : ∀ {A} → Stream A → Stream A
odd xs = even (tl xs)

split : ∀ {A} →  Stream A → Stream A × Stream A
split xs =  even xs , odd xs

merge : ∀ {A} → Stream A × Stream A → Stream A
hd (merge (xs , ys)) = hd xs
tl (merge (xs , ys)) = merge (ys , tl xs)

merge-split-id : ∀ {A} (xs : Stream A) → merge (split xs) ≈ xs
hd-≡ (merge-split-id xs) = refl
tl-≈ (merge-split-id xs) = merge-split-id (tl xs)

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

open import Data.String

test : String
test =  "ℕ ℤ ℚ ℝ ℂ"
