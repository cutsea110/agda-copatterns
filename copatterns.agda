{-# OPTIONS --copatterns #-}
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_

pair : {A B : Set} → A → B → A × B
fst (pair x y) = x
snd (pair x y) = y

swap : {A B : Set} → A × B → B × A
fst (swap p) = snd p
snd (swap p) = fst p

swap3 : {A B C : Set} → (A × B) × C → C × (B × A)
fst (swap3 t) = snd t
fst (snd (swap3 t)) = snd (fst t)
snd (snd (swap3 t)) = fst (fst t)

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A
open Stream

repeat : {A : Set} → A → Stream A
head (repeat x) = x
tail (repeat x) = repeat x

open import Data.Nat

nats : ℕ → Stream ℕ
head (nats zero) = zero
tail (nats zero) = nats zero
head (nats (suc x)) = x
tail (nats (suc x)) = nats x

record State (S A : Set) : Set where
  constructor state
  field
    runState : S → A × S
open State

record Monad (M : Set → Set) : Set₁ where
  constructor monad
  field
    return : {A : Set} → A → M A
    _>>=_ : {A B : Set} → M A → (A → M B) → M B

stateMonad : {S : Set} → Monad (State S)
runState (Monad.return stateMonad a) s = a , s
runState (Monad._>>=_ stateMonad m k) s₀ =
  let a , s₁ = runState  m s₀
  in runState (k a) s₁

open import Relation.Binary.PropositionalEquality as PropEq

module MonadLawForState {S : Set} where
  open Monad (stateMonad {S})

  leftId : {A B : Set}(a : A)(k : A → State S B) → (return a >>= k) ≡ k a
  leftId a k = refl

  rightId : {A B : Set}(m : State S A) → (m >>= return) ≡ m
  rightId m = refl

  assoc : {A B C : Set}(m : State S A)(k : A → State S B)(l : B → State S C) → 
          ((m >>= k) >>= l) ≡ (m >>= λ a → (k a >>= l))
  assoc m k l = refl
