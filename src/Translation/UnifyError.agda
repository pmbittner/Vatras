module Translation.UnifyError where

open import Data.Nat
open import Data.List using (List; []; _∷_; sum)
open import Data.List.NonEmpty using (List⁺; _∷_; toList)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

data Dom (A : Set): Set where
  leaf : A → Dom A
  node : List⁺ (Dom A) → Dom A

data _⊢_⟶_ : ∀ (A : Set) → List⁺ (Dom A) → ℕ → Set
infix 3 _⊢_⟶_

data _⊢_⟶₂_ : (A : Set) → Dom A → ℕ → Set where
  Leaf : ∀ {A : Set} {a : A}
      -----------------------
    → A ⊢ leaf a ⟶₂ 1

  Node : ∀ {A : Set} {n : ℕ} {as : List⁺ (Dom A)}
    → A ⊢ as ⟶ n
      -----------------
    → A ⊢ node as ⟶₂ n

data _⊢_⟶_ where
  Done :
     ∀ {A : Set}
       {a : Dom A}
       {n : ℕ}
     → A ⊢ a ⟶₂ n
       ---------------
     → A ⊢ a ∷ [] ⟶ n

  Recurse :
     ∀ {A : Set}
       {a b : Dom A}
       {n m : ℕ}
       {cs : List (Dom A)}
     → A ⊢ a ⟶₂ n
     → A ⊢ b ∷ cs ⟶ m
       -----------------------
     → A ⊢ a ∷ b ∷ cs ⟶ n + m

⟶-is-deterministic : ∀ {A : Set} {as : List⁺ (Dom A)} {n n' : ℕ}
  → A ⊢ as ⟶ n
  → A ⊢ as ⟶ n'
    ------------
  → n ≡ n'
⟶-is-deterministic (Done x) (Done x₁) = {!!}
⟶-is-deterministic (Recurse x x₁) (Recurse x₂ y) = {!!}
