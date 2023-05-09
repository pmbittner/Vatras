module Translation.UnifyError where

open import Data.Nat
open import Data.List
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

data _,_⊢_⟶_ : ∀ (A : Set) → ℕ → List A → List ℕ → Set
infix 3 _,_⊢_⟶_

data _⟶₂_ : ℕ → ℕ → Set where
  s : ∀ {n : ℕ} → n ⟶₂ suc n

data _,_⊢_⟶_ where
  Done :
     ∀ {A : Set}
       {n : ℕ}
       -----------------
     → A , n ⊢ [] ⟶ []

  Recurse :
     ∀ {A : Set}
       {n : ℕ}
       {a  : A}
       {as : List A}
       {m  : ℕ}
       {ns : List ℕ}
     → n ⟶₂ m
     → A , suc n ⊢ as ⟶ ns
       ------------------------------
     → A ,     n ⊢ a ∷ as ⟶ m ∷ ns

⟶-is-deterministic : ∀ {A : Set} {n : ℕ} {as : List A} {ns ns' : List ℕ}
  → A , n ⊢ as ⟶ ns
  → A , n ⊢ as ⟶ ns'
    ------------
  → ns ≡ ns'
⟶-is-deterministic Done Done = refl
⟶-is-deterministic (Recurse x x₂) (Recurse x₁ y) = ?
