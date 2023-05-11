module Data.MultiSubset where

open import Data.Nat using (ℕ; suc; zero; _<_)
open import Data.Fin using (Fin; suc; zero)
open import Data.Product using (∃-syntax)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

record MultiSubset (A : Set) : Set where
  field
    {size} : ℕ
    get : Fin size → A
open MultiSubset public

record MultiSubset⁺ (A : Set) : Set where
  field
    multisubset : MultiSubset A
    non-empty   : zero < size multisubset

_∈_ : ∀ {A : Set} → A → MultiSubset A → Set
a ∈ S = ∃[ n ] (get S n ≡ a)

_⊆_ : ∀ {A : Set} → MultiSubset A → MultiSubset A → Set
_⊆_ {A} S T = ∀ (a : A) → a ∈ S → a ∈ T
