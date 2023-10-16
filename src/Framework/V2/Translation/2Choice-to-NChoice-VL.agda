open import Framework.V2.Definitions

module Framework.V2.Translation.2Choice-to-NChoice-VL {F : 𝔽} where

open import Data.Bool using (Bool; false; true)
open import Data.List using (List; _∷_; [])
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (proj₁; proj₂) renaming (_,_ to _and_)
open import Function using (_∘_)

-- open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

import Data.IndexedSet

open import Framework.V2.Variants
open import Framework.V2.Compiler

import Framework.V2.Translation.2Choice-to-NChoice as 2→N
open 2→N using (ConfSpec; FnocSpec)

open import Framework.V2.Constructs.Choices as Chc
open Chc.Choice₂ using (_⟨_,_⟩) renaming (Config to Config₂; map to map₂)
open Chc.Choiceₙ using (_⟨_⟩) renaming (Config to Configₙ; map to mapₙ)

module Translate {F : 𝔽} {V : 𝕍} {A : 𝔸}
  (Γ₁ : VariabilityLanguage V F Bool)
  (Γ₂ : VariabilityLanguage V F ℕ)
  (t : LanguageCompiler Γ₁ Γ₂)
  where
  private
    ⟦_⟧₁ = Semantics Γ₁
    ⟦_⟧₂ = Semantics Γ₂
    L₁ = Expression Γ₁
    L₂ = Expression Γ₂
    open LanguageCompiler t

  open VariabilityConstruct (Chc.VLChoice₂.Construct F)
    renaming (Construct to 2Choice; _⊢⟦_⟧ to _⊢⟦_⟧₁)
  open VariabilityConstruct (Chc.VLChoiceₙ.Construct F)
    renaming (Construct to NChoice; _⊢⟦_⟧ to _⊢⟦_⟧₂)

  -- todo: generalize to any setoid for L₁
  module 2→N-T = 2→N.Translate {Q = F} (Eq.setoid (L₂ A))
  open 2→N-T using (convert)

  -- Composition of two compilers:
  -- first: We convert the binary choice to an n-ary choice via convert, not changing any data
  -- second: We convert all alternatives from one language to another using `mapₙ t`.
  -- This composition is commutative; there is a commuting square
  --   mapₙ t ∘ convert ≅ convert ∘ map₂ t
  -- TODO: Prove this commutativity.
  convert-vl : 2Choice F L₁ A → NChoice F L₂ A
  convert-vl = convert ∘ (map₂ compile)

  module Preservation
    (D : F)
    (l r : L₁ A)
    where
    open 2→N-T.Preservation conf fnoc using (convert-preserves)
    open import Framework.V2.V1Compat using (Conf-Preserves; Fnoc-Preserves; _,_⊢_≚_)
    open import Function using (id)

    module LSet = Data.IndexedSet (Eq.setoid (L₁ A))
    module VSet = IVSet V A
    open LSet using () renaming (_≅_ to _≋_)
    open VSet using (_≅[_][_]_; ≐→≅)
    open VSet.≅[]-Reasoning

    convert-vl-preserves :
      -- TODO: - Use config compiler
      --       - Abstract conv and vnoc? Probably not.
      ∀ (conv : ConfSpec D conf)
      → (vnoc : FnocSpec D fnoc)
      → Stable config-compiler -- do we have this already somewhere?
      → (Γ₁ ⊢⟦ D ⟨ l , r ⟩ ⟧₁) ≅[ conf ][ fnoc ] (Γ₂ ⊢⟦ convert-vl (D ⟨ l , r ⟩) ⟧₂)
    convert-vl-preserves conv vnoc stable =
      ≅[]-begin
        Γ₁ ⊢⟦ D ⟨ l , r ⟩ ⟧₁
      ≅[]⟨⟩
        (λ c → ⟦ Choice₂.Standard-Semantics (D ⟨ l , r ⟩) c ⟧₁ c)
      ≅[]⟨ VLChoice₂.map-compile-preserves t (D ⟨ l , r ⟩) stable ⟩
        (λ c → ⟦ Choice₂.Standard-Semantics (map₂ compile (D ⟨ l , r ⟩)) (fnoc c) ⟧₂ c)
      ≅[]⟨⟩
        (λ c → ⟦ Choice₂.Standard-Semantics (D ⟨ compile l , compile r ⟩) (fnoc c) ⟧₂ c)
        -- TODO: Figure out why we need only proj₂ and not also proj₁ in this proof..
      ≐˘[ c ]⟨ Eq.cong (λ x → ⟦ x ⟧₂ c) (proj₂ (convert-preserves D (compile l) (compile r) conv vnoc) c) ⟩
        (λ c → ⟦ Choiceₙ.Standard-Semantics (convert (D ⟨ compile l , compile r ⟩)) c ⟧₂ c)
      ≅[]⟨⟩
        (λ c → ⟦ Choiceₙ.Standard-Semantics (convert (map₂ compile (D ⟨ l , r ⟩))) c ⟧₂ c)
      ≅[]⟨⟩
        Γ₂ ⊢⟦ convert (map₂ compile (D ⟨ l , r ⟩)) ⟧₂
      ≅[]⟨⟩
        Γ₂ ⊢⟦ convert-vl (D ⟨ l , r ⟩) ⟧₂
      ≅[]-∎
