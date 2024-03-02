{-# OPTIONS --sized-types #-}

open import Framework.Construct using (_∈ₛ_; cons; snoc; id-l)
open import Construct.Artifact as At using () renaming (Syntax to Artifact; _-<_>- to artifact-constructor)

module Translation.Lang.FCC-to-FCC (Variant : Set → Set) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

open import Data.Empty using (⊥-elim)
import Data.EqIndexedSet as IndexedSet
open import Data.Fin as Fin using (Fin; zero; suc)
import Data.Fin.Properties as Fin
open import Data.List as List using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
import Data.List.Properties as List
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; s≤s; z≤n; _+_; _∸_)
open import Data.Nat.Properties as ℕ using (≤-refl; ≤-reflexive; ≤-trans; <-trans)
open import Data.Product using (_×_; _,_)
open import Data.Vec as Vec using (Vec; []; _∷_)
import Data.Vec.Properties as Vec
open import Framework.Compiler using (LanguageCompiler)
open import Framework.Relation.Function using (from; to)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; _≗_)
open import Relation.Nullary.Decidable using (yes; no)
open import Size using (Size; ↑_; ∞)
import Util.AuxProofs as ℕ
open import Util.List using (find-or-last; map-find-or-last; find-or-last⇒lookup; lookup⇒find-or-last)
open import Util.Nat.AtLeast as ℕ≥ using (ℕ≥; sucs; _⊔_)
import Util.Vec as Vec

open Eq.≡-Reasoning using (step-≡; step-≡˘; _≡⟨⟩_; _∎)
open IndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]-sym; ≅[]-trans)
open IndexedSet.≅[]-Reasoning using (step-≅[]; _≅[]⟨⟩_; _≅[]-∎)
open IndexedSet.⊆-Reasoning using (step-⊆; _⊆-∎)

import Lang.FCC
module FCC n = Lang.FCC n
open FCC renaming (Configuration to FCCꟲ)
open Lang.FCC.Sem using (FCCL)
module FCCSem {n} {A} = Lang.FCC.Sem n A Variant Artifact∈ₛVariant
open FCCSem using () renaming (⟦_⟧ to ⟦_⟧ₙ)

artifact : {A : Set} → A → List (Variant A) → Variant A
artifact a cs = cons Artifact∈ₛVariant (artifact-constructor a cs)


module map-dim where
  map-dim : {i : Size} → {D₁ D₂ A : Set} → (n : ℕ≥ 2) → (D₁ → D₂) → FCC n D₁ i A → FCC n D₂ i A
  map-dim n f (a -< cs >-) = a -< List.map (map-dim n f) cs >-
  map-dim n f (d ⟨ cs ⟩) = f d ⟨ Vec.map (map-dim n f) cs ⟩

  preserves-⊆ : {i : Size} → {D₁ D₂ A : Set} → (n : ℕ≥ 2) → (f : D₁ → D₂) → (f⁻¹ : D₂ → D₁) → (expr : FCC n D₁ i A) → ⟦ map-dim n f expr ⟧ₙ ⊆[ _∘ f ] ⟦ expr ⟧ₙ
  preserves-⊆ n f f⁻¹ (a -< cs >-) config =
    ⟦ map-dim n f (a -< cs >-) ⟧ₙ config
    ≡⟨⟩
    ⟦ a -< List.map (map-dim n f) cs >- ⟧ₙ config
    ≡⟨⟩
    artifact a (List.map (λ e → ⟦ e ⟧ₙ config) (List.map (map-dim n f) cs))
    ≡˘⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
    artifact a (List.map (λ e → ⟦ map-dim n f e ⟧ₙ config) cs)
    ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊆ n f f⁻¹ e config) cs) ⟩
    artifact a (List.map (λ e → ⟦ e ⟧ₙ (config ∘ f)) cs)
    ≡⟨⟩
    ⟦ a -< cs >- ⟧ₙ (config ∘ f)
    ∎
  preserves-⊆ n f f⁻¹ (d ⟨ cs ⟩) config =
    ⟦ map-dim n f (d ⟨ cs ⟩) ⟧ₙ config
    ≡⟨⟩
    ⟦ f d ⟨ Vec.map (map-dim n f) cs ⟩ ⟧ₙ config
    ≡⟨⟩
    ⟦ Vec.lookup (Vec.map (map-dim n f) cs) (config (f d)) ⟧ₙ config
    ≡⟨ Eq.cong₂ ⟦_⟧ₙ (Vec.lookup-map (config (f d)) (map-dim n f) cs) refl ⟩
    ⟦ map-dim n f (Vec.lookup cs (config (f d))) ⟧ₙ config
    ≡⟨ preserves-⊆ n f f⁻¹ (Vec.lookup cs (config (f d))) config ⟩
    ⟦ Vec.lookup cs (config (f d)) ⟧ₙ (config ∘ f)
    ≡⟨⟩
    ⟦ d ⟨ cs ⟩ ⟧ₙ (config ∘ f)
    ∎

  preserves-⊇ : {i : Size} → {D₁ D₂ A : Set} → (n : ℕ≥ 2) → (f : D₁ → D₂) → (f⁻¹ : D₂ → D₁) → f⁻¹ ∘ f ≗ id → (expr : FCC n D₁ i A) → ⟦ expr ⟧ₙ ⊆[ _∘ f⁻¹ ] ⟦ map-dim n f expr ⟧ₙ
  preserves-⊇ n f f⁻¹ is-inverse (a -< cs >-) config =
    ⟦ a -< cs >- ⟧ₙ config
    ≡⟨⟩
    artifact a (List.map (λ e → ⟦ e ⟧ₙ config) cs)
    ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊇ n f f⁻¹ is-inverse e config) cs) ⟩
    artifact a (List.map (λ e → ⟦ map-dim n f e ⟧ₙ (config ∘ f⁻¹)) cs)
    ≡⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
    artifact a (List.map (λ e → ⟦ e ⟧ₙ (config ∘ f⁻¹)) (List.map (map-dim n f) cs))
    ≡⟨⟩
    ⟦ a -< List.map (map-dim n f) cs >- ⟧ₙ (config ∘ f⁻¹)
    ≡⟨⟩
    ⟦ map-dim n f (a -< cs >-) ⟧ₙ (config ∘ f⁻¹)
    ∎
  preserves-⊇ n f f⁻¹ is-inverse (d ⟨ cs ⟩) config =
    ⟦ d ⟨ cs ⟩ ⟧ₙ config
    ≡⟨⟩
    ⟦ Vec.lookup cs (config d) ⟧ₙ config
    ≡⟨ preserves-⊇ n f f⁻¹ is-inverse (Vec.lookup cs (config d)) config ⟩
    ⟦ map-dim n f (Vec.lookup cs (config d)) ⟧ₙ (config ∘ f⁻¹)
    ≡˘⟨ Eq.cong₂ ⟦_⟧ₙ (Vec.lookup-map (config d) (map-dim n f) cs) refl ⟩
    ⟦ Vec.lookup (Vec.map (map-dim n f) cs) (config d) ⟧ₙ (config ∘ f⁻¹)
    ≡˘⟨ Eq.cong₂ ⟦_⟧ₙ (Eq.cong₂ Vec.lookup {x = Vec.map (map-dim n f) cs} refl (Eq.cong config (is-inverse d))) refl ⟩
    ⟦ Vec.lookup (Vec.map (map-dim n f) cs) (config ((f⁻¹ ∘ f) d)) ⟧ₙ (config ∘ f⁻¹)
    ≡⟨⟩
    ⟦ f d ⟨ Vec.map (map-dim n f) cs ⟩ ⟧ₙ (config ∘ f⁻¹)
    ≡⟨⟩
    ⟦ map-dim n f (d ⟨ cs ⟩) ⟧ₙ (config ∘ f⁻¹)
    ∎

  preserves : {i : Size} → {D₁ D₂ A : Set} → (n : ℕ≥ 2) → (f : D₁ → D₂) → (f⁻¹ : D₂ → D₁) → f⁻¹ ∘ f ≗ id → (e : FCC n D₁ i A) → ⟦ map-dim n f e ⟧ₙ ≅[ _∘ f ][ _∘ f⁻¹ ] ⟦ e ⟧ₙ
  preserves n f f⁻¹ is-inverse expr = preserves-⊆ n f f⁻¹ expr , preserves-⊇ n f f⁻¹ is-inverse expr

  FCC-map-dim : {i : Size} → {D₁ D₂ : Set} → (n : ℕ≥ 2) → (f : D₁ → D₂) → (f⁻¹ : D₂ → D₁) → f⁻¹ ∘ f ≗ id → LanguageCompiler (FCCL n D₁ Variant Artifact∈ₛVariant {i}) (FCCL n D₂ Variant Artifact∈ₛVariant {i})
  FCC-map-dim n f f⁻¹ is-inverse .LanguageCompiler.compile = map-dim n f
  FCC-map-dim n f f⁻¹ is-inverse .LanguageCompiler.config-compiler .to = _∘ f⁻¹
  FCC-map-dim n f f⁻¹ is-inverse .LanguageCompiler.config-compiler .from = _∘ f
  FCC-map-dim n f f⁻¹ is-inverse .LanguageCompiler.preserves e = ≅[]-sym (preserves n f f⁻¹ is-inverse e)

module IncreaseArity where
  module General where
    translate : {i : Size} → {D A : Set} → (n m : ℕ≥ 2) → n ℕ≥.≤ m → FCC n D i A → FCC m D i A
    translate n m n≤m (a -< cs >-) = a -< List.map (translate n m n≤m) cs >-
    translate (sucs n) m n≤m (d ⟨ cs ⟩) = d ⟨ Vec.saturate n≤m (Vec.map (translate (sucs n) m n≤m) cs) ⟩


    conf : {D : Set} → (n m : ℕ≥ 2) → n ℕ≥.≤ m → FCCꟲ n D → FCCꟲ m D
    conf (sucs n) (sucs m) n≤m config d = Fin.inject≤ (config d) n≤m

    fnoc : {D : Set} → (n m : ℕ≥ 2) → n ℕ≥.≤ m → FCCꟲ m D → FCCꟲ n D
    fnoc (sucs n) (sucs m) n≤m config d = ℕ≥.cappedFin (Fin.toℕ (config d))

    preserves-⊆ : ∀ {i : Size} {D A : Set} (n m : ℕ≥ 2)
      → (n≤m : n ℕ≥.≤ m)
      → (expr : FCC n D i A)
      → ⟦ translate n m n≤m expr ⟧ₙ ⊆[ fnoc n m n≤m ] ⟦ expr ⟧ₙ
    preserves-⊆ n m n≤m (a -< cs >-) config =
      ⟦ translate n m n≤m (a -< cs >-) ⟧ₙ config
      ≡⟨⟩
      ⟦ a -< List.map (translate n m n≤m) cs >- ⟧ₙ config
      ≡⟨⟩
      artifact a (List.map (λ e → ⟦ e ⟧ₙ config) (List.map (translate n m n≤m) cs))
      ≡˘⟨ Eq.cong₂ artifact Eq.refl (List.map-∘ cs) ⟩
      artifact a (List.map (λ e → ⟦ translate n m n≤m e ⟧ₙ config) cs)
      ≡⟨ Eq.cong₂ artifact Eq.refl (List.map-cong (λ e → preserves-⊆ n m n≤m e config) cs) ⟩
      artifact a (List.map (λ e → ⟦ e ⟧ₙ (fnoc n m n≤m config)) cs)
      ≡⟨⟩
      ⟦ a -< cs >- ⟧ₙ (fnoc n m n≤m config)
      ∎
    preserves-⊆ (sucs n) (sucs m) n≤m (d ⟨ cs ⟩) config =
      ⟦ translate (sucs n) (sucs m) n≤m (d ⟨ cs ⟩) ⟧ₙ config
      ≡⟨⟩
      ⟦ d ⟨ Vec.saturate n≤m (Vec.map (translate (sucs n) (sucs m) n≤m) cs) ⟩ ⟧ₙ config
      ≡⟨⟩
      ⟦ Vec.lookup (Vec.saturate n≤m (Vec.map (translate (sucs n) (sucs m) n≤m) cs)) (config d) ⟧ₙ config
      ≡⟨ Eq.cong₂ ⟦_⟧ₙ (Eq.cong₂ Vec.lookup (Vec.saturate-map n≤m (translate (sucs n) (sucs m) n≤m) cs) refl) refl ⟩
      ⟦ Vec.lookup (Vec.map (translate (sucs n) (sucs m) n≤m) (Vec.saturate n≤m cs)) (config d) ⟧ₙ config
      ≡⟨ Eq.cong₂ ⟦_⟧ₙ (Vec.lookup-map (config d) (translate (sucs n) (sucs m) n≤m) (Vec.saturate n≤m cs)) refl ⟩
      ⟦ (translate (sucs n) (sucs m) n≤m) (Vec.lookup (Vec.saturate n≤m cs) (config d)) ⟧ₙ config
      ≡⟨ preserves-⊆ (sucs n) (sucs m) n≤m (Vec.lookup (Vec.saturate n≤m cs) (config d)) config ⟩
      ⟦ Vec.lookup (Vec.saturate n≤m cs) (config d) ⟧ₙ (fnoc (sucs n) (sucs m) n≤m config)
      ≡⟨ Eq.cong₂ ⟦_⟧ₙ (Vec.lookup-saturate n≤m cs (config d)) refl ⟩
      ⟦ Vec.lookup cs (fnoc (sucs n) (sucs m) n≤m config d) ⟧ₙ (fnoc (sucs n) (sucs m) n≤m config)
      ≡⟨⟩
      ⟦ d ⟨ cs ⟩ ⟧ₙ (fnoc (sucs n) (sucs m) n≤m config)
      ∎

    preserves-⊇ : {i : Size} → {D A : Set} → (n m : ℕ≥ 2) → (n≤m : n ℕ≥.≤ m) → (expr : FCC n D i A) → ⟦ expr ⟧ₙ ⊆[ conf n m n≤m ] ⟦ translate n m n≤m expr ⟧ₙ
    preserves-⊇ n m n≤m (a -< cs >-) config =
      artifact a (List.map (λ e → ⟦ e ⟧ₙ config) cs)
      ≡⟨ Eq.cong₂ artifact Eq.refl (List.map-cong (λ e → preserves-⊇ n m n≤m e config) cs) ⟩
      artifact a (List.map (λ e → ⟦ translate n m n≤m e ⟧ₙ (conf n m n≤m config)) cs)
      ≡⟨ Eq.cong₂ artifact Eq.refl (List.map-∘ cs) ⟩
      ⟦ a -< List.map (translate n m n≤m) cs >- ⟧ₙ (conf n m n≤m config)
      ≡⟨⟩
      artifact a (List.map (λ e → ⟦ e ⟧ₙ (conf n m n≤m config)) (List.map (translate n m n≤m) cs))
      ∎
    preserves-⊇ (sucs n) (sucs m) n≤m (d ⟨ cs ⟩) config =
      ⟦ d ⟨ cs ⟩ ⟧ₙ config
      ≡⟨⟩
      ⟦ Vec.lookup cs (config d) ⟧ₙ config
      ≡˘⟨ Eq.cong₂ ⟦_⟧ₙ (Eq.cong₂ Vec.lookup (refl {x = cs}) (ℕ≥.cappedFin-toℕ (config d))) refl ⟩
      ⟦ Vec.lookup cs (ℕ≥.cappedFin (Fin.toℕ (config d))) ⟧ₙ config
      ≡˘⟨ Eq.cong₂ ⟦_⟧ₙ (Eq.cong₂ Vec.lookup (refl {x = cs}) (Eq.cong ℕ≥.cappedFin (Fin.toℕ-inject≤ (config d) n≤m))) refl ⟩
      ⟦ Vec.lookup cs (ℕ≥.cappedFin (Fin.toℕ (Fin.inject≤ (config d) n≤m))) ⟧ₙ config
      ≡˘⟨ Eq.cong₂ ⟦_⟧ₙ (Vec.lookup-saturate n≤m cs (Fin.inject≤ (config d) n≤m)) refl ⟩
      ⟦ Vec.lookup (Vec.saturate n≤m cs) (Fin.inject≤ (config d) n≤m) ⟧ₙ config
      ≡⟨⟩
      ⟦ Vec.lookup (Vec.saturate n≤m cs) (conf (sucs n) (sucs m) n≤m config d) ⟧ₙ config
      ≡⟨ preserves-⊇ (sucs n) (sucs m) n≤m (Vec.lookup (Vec.saturate n≤m cs) (conf (sucs n) (sucs m) n≤m config d)) config ⟩
      ⟦ (translate (sucs n) (sucs m) n≤m) (Vec.lookup (Vec.saturate n≤m cs) (conf (sucs n) (sucs m) n≤m config d)) ⟧ₙ (conf (sucs n) (sucs m) n≤m config)
      ≡˘⟨ Eq.cong₂ ⟦_⟧ₙ (Vec.lookup-map (conf (sucs n) (sucs m) n≤m config d) (translate (sucs n) (sucs m) n≤m) (Vec.saturate n≤m cs)) refl ⟩
      ⟦ Vec.lookup (Vec.map (translate (sucs n) (sucs m) n≤m) (Vec.saturate n≤m cs)) (conf (sucs n) (sucs m) n≤m config d) ⟧ₙ (conf (sucs n) (sucs m) n≤m config)
      ≡˘⟨ Eq.cong₂ ⟦_⟧ₙ (Eq.cong₂ Vec.lookup (Vec.saturate-map n≤m (translate (sucs n) (sucs m) n≤m) cs) refl) refl ⟩
      ⟦ Vec.lookup (Vec.saturate n≤m (Vec.map (translate (sucs n) (sucs m) n≤m) cs)) (conf (sucs n) (sucs m) n≤m config d) ⟧ₙ (conf (sucs n) (sucs m) n≤m config)
      ≡⟨⟩
      ⟦ d ⟨ Vec.saturate n≤m (Vec.map (translate (sucs n) (sucs m) n≤m) cs) ⟩ ⟧ₙ (conf (sucs n) (sucs m) n≤m config)
      ≡⟨⟩
      ⟦ translate (sucs n) (sucs m) n≤m (d ⟨ cs ⟩) ⟧ₙ (conf (sucs n) (sucs m) n≤m config)
      ∎

    preserves : {i : Size} → {D A : Set} → (n m : ℕ≥ 2) → (n≤m : n ℕ≥.≤ m) → (expr : FCC n D i A) → ⟦ translate n m n≤m expr ⟧ₙ ≅[ fnoc n m n≤m ][ conf n m n≤m ] ⟦ expr ⟧ₙ
    preserves n m n≤m expr = preserves-⊆ n m n≤m expr , preserves-⊇ n m n≤m expr

    FCC→FCC : {i : Size} → {D : Set} → (n m : ℕ≥ 2) → n ℕ≥.≤ m → LanguageCompiler (FCCL n D Variant Artifact∈ₛVariant {i}) (FCCL m D Variant Artifact∈ₛVariant {i})
    FCC→FCC n m n≤m .LanguageCompiler.compile = translate n m n≤m
    FCC→FCC n m n≤m .LanguageCompiler.config-compiler .to = conf n m n≤m
    FCC→FCC n m n≤m .LanguageCompiler.config-compiler .from = fnoc n m n≤m
    FCC→FCC n m n≤m .LanguageCompiler.preserves e = ≅[]-sym (preserves n m n≤m e)

  translate : {i : Size} → {D A : Set} → (n : ℕ≥ 2) → FCC (sucs zero) D i A → FCC n D i A
  translate (sucs n) = General.translate (sucs zero) (sucs n) (ℕ≥.lift≤ z≤n)

  conf : {D : Set} → (n : ℕ≥ 2) → FCCꟲ (sucs zero) D → FCCꟲ n D
  conf (sucs n) = General.conf (sucs zero) (sucs n) (ℕ≥.lift≤ z≤n)

  fnoc : {D : Set} → (n : ℕ≥ 2) → FCCꟲ n D → FCCꟲ (sucs zero) D
  fnoc (sucs n) = General.fnoc (sucs zero) (sucs n) (ℕ≥.lift≤ z≤n)

  preserves : {i : Size} → {D A : Set} → (n : ℕ≥ 2) → (expr : FCC (sucs zero) D i A) → ⟦ translate n expr ⟧ₙ ≅[ fnoc n ][ conf n ] ⟦ expr ⟧ₙ
  preserves (sucs n) = General.preserves (sucs zero) (sucs n) (ℕ≥.lift≤ z≤n)

  FCC→FCC : {i : Size} → {D : Set} → (n : ℕ≥ 2) → LanguageCompiler (FCCL (sucs zero) D Variant Artifact∈ₛVariant {i}) (FCCL n D Variant Artifact∈ₛVariant {i})
  FCC→FCC n .LanguageCompiler.compile = translate n
  FCC→FCC n .LanguageCompiler.config-compiler .to = conf n
  FCC→FCC n .LanguageCompiler.config-compiler .from = fnoc n
  FCC→FCC n .LanguageCompiler.preserves e = ≅[]-sym (preserves n e)


module DecreaseArity where
  IndexedDimension : Set → ℕ≥ 2 → Set
  IndexedDimension D n = D × Fin (ℕ≥.toℕ (ℕ≥.pred n))

  translate : {i : Size} → {D A : Set} → (n : ℕ≥ 2) → FCC n D i A → FCC (sucs zero) (IndexedDimension D n) ∞ A
  translate n (a -< cs >-) = a -< List.map (translate n) cs >-
  translate {i} {D} {A} (sucs n) (d ⟨ cs ⟩) = go n (ℕ.n<1+n n) cs
    module translate-Implementation where
    go : {i : Size} → (m : ℕ) → (m≤n : m < suc n) → Vec (FCC (sucs n) D i A) (suc (suc m)) → FCC (sucs zero) (D × Fin (suc n)) ∞ A
    go zero m≤n (l ∷ r ∷ []) = (d , Fin.opposite (Fin.fromℕ< {zero} m≤n)) ⟨ translate (sucs n) l ∷ translate (sucs n) r ∷ [] ⟩
    go (suc m) m≤n (c ∷ cs) = (d , Fin.opposite (Fin.fromℕ< {suc m} m≤n)) ⟨ translate (sucs n) c ∷ go m (<-trans (ℕ.n<1+n m) m≤n) cs ∷ [] ⟩


  conf : {D : Set} → (n : ℕ≥ 2) → FCCꟲ n D → FCCꟲ (sucs zero) (IndexedDimension D n)
  conf (sucs n) config (d , m) with config d Fin.≟ (Fin.inject₁ m)
  ... | yes _ = zero
  ... | no _ = suc zero

  fnoc : {D : Set} → (n : ℕ≥ 2) → FCCꟲ (sucs zero) (IndexedDimension D n) → FCCꟲ n D
  fnoc (sucs n) config d = go n (ℕ.n<1+n n)
    module fnoc-Implementation where
    go : (m : ℕ) → m < suc n → Fin (suc (suc n))
    go m m<n with config (d , Fin.opposite (Fin.fromℕ< {m} m<n))
    go m m<n | zero = Fin.inject₁ (Fin.opposite (Fin.fromℕ< {m} m<n))
    go zero m<n | suc zero = Fin.fromℕ (suc n)
    go (suc m) m<n | suc zero = go m (<-trans (ℕ.n<1+n m) m<n)

  -- TODO move out of top-level
  config≡0 : {D : Set} → {d : D} → {n : ℕ} → (config : FCCꟲ (sucs zero) (D × Fin (suc n))) → (j : Fin (suc n)) → fnoc (sucs n) config d ≡ Fin.inject₁ j → config (d , j) ≡ zero
  config≡0 {d = d} {n = n} config j config≡j = go' n (ℕ.n<1+n n) config≡j
    where
    open fnoc-Implementation

    go' : (m : ℕ) → (m<n : m < suc n) → go n config d m m<n ≡ Fin.inject₁ j → config (d , j) ≡ zero
    go' m m<n go≡j with config (d , Fin.opposite (Fin.fromℕ< {m} m<n)) in config-opposite-m
    go' m m<n go≡j | zero = Eq.trans (Eq.cong config (Eq.cong₂ _,_ refl (Eq.sym (Fin.inject₁-injective go≡j)))) config-opposite-m
    go' zero m<n go≡j | suc zero = ⊥-elim (Fin.toℕ-inject₁-≢ j (Eq.trans (Eq.sym (Fin.toℕ-fromℕ (suc n))) (Eq.cong Fin.toℕ go≡j)))
    go' (suc m) m<n go≡j | suc zero = go' m (<-trans (ℕ.n<1+n m) m<n) go≡j

  config≡1 : {D : Set} → {d : D} → {n : ℕ} → (config : FCCꟲ (sucs zero) (D × Fin (suc n))) → (j : Fin (suc n)) → j Fin.< fnoc (sucs n) config d → config (d , j) ≡ suc zero
  config≡1 {d = d} {n = n} config j config<j = go' n (ℕ.n<1+n n) config<j (λ k<opposite-n → ⊥-elim (ℕ.n≮0 (≤-trans k<opposite-n (≤-reflexive (Eq.trans (Fin.opposite-prop (Fin.fromℕ< (ℕ.n<1+n n))) (Eq.trans (Eq.cong₂ _∸_ refl (Fin.toℕ-fromℕ< (ℕ.n<1+n n))) (ℕ.n∸n≡0 n)))))))
    where
    open fnoc-Implementation

    extend-∀config≡1
      : {m : ℕ}
      → (m<n : suc m < suc n)
      → config (d , Fin.opposite (Fin.fromℕ< {suc m} m<n)) ≡ suc zero
      → (∀ {k} → k Fin.< Fin.opposite (Fin.fromℕ< {suc m}                    m<n ) → config (d , k) ≡ suc zero)
      → (∀ {k} → k Fin.< Fin.opposite (Fin.fromℕ< {    m} (<-trans (ℕ.n<1+n m) m<n)) → config (d , k) ≡ suc zero)
    extend-∀config≡1 {m} m<n config≡1 ∀config≡1 {k} m<k with k Fin.≟ Fin.opposite (Fin.fromℕ< {suc m} m<n)
    ... | yes k≡m = Eq.trans (Eq.cong config (Eq.cong₂ _,_ refl k≡m)) config≡1
    ... | no k≢m = ∀config≡1 (ℕ.≤∧≢⇒< (ℕ.≤-pred (≤-trans m<k (≤-reflexive (Eq.trans (Fin.opposite-prop (Fin.fromℕ< (<-trans (s≤s ≤-refl) m<n))) (Eq.trans (Eq.cong₂ _∸_ refl (Fin.toℕ-fromℕ< (<-trans (s≤s ≤-refl) m<n))) (Eq.trans (ℕ.+-∸-assoc 1 (ℕ.≤-pred m<n)) (Eq.cong suc (Eq.sym (Eq.trans (Fin.opposite-prop (Fin.fromℕ< m<n)) (Eq.cong₂ _∸_ refl (Fin.toℕ-fromℕ< m<n))))))))))) (k≢m ∘ Fin.toℕ-injective))

    go' : (m : ℕ) → (m<n : m < suc n) → j Fin.< go n config d m m<n → (∀ {k : Fin (suc n)} → k Fin.< Fin.opposite (Fin.fromℕ< {m} m<n) → config (d , k) ≡ suc zero) → config (d , j) ≡ suc zero
    go' m m<n j<go ∀config≡1 with config (d , Fin.opposite (Fin.fromℕ< {m} m<n)) in config-opposite-m
    go' m m<n j<go ∀config≡1 | zero with Fin.opposite (Fin.fromℕ< {m} m<n) Fin.≤? j
    go' m m<n j<go ∀config≡1 | zero | yes m≤j = ⊥-elim (ℕ.n≮n (Fin.toℕ j) (≤-trans j<go (≤-trans (≤-reflexive (Fin.toℕ-inject₁ (Fin.opposite (Fin.fromℕ< m<n)))) m≤j)))
    go' m m<n j<go ∀config≡1 | zero | no m≰j = ∀config≡1 (ℕ.≰⇒> m≰j)
    go' m m<n j<go ∀config≡1 | suc zero with j Fin.≟ Fin.opposite (Fin.fromℕ< {m} m<n)
    go' m m<n j<go ∀config≡1 | suc zero | yes j≡m = Eq.trans (Eq.cong config (Eq.cong₂ _,_ refl j≡m)) config-opposite-m
    go' zero m<n j<go ∀config≡1 | suc zero | no j≢m = ∀config≡1 (ℕ.≤∧≢⇒< (≤-trans (ℕ.≤-pred (Fin.toℕ<n j)) (≤-reflexive (Eq.sym (Eq.trans (Fin.opposite-prop (Fin.fromℕ< m<n)) (Eq.cong₂ _∸_ refl (Fin.toℕ-fromℕ< m<n)))))) (j≢m ∘ Fin.toℕ-injective))
    go' (suc m) m<n j<go ∀config≡1 | suc zero | no j≢m = go' m (<-trans (ℕ.n<1+n m) m<n) j<go (extend-∀config≡1 {m = m} m<n config-opposite-m ∀config≡1)

  preserves-⊆ : {i : Size} {D A : Set} → (n : ℕ≥ 2) → (expr : FCC n D i A) → ⟦ translate n expr ⟧ₙ ⊆[ fnoc n ] ⟦ expr ⟧ₙ
  preserves-⊆ (sucs n) (a -< cs >-) config =
    ⟦ translate (sucs n) (a -< cs >-) ⟧ₙ config
    ≡⟨⟩
    ⟦ a -< List.map (translate (sucs n)) cs >- ⟧ₙ config
    ≡⟨⟩
    artifact a (List.map (λ e → ⟦ e ⟧ₙ config) (List.map (translate (sucs n)) cs))
    ≡˘⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
    artifact a (List.map (λ e → ⟦ translate (sucs n) e ⟧ₙ config) cs)
    ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊆ (sucs n) e config) cs) ⟩
    artifact a (List.map (λ e → ⟦ e ⟧ₙ (fnoc (sucs n) config)) cs)
    ≡⟨⟩
    ⟦ a -< cs >- ⟧ₙ (fnoc (sucs n) config)
    ∎
  preserves-⊆ {D = D} {A = A} (sucs n) (d ⟨ cs ⟩) config =
    ⟦ translate (sucs n) (d ⟨ cs ⟩) ⟧ₙ config
    ≡⟨ lemma n (ℕ.n<1+n n) cs (fnoc (sucs n) config d) (ℕ.+-comm n (Fin.toℕ (fnoc (sucs n) config d))) ⟩
    ⟦ Vec.lookup cs (fnoc (sucs n) config d) ⟧ₙ (fnoc (sucs n) config)
    ≡⟨⟩
    ⟦ d ⟨ cs ⟩ ⟧ₙ (fnoc (sucs n) config)
    ∎
    where
    open translate-Implementation

    lemma
      : {i : Size}
      → (m : ℕ)
      → (m≤n : m < suc n)
      → (cs' : Vec (FCC (sucs n) D i A) (suc (suc m)))
      → (j : Fin (suc (suc m)))
      → m + Fin.toℕ (fnoc (sucs n) config d) ≡ Fin.toℕ j + n
      → ⟦ go n d cs m m≤n cs' ⟧ₙ config ≡ ⟦ Vec.lookup cs' j ⟧ₙ (fnoc (sucs n) config)
    lemma zero m≤n (l ∷ r ∷ []) zero m+config-d≡j+n =
      ⟦ go n d cs zero m≤n (l ∷ r ∷ []) ⟧ₙ config
      ≡⟨⟩
      ⟦ (d , Fin.opposite (Fin.fromℕ< {zero} m≤n)) ⟨ translate (sucs n) l ∷ translate (sucs n) r ∷ [] ⟩ ⟧ₙ config
      ≡⟨⟩
      ⟦ Vec.lookup (translate (sucs n) l ∷ translate (sucs n) r ∷ []) (config (d , Fin.opposite (Fin.fromℕ< {zero} m≤n))) ⟧ₙ config
      ≡⟨ Eq.cong₂ ⟦_⟧ₙ (Eq.cong₂ Vec.lookup {x = translate (sucs n) l ∷ translate (sucs n) r ∷ []} refl (config≡0 config (Fin.opposite (Fin.fromℕ< m≤n)) (Fin.toℕ-injective (Eq.trans m+config-d≡j+n (Eq.trans (Eq.sym (Fin.toℕ-fromℕ n)) (Eq.trans (Eq.cong Fin.toℕ (Eq.cong Fin.opposite (Eq.sym (Fin.fromℕ<-toℕ zero m≤n)))) (Eq.sym (Fin.toℕ-inject₁ (Fin.opposite (Fin.fromℕ< m≤n)))))))))) refl ⟩
      ⟦ Vec.lookup (translate (sucs n) l ∷ translate (sucs n) r ∷ []) zero ⟧ₙ config
      ≡⟨⟩
      ⟦ translate (sucs n) l ⟧ₙ config
      ≡⟨ preserves-⊆ (sucs n) l config ⟩
      ⟦ l ⟧ₙ (fnoc (sucs n) config)
      ∎
    lemma zero m≤n (l ∷ r ∷ []) (suc zero) m+config-d≡j+n =
      ⟦ (d , Fin.opposite (Fin.fromℕ< m≤n)) ⟨ translate (sucs n) l ∷ translate (sucs n) r ∷ [] ⟩ ⟧ₙ config
      ≡⟨⟩
      ⟦ Vec.lookup (translate (sucs n) l ∷ translate (sucs n) r ∷ []) (config (d , Fin.opposite (Fin.fromℕ< m≤n))) ⟧ₙ config
      ≡⟨ Eq.cong₂ ⟦_⟧ₙ (Eq.cong₂ Vec.lookup {x = translate (sucs n) l ∷ translate (sucs n) r ∷ []} refl (config≡1 config (Fin.opposite (Fin.fromℕ< m≤n))
        (let module ≤ = ℕ.≤-Reasoning in
          ≤.begin-strict
          Fin.toℕ (Fin.opposite (Fin.fromℕ< m≤n))
          ≤.≡⟨ Fin.opposite-prop (Fin.fromℕ< m≤n) ⟩
          n ∸ Fin.toℕ (Fin.fromℕ< m≤n)
          ≤.≡⟨ Eq.cong₂ _∸_ refl (Fin.toℕ-fromℕ< m≤n) ⟩
          n
          ≤.<⟨ ℕ.n<1+n n ⟩
          suc n
          ≤.≡˘⟨ m+config-d≡j+n ⟩
          Fin.toℕ (fnoc (sucs n) config d)
          ≤.∎
        ))) refl ⟩
      ⟦ translate (sucs n) r ⟧ₙ config
      ≡⟨ preserves-⊆ (sucs n) r config ⟩
      ⟦ r ⟧ₙ (fnoc (sucs n) config)
      ∎
    lemma (suc m) m≤n (c ∷ cs') zero m+config-d≡j+n =
      ⟦ (d , Fin.opposite (Fin.fromℕ< m≤n)) ⟨ translate (sucs n) c ∷ go n d cs m (<-trans (ℕ.n<1+n m) m≤n) cs' ∷ [] ⟩ ⟧ₙ config
      ≡⟨ Eq.cong₂ ⟦_⟧ₙ (Eq.cong₂ Vec.lookup {x = translate (sucs n) c ∷ go n d cs m (<-trans (ℕ.n<1+n m) m≤n) cs' ∷ []} refl (config≡0 config (Fin.opposite (Fin.fromℕ< {suc m} m≤n)) (Fin.toℕ-injective (
          Fin.toℕ (fnoc (sucs n) config d)
          ≡˘⟨ ℕ.m+n∸m≡n (suc m) (Fin.toℕ (fnoc (sucs n) config d)) ⟩
          suc m + Fin.toℕ (fnoc (sucs n) config d) ∸ suc m
          ≡⟨ Eq.cong (λ n → n ∸ suc m) m+config-d≡j+n ⟩
          n ∸ suc m
          ≡˘⟨ Eq.cong₂ _∸_ refl (Fin.toℕ-fromℕ< m≤n) ⟩
          n ∸ (Fin.toℕ (Fin.fromℕ< m≤n))
          ≡˘⟨ Fin.opposite-prop (Fin.fromℕ< m≤n) ⟩
          Fin.toℕ (Fin.opposite (Fin.fromℕ< m≤n))
          ≡˘⟨ Fin.toℕ-inject₁ (Fin.opposite (Fin.fromℕ< m≤n)) ⟩
          Fin.toℕ (Fin.inject₁ (Fin.opposite (Fin.fromℕ< m≤n)))
          ∎
        )))) refl ⟩
      ⟦ translate (sucs n) c ⟧ₙ config
      ≡⟨ preserves-⊆ (sucs n) c config ⟩
      ⟦ c ⟧ₙ (fnoc (sucs n) config)
      ∎
    lemma (suc m) (s≤s m≤n) (c ∷ cs') (suc j) m+config-d≡j+n =
      ⟦ (d , Fin.opposite (Fin.fromℕ< (s≤s m≤n))) ⟨ translate (sucs n) c ∷ go n d cs m (<-trans (ℕ.n<1+n m) (s≤s m≤n)) cs' ∷ [] ⟩ ⟧ₙ config
      ≡⟨ Eq.cong₂ ⟦_⟧ₙ (Eq.cong₂ Vec.lookup {x = translate (sucs n) c ∷ go n d cs m (<-trans (ℕ.n<1+n m) (s≤s m≤n)) cs' ∷ []} refl (config≡1 config (Fin.opposite (Fin.fromℕ< (s≤s m≤n)))
        (let module ≤ = ℕ.≤-Reasoning in
          ≤.begin-strict
          Fin.toℕ (Fin.inject₁ (Fin.opposite (Fin.fromℕ< m≤n)))
          ≤.≡⟨ Fin.toℕ-inject₁ (Fin.opposite (Fin.fromℕ< m≤n)) ⟩
          Fin.toℕ (Fin.opposite (Fin.fromℕ< m≤n))
          ≤.≡⟨ Fin.opposite-prop (Fin.fromℕ< m≤n) ⟩
          n ∸ suc (Fin.toℕ (Fin.fromℕ< m≤n))
          ≤.≡⟨ Eq.cong₂ _∸_ {x = n} refl (Eq.cong suc (Fin.toℕ-fromℕ< m≤n)) ⟩
          n ∸ suc m
          ≤.<⟨ ℕ.m≤n⇒m≤o+n (Fin.toℕ j) (ℕ.m∸n≢0⇒n<m (ℕ.m>n⇒m∸n≢0 (ℕ.n∸1+m<n∸m m≤n))) ⟩
          Fin.toℕ j + (n ∸ m)
          ≤.≡˘⟨ ℕ.+-∸-assoc (Fin.toℕ j) (ℕ.≤-pred (ℕ.m≤n⇒m≤1+n m≤n)) ⟩
          Fin.toℕ j + n ∸ m
          ≤.≡⟨⟩
          suc (Fin.toℕ j + n) ∸ suc m
          ≤.≡˘⟨ Eq.cong (λ n → n ∸ suc m) m+config-d≡j+n ⟩
          suc m + Fin.toℕ (fnoc (sucs n) config d) ∸ suc m
          ≤.≡⟨ ℕ.m+n∸m≡n (suc m) (Fin.toℕ (fnoc (sucs n) config d)) ⟩
          Fin.toℕ (fnoc (sucs n) config d)
          ≤.∎
        ))) refl ⟩
      ⟦ go n d cs m (<-trans (ℕ.n<1+n m) (s≤s m≤n)) cs' ⟧ₙ config
      ≡⟨ lemma m (<-trans (ℕ.n<1+n m) (s≤s m≤n)) cs' j (ℕ.suc-injective m+config-d≡j+n) ⟩
      ⟦ Vec.lookup cs' j ⟧ₙ (fnoc (sucs n) config)
      ∎

  preserves-⊇ : {i : Size} → {D A : Set} → (n : ℕ≥ 2) → (expr : FCC n D i A) → ⟦ expr ⟧ₙ ⊆[ conf n ] ⟦ translate n expr ⟧ₙ
  preserves-⊇ (sucs n) (a -< cs >-) config =
    ⟦ a -< cs >- ⟧ₙ config
    ≡⟨⟩
    artifact a (List.map (λ e → ⟦ e ⟧ₙ config) cs)
    ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊇ (sucs n) e config) cs) ⟩
    artifact a (List.map (λ z → ⟦ translate (sucs n) z ⟧ₙ (conf (sucs n) config)) cs)
    ≡⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
    artifact a (List.map (λ e → ⟦ e ⟧ₙ (conf (sucs n) config)) (List.map (translate (sucs n)) cs))
    ≡⟨⟩
    ⟦ translate (sucs n) (a -< cs >-) ⟧ₙ (conf (sucs n) config)
    ∎
  preserves-⊇ {D = D} {A = A} (sucs n) (d ⟨ cs ⟩) config =
    ⟦ d ⟨ cs ⟩ ⟧ₙ config
    ≡⟨⟩
    ⟦ Vec.lookup cs (config d) ⟧ₙ config
    ≡˘⟨ lemma n (ℕ.n<1+n n) cs (config d) (ℕ.+-comm n (Fin.toℕ (config d))) ⟩
    ⟦ translate (sucs n) (d ⟨ cs ⟩) ⟧ₙ (conf (sucs n) config)
    ∎
    where
    open translate-Implementation

    config≡0' : {D : Set} → {d : D} → {n : ℕ} → (config : FCCꟲ (sucs n) D) → (j : Fin (suc n)) → config d ≡ (Fin.inject₁ j) → conf (sucs n) config (d , j) ≡ zero
    config≡0' {d = d} config j config-d≡j with config d Fin.≟ (Fin.inject₁ j)
    ... | yes _ = refl
    ... | no config-d≢j = ⊥-elim (config-d≢j config-d≡j)

    config≡1' : {D : Set} → {d : D} → {n : ℕ} → (config : FCCꟲ (sucs n) D) → (j : Fin (suc n)) → config d ≢ (Fin.inject₁ j) → conf (sucs n) config (d , j) ≡ suc zero
    config≡1' {d = d} config j config-d≢j with config d Fin.≟ (Fin.inject₁ j)
    ... | yes config-d≡j = ⊥-elim (config-d≢j config-d≡j)
    ... | no _ = refl

    lemma
      : {i : Size}
      → (m : ℕ)
      → (m≤n : m < suc n)
      → (cs' : Vec (FCC (sucs n) D i A) (suc (suc m)))
      → (j : Fin (suc (suc m)))
      → m + Fin.toℕ (config d) ≡ Fin.toℕ j + n
      → ⟦ go n d cs m m≤n cs' ⟧ₙ (conf (sucs n) config) ≡ ⟦ Vec.lookup cs' j ⟧ₙ config
    lemma zero m≤n (l ∷ r ∷ []) zero m+config-d≡j+n =
      ⟦ go n d cs zero m≤n (l ∷ r ∷ []) ⟧ₙ (conf (sucs n) config)
      ≡⟨⟩
      ⟦ (d , Fin.opposite (Fin.fromℕ< {zero} m≤n)) ⟨ translate (sucs n) l ∷ translate (sucs n) r ∷ [] ⟩ ⟧ₙ (conf (sucs n) config)
      ≡⟨⟩
      ⟦ Vec.lookup (translate (sucs n) l ∷ translate (sucs n) r ∷ []) (conf (sucs n) config (d , Fin.opposite (Fin.fromℕ< {zero} m≤n))) ⟧ₙ (conf (sucs n) config)
      ≡⟨ Eq.cong₂ ⟦_⟧ₙ (Eq.cong₂ Vec.lookup {x = translate (sucs n) l ∷ translate (sucs n) r ∷ []} refl (config≡0' config (Fin.opposite (Fin.fromℕ< m≤n)) (Fin.toℕ-injective (
          Fin.toℕ (config d)
          ≡⟨ m+config-d≡j+n ⟩
          n
          ≡˘⟨ Fin.toℕ-fromℕ n ⟩
          Fin.toℕ (Fin.fromℕ n)
          ≡⟨ Eq.cong Fin.toℕ (Eq.cong Fin.opposite (Eq.sym (Fin.fromℕ<-toℕ zero m≤n))) ⟩
          Fin.toℕ (Fin.opposite (Fin.fromℕ< m≤n))
          ≡˘⟨ Fin.toℕ-inject₁ (Fin.opposite (Fin.fromℕ< m≤n)) ⟩
          Fin.toℕ (Fin.inject₁ (Fin.opposite (Fin.fromℕ< m≤n)))
          ∎
        )))) refl ⟩
      ⟦ Vec.lookup (translate (sucs n) l ∷ translate (sucs n) r ∷ []) zero ⟧ₙ (conf (sucs n) config)
      ≡⟨⟩
      ⟦ translate (sucs n) l ⟧ₙ (conf (sucs n) config)
      ≡˘⟨ preserves-⊇ (sucs n) l config ⟩
      ⟦ l ⟧ₙ config
      ∎
    lemma zero m≤n (l ∷ r ∷ []) (suc zero) m+config-d≡j+n =
      ⟦ (d , Fin.opposite (Fin.fromℕ< m≤n)) ⟨ translate (sucs n) l ∷ translate (sucs n) r ∷ [] ⟩ ⟧ₙ (conf (sucs n) config)
      ≡⟨⟩
      ⟦ Vec.lookup (translate (sucs n) l ∷ translate (sucs n) r ∷ []) (conf (sucs n) config (d , Fin.opposite (Fin.fromℕ< m≤n))) ⟧ₙ (conf (sucs n) config)
      ≡⟨ Eq.cong₂ ⟦_⟧ₙ (Eq.cong₂ Vec.lookup {x = translate (sucs n) l ∷ translate (sucs n) r ∷ []} refl (config≡1' config (Fin.opposite (Fin.fromℕ< m≤n)) (λ config-d≡opposite-m → ℕ.1+n≢n (
          suc n
          ≡˘⟨ m+config-d≡j+n ⟩
          Fin.toℕ (config d)
          ≡⟨ Eq.cong Fin.toℕ config-d≡opposite-m ⟩
          Fin.toℕ (Fin.inject₁ (Fin.opposite (Fin.fromℕ< m≤n)))
          ≡⟨ Fin.toℕ-inject₁ (Fin.opposite (Fin.fromℕ< m≤n)) ⟩
          Fin.toℕ (Fin.opposite (Fin.fromℕ< m≤n))
          ≡⟨ Fin.opposite-prop (Fin.fromℕ< m≤n) ⟩
          n ∸ Fin.toℕ (Fin.fromℕ< m≤n)
          ≡⟨ Eq.cong₂ _∸_ refl (Fin.toℕ-fromℕ< m≤n) ⟩
          n ∸ zero
          ≡⟨⟩
          n
          ∎
        )))) refl ⟩
      ⟦ translate (sucs n) r ⟧ₙ (conf (sucs n) config)
      ≡˘⟨ preserves-⊇ (sucs n) r config ⟩
      ⟦ r ⟧ₙ config
      ∎
    lemma (suc m) m≤n (c ∷ cs') zero m+config-d≡j+n =
      ⟦ (d , Fin.opposite (Fin.fromℕ< m≤n)) ⟨ translate (sucs n) c ∷ go n d cs m (<-trans (ℕ.n<1+n m) m≤n) cs' ∷ [] ⟩ ⟧ₙ (conf (sucs n) config)
      ≡⟨ Eq.cong₂ ⟦_⟧ₙ (Eq.cong₂ Vec.lookup {x = translate (sucs n) c ∷ go n d cs m (<-trans (ℕ.n<1+n m) m≤n) cs' ∷ []} refl (config≡0' config (Fin.opposite (Fin.fromℕ< m≤n)) (Fin.toℕ-injective (
          Fin.toℕ (config d)
          ≡˘⟨ ℕ.m+n∸m≡n (suc m) (Fin.toℕ (config d)) ⟩
          suc m + Fin.toℕ (config d) ∸ suc m
          ≡⟨ Eq.cong (λ n → n ∸ suc m) m+config-d≡j+n ⟩
          n ∸ suc m
          ≡˘⟨ Eq.cong₂ _∸_ refl (Fin.toℕ-fromℕ< m≤n) ⟩
          n ∸ (Fin.toℕ (Fin.fromℕ< m≤n))
          ≡˘⟨ Fin.opposite-prop (Fin.fromℕ< m≤n) ⟩
          Fin.toℕ (Fin.opposite (Fin.fromℕ< m≤n))
          ≡˘⟨ Fin.toℕ-inject₁ (Fin.opposite (Fin.fromℕ< m≤n)) ⟩
          Fin.toℕ (Fin.inject₁ (Fin.opposite (Fin.fromℕ< m≤n)))
          ∎
        )))) refl ⟩
      ⟦ translate (sucs n) c ⟧ₙ (conf (sucs n) config)
      ≡˘⟨ preserves-⊇ (sucs n) c config ⟩
      ⟦ c ⟧ₙ config
      ∎
    lemma (suc m) (s≤s m≤n) (c ∷ cs') (suc j) m+config-d≡j+n =
      ⟦ (d , Fin.opposite (Fin.fromℕ< (s≤s m≤n))) ⟨ translate (sucs n) c ∷ go n d cs m (<-trans (ℕ.n<1+n m) (s≤s m≤n)) cs' ∷ [] ⟩ ⟧ₙ (conf (sucs n) config)
      ≡⟨ Eq.cong₂ ⟦_⟧ₙ (Eq.cong₂ Vec.lookup {x = translate (sucs n) c ∷ go n d cs m (<-trans (ℕ.n<1+n m) (s≤s m≤n)) cs' ∷ []} refl (config≡1' config (Fin.opposite (Fin.fromℕ< (s≤s m≤n)))
        (λ config-d≡opposite-m → (ℕ.<⇒≢ (ℕ.m≤n⇒m≤o+n (Fin.toℕ j) (ℕ.m∸n≢0⇒n<m (ℕ.m>n⇒m∸n≢0 (ℕ.n∸1+m<n∸m m≤n))))) (
          n ∸ suc m
          ≡˘⟨ Eq.cong₂ _∸_ {x = n} refl (Eq.cong suc (Fin.toℕ-fromℕ< m≤n)) ⟩
          n ∸ suc (Fin.toℕ (Fin.fromℕ< m≤n))
          ≡˘⟨ Fin.opposite-prop (Fin.fromℕ< m≤n) ⟩
          Fin.toℕ (Fin.opposite (Fin.fromℕ< m≤n))
          ≡˘⟨ Fin.toℕ-inject₁ (Fin.opposite (Fin.fromℕ< m≤n)) ⟩
          Fin.toℕ (Fin.inject₁ (Fin.opposite (Fin.fromℕ< m≤n)))
          ≡˘⟨ Fin.toℕ-inject₁ (Fin.inject₁ (Fin.opposite (Fin.fromℕ< m≤n))) ⟩
          Fin.toℕ (Fin.inject₁ (Fin.inject₁ (Fin.opposite (Fin.fromℕ< m≤n))))
          ≡˘⟨ Eq.cong Fin.toℕ config-d≡opposite-m ⟩
          Fin.toℕ (config d)
          ≡˘⟨ ℕ.m+n∸m≡n (suc m) (Fin.toℕ (config d)) ⟩
          suc m + Fin.toℕ (config d) ∸ suc m
          ≡⟨⟩
          m + Fin.toℕ (config d) ∸ m
          ≡⟨ Eq.cong (λ n → n ∸ suc m) m+config-d≡j+n ⟩
          Fin.toℕ j + n ∸ m
          ≡⟨ ℕ.+-∸-assoc (Fin.toℕ j) (ℕ.≤-pred (ℕ.m≤n⇒m≤1+n m≤n)) ⟩
          Fin.toℕ j + (n ∸ m)
          ∎
        )))) refl ⟩
      ⟦ go n d cs m (<-trans (ℕ.n<1+n m) (s≤s m≤n)) cs' ⟧ₙ (conf (sucs n) config)
      ≡⟨ lemma m (<-trans (ℕ.n<1+n m) (s≤s m≤n)) cs' j (ℕ.suc-injective m+config-d≡j+n) ⟩
      ⟦ Vec.lookup cs' j ⟧ₙ config
      ∎

  preserves : {i : Size} → {D A : Set} → (n : ℕ≥ 2) → (expr : FCC n D i A) → ⟦ translate n expr ⟧ₙ ≅[ fnoc n ][ conf n ] ⟦ expr ⟧ₙ
  preserves n expr = preserves-⊆ n expr , preserves-⊇ n expr

  FCC→FCC : {i : Size} → {D : Set} → (n : ℕ≥ 2) → LanguageCompiler (FCCL n D Variant Artifact∈ₛVariant {i}) (FCCL (sucs zero) (D × Fin (ℕ≥.toℕ (ℕ≥.pred n))) Variant Artifact∈ₛVariant)
  FCC→FCC n .LanguageCompiler.compile = translate n
  FCC→FCC n .LanguageCompiler.config-compiler .to = conf n
  FCC→FCC n .LanguageCompiler.config-compiler .from = fnoc n
  FCC→FCC n .LanguageCompiler.preserves e = ≅[]-sym (preserves n e)


open DecreaseArity using (IndexedDimension) public

conf : {D : Set} → (n m : ℕ≥ 2) → FCCꟲ n D → FCCꟲ m (IndexedDimension D n)
conf n m = IncreaseArity.conf m ∘ DecreaseArity.conf n

fnoc : {D : Set} → (n m : ℕ≥ 2) → FCCꟲ m (IndexedDimension D n) → FCCꟲ n D
fnoc n m = DecreaseArity.fnoc n ∘ IncreaseArity.fnoc m

translate : {i : Size} → {D A : Set} → (n m : ℕ≥ 2) → FCC n D i A → FCC m (IndexedDimension D n) ∞ A
translate (sucs n) (sucs m) expr = IncreaseArity.translate (sucs m) (DecreaseArity.translate (sucs n) expr)

preserves : {i : Size} → {D A : Set} → (n m : ℕ≥ 2) → (expr : FCC n D i A) → ⟦ translate n m expr ⟧ₙ ≅[ fnoc n m ][ conf n m ] ⟦ expr ⟧ₙ
preserves (sucs n) (sucs m) expr = ≅[]-trans (IncreaseArity.preserves (sucs m) (DecreaseArity.translate (sucs n) expr)) (DecreaseArity.preserves (sucs n) expr)

FCC→FCC : {i : Size} → {D : Set} → (n m : ℕ≥ 2) → LanguageCompiler (FCCL n D Variant Artifact∈ₛVariant {i}) (FCCL m (D × Fin (ℕ≥.toℕ (ℕ≥.pred n))) Variant Artifact∈ₛVariant)
FCC→FCC n m .LanguageCompiler.compile = translate n m
FCC→FCC n m .LanguageCompiler.config-compiler .to = conf n m
FCC→FCC n m .LanguageCompiler.config-compiler .from = fnoc n m
FCC→FCC n m .LanguageCompiler.preserves e = ≅[]-sym (preserves n m e)
