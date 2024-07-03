module Framework.Definitions where

open import Data.Maybe using (Maybe; just)
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂) renaming (_,_ to _and_)
open import Data.Unit using (⊤; tt) public
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl)
open import Relation.Binary using (DecidableEquality)
open import Relation.Nullary.Negation using (¬_)

-- open import Level using (suc; _⊔_)

{-
Some Atomic Data.
Any type can be used as atomic data in variants as long as
we can decide equality.
Our framework as well as most variability language actually
do not require decidable equality but a few variability languages
require it (e.g., feature structure trees).
We decided to include the assumption that equality is decidable into
the core definitions because it is quite reasonable.
Any actual data we can think of to plug in here (e.g., strings, tokens or
nodes of an abstract syntax tree) can be checked for equality.
-}
𝔸 : Set₁
𝔸 = Σ Set DecidableEquality

-- retrieve the set of atoms from an atom type 𝔸
atoms : 𝔸 → Set
atoms = proj₁

{-
Variant Language.
A variant should represent atomic data in some way so its parameterized in atomic data.
In our paper, this type is fixed to rose trees (see Framework.Variants.agda).
-}
𝕍 : Set₂
𝕍 = 𝔸 → Set₁

{-
Annotation Language.
This can be names or propositional formulas or whatever you like to annotate artifacts with.
We have no assumptions on this kind of language (yet).
In the future, it might be interesting to dig deeper into 𝔽 and to explore its impact on a
language's expressiveness more deeply.
-}
𝔽 : Set₁
𝔽 = Set

{-
Feature Selection Language.
This is the semantics of an annotation language 𝔽. An instance of 𝕊 describes the
set of configurations for a feature language 𝔽.  Usually, each feature selection
language `S : 𝕊` has a some function `ConfigEvaluater F S Sel` which resolves an
expression of the annotation language `F : 𝔽` to a selection `Sel` interpreted
by a concrete language.
For example, a binary choice language may use `F → Bool` as the feature
selections language.
-}
𝕊 : Set₁
𝕊 = Set

-- Set of configuration languages
ℂ : Set₁
ℂ = Set

{-
The set of expressions of a variability language.
An expression denotes a set of variants and hence, variant-like sub-terms
occur within an expression.
Such sub-terms describe variants of atomic data (i.e., some structure on atomic elements),
and hence expressions are parameterized in the type of this atomic data.
-}
𝔼 : Set₂
𝔼 = 𝔸 → Set₁
