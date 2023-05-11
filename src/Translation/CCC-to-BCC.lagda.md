# Relating Core Choice Calculus to Binary Choice Calculus

## Options

```agda
{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
```

## Module

```agda
module Translation.CCC-to-BCC where
```

## Imports

```agda
-- stdlib
open import Data.Bool
  using (Bool; true; false; if_then_else_)
open import Data.List
  using (List; []; _∷_; lookup)
  renaming (map to mapl)
open import Data.List.NonEmpty
  using (List⁺; _∷_; toList)
  renaming (map to mapl⁺)
open import Data.Nat
  using (ℕ; zero; suc; NonZero)
open import Data.Product
  using (∃; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.String
  using (String; _++_)
open import Function
  using (id; _∘_; flip)
open import Size
  using (Size; ∞; ↑_; _⊔ˢ_)

import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≗_; refl)
open Eq.≡-Reasoning
  using (begin_; _≡⟨⟩_; step-≡; _∎)

-- own modules

open import Lang.Annotation.Name using (Dimension; _==_)
open import Lang.CCC
  using (CCC; choice-elimination)
  renaming (Artifact to Artifactₙ;
            _⟨_⟩ to _⟨_⟩ₙ;
            Tag to Tagₙ;
            Configuration to Configurationₙ;
            ⟦_⟧ to ⟦_⟧ₙ)
open import Lang.BCC
  using (BCC; BCC-is-weakenable)
  renaming (Artifact to Artifact₂;
            _⟨_,_⟩ to _⟨_,_⟩₂;
            Tag to Tag₂;
            Configuration to Configuration₂;
            ⟦_⟧ to ⟦_⟧₂)

open import SemanticDomain using (Variant; Artifactᵥ)
open import Definitions using (Domain; VarLang; ConfLang; Semantics; sequence-sized-artifact)
open import Relations.Semantic
  -- Relations between variability languages
  using (_,_is-at-least-as-expressive-as_,_)
open import Translation.Translation
  -- Translations
  using (Translation; TranslationResult; expr; conf; fnoc)
  -- Translation properties
  using (_⊆-via_; _⊇-via_; _is-variant-preserving; _is-semantics-preserving; translation-proves-variant-preservation)

open import Axioms.Extensionality
  using (extensionality; _embeds-via_)
  renaming (map-cong-≡ to mapl-cong-≡; map-cong-≗-≡ to mapl-cong-≗-≡)

open import Util.Existence using (_,_; proj₁; proj₂)
```

## Translation

To convert choice calculus to binary normal form, we have to convert n-ary choices to binary choices.
We can do so by recursively nesting alternatives beyond the second in nested binary decisions.
This translation follows the similar observations for if-statements that an `elseif` expression is equivalent to an `else` branch with a nested `if`:

      if x
        then a
      elif y
        then b
      else
        c

    ≡ if x
        then a
      else
        if y
          then b
        else
          c

One of the key challenges for this translations is to introduce correct new conditions (i.e., dimensions) for the nested choices.
Here, this means, we have to generate new choices, and thus new dimensions.
In the above example, this is not necessary because every branch already has a condition, but in choice calculus, every alternative is just identified by an index below a dimension.
So for example, the first if-elif-else chain would be expressed as `D⟨a, b, c⟩`, where `D` somehow reflects the conditions `x` and `y`.
So to translate this chain to binary, we have to nest every alternatives beyond the first, such that `D⟨a, b, c⟩` becomes `D⟨a, E⟨b, c⟩⟩`, where `E` is a new new name that corresponds to `y` in the second if-else-if-else chain above.
When generating a new name for a new dimension, we have to assume that it does not exist yet or otherwise, we cannot preserve semantics.
For example, when generating names by appending tick marks, we may get `toBCC (D⟨a,b,D'⟨c, d⟩⟩) ≡ D⟨a, D'⟨b, D'⟨c, d⟩⟩⟩` which has different semantics than the input.

We identified two possible ways to ensure that new generated names do not collide with existing dimension names:

1. Bake uniqueness into the type-level by using a different type for dimension in the output expression: Values of the new type would ensure that these values were never part of the original input expression. However, this is very intrusive into the language design and introduces complexity for all matters other than conversion to binary normal form. It also obfuscates the language design for an easier solution to this particular problem. That is why we choose the second alternative below.
2. Ensure that any new dimension name does not collide (as shown in the example above). Collision can either occur with names from the input formula or in the output formula. When generating a new name, we can only guarantee that it does not collide with another name in the input formula by comparing it to every name in the input formula. This is an intricate process, vastly complicating proofs. Another strategy would be to ensure that any generated name in the output formula collides exactly with those names in the output formula for which both respective dimensions in the input formula collided. For example, when transforming `D⟨D⟨x, y, z⟩, A⟨u, v, w⟩, n⟩`, we have to introduce new dimensions for `D` and `A` because these have arity greater 2. For both occurences of `D`, the generated dimension has to have the same name to ensure choice synchronization (see Erics PhD thesis). And these two names must collide in the output but must not collide with any other name. For example, `D⟨D⟨x, D'⟨y, z⟩⟩, D'⟨A⟨u, A'⟨v, w⟩⟩, n⟩⟩` would be valid but the generated name `D'` can still collide with names for the input formula.

To prevent collisions of names, we (1) rename every dimension in the input in a consistent way and (2) also generate new names following this way. This allows us to ensure that generated names do not collide with other existing names.
The idea is to append an index to every dimension that indicates the tag that had to be chosen in the input formula to pick that choice's left alternative.

Example: `D⟨x, y, z, w⟩ ↦ D.0⟨x, D.1⟨y, D.2⟨z, w⟩⟩⟩`

Definition:
```agda
open import Data.Nat.Show renaming (show to show-nat)

indexedDim : Dimension → ℕ → Dimension
indexedDim D n = D ++ "." ++ (show-nat n) -- Do not simplify for n ≡ᵇ zero! I know names like A.0 are ugly if we can avoid them but dropping the .0 where possible can cause name collisions in the output formula!
```

Here is an informal proof that using `indexedDim` to rename every dimension does not cause unintended choice synchronizations:

    Every dimension D in the input formula is renamed to (D ++ ".0").
    Thus every dimension is manipulated equally and thus, this transformation is a true renaming.

    Removal of dimensions occurs only for unary choices and cannot invalidate uniqueness of names anyway.

    New dimensions are introduced only to unroll a dimension from the input formula.
    This means, each generated dimension G is associated to exactly one dimension D from the input formula.
    The name of G is (D ++ "." ++ suc n) for an n : ℕ.
    The name of G is new because of proof by contradiction:
      Assume the name of G is not new (i.e., collides).
      This means there is dimension A in the output formula with the same name as G
      but A was associated to another dimension in the input formula.
      The name of A is of the form (I ++ "." m) for an m : ℕ and a dimension I from the input formula.
      Because A has the same name as G, we know that I = D and suc n = m.
      Thus, both A and G originate from the same dimension in the input formula.
      This contradicts our assumption that G collided.

To prove that a translation from choice calculus to binary normal form is semantics-preserving, we have to show that both, the input as well as the output expression, describe the same set of variants (just as we did earlier for the inverse translation).
As we will see later, this requires us to not only translate an expression from n-ary to binary form, but also configurations.
Our implementation of the translation thus takes an n-ary choice calculus expression as input and yields two results: (1) a converter that can translate configurations for the input formula to configurations for the output formula and vice versa, and (2) the expression in binary normal form.
To define the configuration converter, we use the state monad that keeps track of our current progress of translating configurations.

We thus first import the necessary definitions from the standard library:
```agda
-- Import general functor and monad operations.
open import Effect.Functor using (RawFunctor)
open import Effect.Applicative using (RawApplicative)
open import Effect.Monad using (RawMonad)

-- Import state monad
open import Effect.Monad.State
  using (State; RawMonadState; runState; execState; evalState)
  renaming (functor to state-functor;
            applicative to state-applicative;
            monad to state-monad;
            monadState to state-monad-specifics)


open import Util.Existence using (∃-Size; _,_)
import Util.NonEmptyTraversable
open Util.NonEmptyTraversable.TraversableA⁺ using (mapA⁺)

```

To convert configurations for the input formula to configurations for the output formula and vice versa, we introduce the following record.
We use this record as the state during our translation.
```agda
-- resembles a specialized version of _⇔_ in the plfa book
record ConfigurationConverter : Set where
  field
    nary→binary : Configurationₙ → Configuration₂
    binary→nary : Configuration₂ → Configurationₙ
open ConfigurationConverter public

-- Default configuration converter that always goes left.
-- We use it as a base case when we have no further information.
-- The actual values here do not matter as we will always have values from recursion ends.
unknownConfigurationConverter : ConfigurationConverter
unknownConfigurationConverter = record
  { nary→binary = λ _ _ → true
  ; binary→nary = λ _ _ → 0
  }

-- The state we are going to use during the translation from n-ary to binary choice calculus.
-- We keep track of the current configuration converter and update it when necessary.
-- During the translation, we keep track of the intermediate translated expression as well as its size.
TranslationState : Domain → Set
TranslationState D = State ConfigurationConverter (∃-Size[ i ] (BCC i D))
```

We can now define our translation function.
```agda
-- Helper function to making our desired TranslationResult stateful via TranslationState.
toBCC : ∀ {i : Size} {A : Set} → CCC i A → TranslationState A

{- |
Unroll choices by recursively nesting any alternatives beyond the first.
Example: D ⟨ u ∷ v ∷ w ∷ [] ⟩ → D.0 ⟨ u, D.1 ⟨ v , w ⟩₂ ⟩₂
-}
{-# TERMINATING #-} -- I do not know yet how to teach Agda that this terminates. TODO: Fix
toBCC-choice-unroll : ∀ {i : Size} {A : Set}
  → Dimension      -- initial dimension in input formula that we translate (D in the example above).
  → ℕ             -- Current alternative of the given dimension we are translating. zero is left-most alternative (pointing to u in the example above).
  → List⁺ (CCC i A) -- remaining alternatives of the choice to unroll. We let this shrink recursively.
  → TranslationState A

-- Translation of leaves:
-- Just convert the constructor and keep the current bound i.
toBCC {i = i} (Artifactₙ a []) =
  let open RawMonad state-monad in
    pure (i , Artifact₂ a [])
-- Translation of inner artifact nodes:
-- Basically, we are leaving the tree structure unchanged and just translate the n-ary artifact to a binary one without any changes.
-- However, recursively translating all sub-expression is pretty complicated because of the sizes and the state.
-- Recursively translating all children yields a list of states which we evaluate in sequence (using mapA⁺).
-- The result "children-and-their-sizes" is a list of subtrees paired with their size each
-- (children-and-their-sizes : List (∃-Size[ i ] (BCC i A))).
-- We then find the maximum subtree depth from that list and put all children below an artifact node.
toBCC (Artifactₙ a (e ∷ es)) =
  let open RawMonad state-monad in
  do
    children-and-their-sizes ← mapA⁺ state-applicative toBCC (e ∷ es)
    pure (sequence-sized-artifact BCC-is-weakenable Artifact₂ a children-and-their-sizes)
-- Translation of choices, which we do via auxiliary unroll function.
toBCC (D ⟨ es ⟩ₙ) = toBCC-choice-unroll D zero es

open import Data.Nat renaming (_≡ᵇ_ to _nat-≡ᵇ_)
open import Util.Util using (empty?)

update-configuration-converter :
    ConfigurationConverter
  → Dimension  -- corresponding dimension in the input n-ary expression
  → ℕ         -- current nesting depth (see toBCC'-choice-unroll)
  → Dimension  -- name of the corresponding dimension in the output binary expression
  → Bool       -- True iff the currently inspected choice is binary.
  → ConfigurationConverter
update-configuration-converter conf-converter D n D' binary? =
    let n→b = nary→binary conf-converter
        b→n = binary→nary conf-converter in
    record
      -- Given an n-ary configuration cₙ for the input formula, we want to find the value of a given dimension in the binary output formula
      { nary→binary = λ {cₙ queried-output-dimension →
          -- If the queried dimension was translated from our currently translated dimension D.
          if queried-output-dimension == D'
          -- If the selection made in the input formula did select the left alternative of our choice
          -- then also pick it in the binary output formula. Otherwise, do not pick it.
          -- In case cₙ D <ᵇ n, the result does not matter. Then, an alternative above this choice was already chosen
          -- (and we are within an else branch). So it does not matter what we pick here. Could be true, false, or n→b cₙ queried-output-dimension.
          -- In case cₙ D >ᵇ n, the result has to be false because the alternative that has to be picked is on the right, which is only checked if we do not go left here.
          then cₙ D nat-≡ᵇ n
          -- If not, ask our existing configuration translation knowledge.
          else n→b cₙ queried-output-dimension
          }
      -- Given a binary configuration c₂ for the output formula, we want to find the value of a queried dimension in the n-ary input formula.
      ; binary→nary = λ {c₂ queried-input-dimension →
          let recursive-result = b→n c₂ queried-input-dimension in
          -- If the queried dimension is the dimension we currently translate.
          if queried-input-dimension == D
          then if c₂ D'        -- If the binary configuration has chosen the left alternative of the nested binary dimension
               then n          -- ... then that is the alternative we have to pick in the input formula.
               else if binary? -- ... if not, we check if the current choice is already binary.
                    then suc n            -- If it is, we pick the right alternative.
                    else recursive-result -- Otherwise, we check further nested branches recursively.
          else recursive-result
          }
      }

-- Use the idempotency rule D⟨e⟩≈e to unwrap unary choices.
-- This is where recursion stops.
toBCC-choice-unroll D n (e₁ ∷ []) = toBCC e₁
-- For n-ary choices with n > 1, convert the head and recursively convert the tail.
toBCC-choice-unroll D n (e₁ ∷ e₂ ∷ es) =
  let open RawMonad state-monad
      open RawMonadState state-monad-specifics
  in do
    let D' = indexedDim D n

    -- translation of the formula
    (size-e₁   , cc₂-e₁  ) ← toBCC e₁
    (size-tail , cc₂-tail) ← toBCC-choice-unroll D (suc n) (e₂ ∷ es)

    -- translation of configurations
    -- The tail length check is actually a recursion end that checks if we are left with a binary choice.
    -- So we might want to introduce a pattern matching case for binary choices instead of doing this runtime-check here.
    -- However, this abstraction causes more boilerplate than it simplifies.
    -- Let's see how much more complicated the proofs become.
    conf-converter ← get
    put (update-configuration-converter conf-converter D n D' (empty? es))

    let max-child-size = size-e₁ ⊔ˢ size-tail
        choice-size    = ↑ max-child-size
    pure (choice-size , _⟨_,_⟩₂ {max-child-size} D' cc₂-e₁ cc₂-tail)
```

Finally, we can use `toBCC` to produce a `Translation`:
```agda
{-
Translates a given n-ary expression to a (1) a binary expression of a certain size, (2) two conversion functions to translate configurations for the input and output expressions.
-}
translate : ∀ {i : Size} {A : Domain} → CCC i A → TranslationResult A BCC Configurationₙ Configuration₂
translate {i} {_} ccc =
  let (configConverter , (i , bcc)) = runState (toBCC ccc) unknownConfigurationConverter
  in
  record
  { size = i
  ; expr = bcc
  ; conf = nary→binary configConverter
  ; fnoc = binary→nary configConverter
  }

CCC→BCC : Translation CCC BCC Configurationₙ Configuration₂
CCC→BCC =
  record
  { sem₁ = ⟦_⟧ₙ
  ; sem₂ = ⟦_⟧₂
  ; translate = translate
  }
```

# As inference rules

## Translation of Expressions

```agda
data _,_⊢_⟶_ : ∀ {A : Domain} → (i : Size) → ℕ → CCC i A → BCC ∞ A → Set
infix 3 _,_⊢_⟶_

data _,_,_⊢_⟶ᶜ_ : ∀ {A : Domain} → (i : Size) → ℕ → Dimension → List⁺ (CCC i A) → BCC ∞ A → Set
infix 3 _,_,_⊢_⟶ᶜ_

data _,_⊢_⟶_ where
  -- leaf translation is trivial
  E-Artifact-Leaf :
     ∀ {A : Domain}
       {i : Size}
       {n : ℕ}
       {a : A}
       ------------------------------------------
     → ↑ i , n ⊢ Artifactₙ a [] ⟶ Artifact₂ a []

  {-|
  For artifacts, we recurse on each element.
  As a trick to reapply the artifact rules, we wrap the tail in an artifact again.
  This unfortunately requires some separete unwrapping boilerplate in later proofs.
  However, simplification measures I tried to not wrap the recursion on the tail in a new Artifact failed or were less convenient.
  I tried to:
    - Use All on lists to say that all es can be reduced via a list predicate. This requires to deal with All in later proofs which is ok but not less boilerplate and probably harder to understand.
    - Use a separate relation (i.e., another set of inference rules) solely for artifact recursion but I got into some pattern matching problems with Agda that I couldnt resolve.
  -}
  E-Artifact :
     ∀ {A : Domain}
       {i : Size}
       {n : ℕ}
       {a : A}
       {e  : CCC i A}
       {es : List (CCC i A)}
       {e'  : BCC ∞ A}
       {es' : List (BCC ∞ A)}
     →   i , n ⊢ e ⟶ e'
     → ↑ i , n ⊢ Artifactₙ a es ⟶ Artifact₂ a es'
       --------------------------------------------------------
     → ↑ i , n ⊢ Artifactₙ a (e ∷ es) ⟶ Artifact₂ a (e' ∷ es')

  {-|
  Unary choices are mandatory so we can just recursively translate what's in the choice and go with that.
  No choices to make so we strip it off.
  -}
  E-Choice-Unary :
    ∀ {i : Size}
      {n : ℕ}
      {A : Domain}
      {D : Dimension}
      {m : CCC i A}
      {m' : BCC ∞ A}
    →   i , n ⊢ m ⟶ m'
      ---------------------------
    → ↑ i , n ⊢ D ⟨ m ∷ [] ⟩ₙ ⟶ m'

  {-|
  Choices that have more than one alternative have to be unrolled.
  This is the crucial step of the translation from core to binary choice calculus.
  We create a new dimension whose name is indexed by the current unroll depth we are in.
  We recursively translate the first alternative "a".
  We recursively unroll the tail alternatives "b ∷ cs", going one level deeper into unrolling (suc n).
  -}
  E-Choice-Unroll :
    ∀ {i : Size}
      {n : ℕ}
      {A : Domain}
      {D : Dimension}
      {a b : CCC i A}
      {cs : List (CCC i A)}
      {a' bcs' : BCC ∞ A}
    →   i , suc n ⊢ a ⟶ a'
    → ↑ i , suc n ⊢ D ⟨ b ∷ cs ⟩ₙ ⟶ bcs'
      ----------------------------------------------------------------
    → ↑ i ,     n ⊢ D ⟨ a ∷ b ∷ cs ⟩ₙ ⟶ (indexedDim D n) ⟨ a' , bcs' ⟩₂

data _,_,_⊢_⟶ᶜ_ where
  EE-Choice-Unary :
    ∀ {i : Size}
      {n : ℕ}
      {A : Domain}
      {D : Dimension}
      {m : CCC i A} -- m for mandatory
      {m' : BCC ∞ A}
    →   i , n     ⊢ m ⟶ m'
      ---------------------------
    → ↑ i , n , D ⊢ m ∷ [] ⟶ᶜ m'

  EE-Choice-Unroll :
    ∀ {i : Size}
      {n : ℕ}
      {A : Domain}
      {D : Dimension}
      {a b : CCC i A}
      {cs : List (CCC i A)}
      {a' bcs' : BCC ∞ A}
    →   i , suc n     ⊢ a ⟶ a'
    → ↑ i , suc n , D ⊢ b ∷ cs ⟶ᶜ bcs'
      ----------------------------------------------------------------
    → ↑ i ,     n , D ⊢ a ∷ b ∷ cs ⟶ᶜ (indexedDim D n) ⟨ a' , bcs' ⟩₂
```

### Determinism

#### Theorems
```agda
⟶-is-deterministic : ∀ {i} {A} {n} {e : CCC i A} {b b' : BCC ∞ A}
  → i , n ⊢ e ⟶ b
  → i , n ⊢ e ⟶ b'
    ---------------
  → b ≡ b'

⟶ᶜ-is-deterministic : ∀ {i} {A} {D} {n} {es : List⁺ (CCC i A)} {b b' : BCC ∞ A}
  → i , n , D ⊢ es ⟶ᶜ b
  → i , n , D ⊢ es ⟶ᶜ b'
    ---------------------
  → b ≡ b'

artifact₂-tail-equals : ∀ {i : Size} {A : Domain} {a : A} {es es' : List (BCC i A)}
  → Artifact₂ a es ≡ Artifact₂ a es'
  → es ≡ es'
artifact₂-tail-equals refl = refl

⟶-is-deterministic E-Artifact-Leaf E-Artifact-Leaf = refl
⟶-is-deterministic (E-Artifact ⟶e₁ ⟶es₁) (E-Artifact ⟶e₂ ⟶es₂)
  rewrite ⟶-is-deterministic ⟶e₁ ⟶e₂ | artifact₂-tail-equals (⟶-is-deterministic ⟶es₁ ⟶es₂)
  = refl
⟶-is-deterministic (E-Choice-Unary ⟶b) (E-Choice-Unary ⟶b') = ⟶-is-deterministic ⟶b ⟶b'
⟶-is-deterministic (E-Choice-Unroll ⟶a ⟶bcs) (E-Choice-Unroll ⟶a' ⟶bcs')
  rewrite (⟶-is-deterministic ⟶a ⟶a') | (⟶-is-deterministic ⟶bcs ⟶bcs')
  = refl

⟶ᶜ-is-deterministic {i} {A} {D} {n} {es} {b} {b'} (EE-Choice-Unary ⟶b) x = {!!}
⟶ᶜ-is-deterministic (EE-Choice-Unroll ⟶a ⟶bcs) ()
```

### Totality (i.e., Progress)

```agda
Total : ∀ {i} {A} → ℕ → CCC i A → Set
Total {i} n e = ∃[ b ] (i , n ⊢ e ⟶ b)

from-rule : ∀ {i} {n} {A} {e : CCC i A} {b : BCC ∞ A}
  → i , n ⊢ e ⟶ b
    --------------
  → Total n e
from-rule {b = b} r = b , r

⟶-is-total-Artifact : ∀ {i} {n} {A}
  → (a : A)
  → (e : CCC i A)
  → (es : List (CCC i A))
  → Total n e
  → Total n (Artifactₙ a es)
    ----------------------
  → Total n (Artifactₙ a (e ∷ es))
⟶-is-total-Artifact a e .[]      (e' , ⟶e') (Artifact₂ .a .[]      , E-Artifact-Leaf)
  = from-rule (E-Artifact ⟶e' E-Artifact-Leaf)
⟶-is-total-Artifact a e .(_ ∷ _) (e' , ⟶e') (Artifact₂ .a .(_ ∷ _) , E-Artifact ⟶es-head ⟶es-tail)
  = from-rule (E-Artifact ⟶e' (E-Artifact ⟶es-head ⟶es-tail))

⟶-is-total : ∀ {i} {A}
  → (n : ℕ)
  → (e : CCC i A)
    -------------
  → Total n e
⟶-is-total _ (Artifactₙ a [])       = from-rule E-Artifact-Leaf
⟶-is-total n (Artifactₙ a (e ∷ es)) = ⟶-is-total-Artifact a e es (⟶-is-total n e) (⟶-is-total n (Artifactₙ a es))
⟶-is-total n (D ⟨ a ∷ [] ⟩ₙ)         = from-rule (E-Choice-Unary (proj₂ (⟶-is-total n a)))
⟶-is-total n (D ⟨ a ∷ b ∷ cs ⟩ₙ)     = {!!}
  -- let ⟶a   = proj₂ (⟶-is-total (suc n) a)
  --     ⟶bcs = proj₂ (⟶-is-total (suc n) (D ⟨ b ∷ cs ⟩ₙ))
  --  in from-rule (E-Choice-Unroll ⟶a ⟶bcs)
```

## Translation of Configurations

```agda
Conf : Set
Conf = Configurationₙ → Configuration₂

Fnoc : Set
Fnoc = Configuration₂ → Configurationₙ

all-left : Conf
all-left cₙ D = true

all-first : Fnoc
all-first c₂ D = 0

--\rr-
data _,_⊢_↠_ : ∀ {A : Domain} {i : Size} → ℕ → CCC i A → Conf → Conf → Set
infix 3 _,_⊢_↠_

--\ll-
data _⊢_↞_ : ∀ {A : Domain} {i : Size} → CCC i A → Fnoc → Fnoc → Set
infix 3 _⊢_↞_

data _,_⊢_↠_ where
  C-Artifact-Leaf :
     ∀ {n : ℕ}
       {A : Domain}
       {a : A}
       {c : Conf}
       -----------------------
     → n , Artifactₙ a [] ⊢ c ↠ c

  C-Artifact :
     ∀ {n : ℕ}
       {i : Size}
       {A : Domain}
       {a : A}
       {e : CCC i A}
       {es : List (CCC i A)}
       {c c' c'' : Conf}
     → n ,              e       ⊢ c  ↠ c'
     → n , Artifactₙ a      es  ⊢ c' ↠ c''
       -------------------------------
     → n , Artifactₙ a (e ∷ es) ⊢ c  ↠ c''

  C-Choice-Unary :
    ∀ {n : ℕ}
      {i : Size}
      {A : Domain}
      {D : Dimension}
      {m : CCC i A}
      {c c' : Conf}
    → n ,   m ⊢ c ↠ c'
      --------------------------
    → n , D ⟨ m ∷ [] ⟩ₙ ⊢ c ↠ c'

  C-Choice-Unroll :
    ∀ {n : ℕ}
      {i : Size}
      {A : Domain}
      {D : Dimension}
      {a b : CCC i A}
      {cs : List (CCC i A)}
      {c c' c'' : Conf}
    → suc n ,     a            ⊢ c ↠ c'
    → suc n , D ⟨     b ∷ cs ⟩ₙ ⊢ c' ↠ c''
      -----------------------------------
    →     n , D ⟨ a ∷ b ∷ cs ⟩ₙ ⊢ c ↠ (λ {cₙ queried-output-dimension →
          -- If the queried dimension was translated from our currently translated dimension D.
          if queried-output-dimension == (indexedDim D n)
          -- If the selection made in the input formula did select the left alternative of our choice
          -- then also pick it in the binary output formula. Otherwise, do not pick it.
          -- In case cₙ D <ᵇ n, the result does not matter. Then, an alternative above this choice was already chosen
          -- (and we are within an else branch). So it does not matter what we pick here. Could be true, false, or n→b cₙ queried-output-dimension.
          -- In case cₙ D >ᵇ n, the result has to be false because the alternative that has to be picked is on the right, which is only checked if we do not go left here.
          then cₙ D nat-≡ᵇ n
          -- If not, ask our existing configuration translation knowledge.
          else c'' cₙ queried-output-dimension
          })

data _⊢_↞_ where
```


### Determinism

### Totality

## Preservation

```agda
preserves-l : ∀ {i} {n} {A} {e : CCC i A} {b : BCC ∞ A} {c : Conf}
  → (cₙ : Configurationₙ)
  → i , n ⊢ e ⟶ b
  → n , e ⊢ all-left ↠ c
    -----------------------------
  → ⟦ e ⟧ₙ cₙ ≡ ⟦ b ⟧₂ (c cₙ)
preserves-l = {!!}

preserves-r : ∀ {i} {n} {A} {e : CCC i A} {b : BCC ∞ A} {c : Fnoc}
  → (c₂ : Configuration₂)
  → i , n ⊢ e ⟶ b
  → e ⊢ c ↞ all-first
    -----------------------------
  → ⟦ e ⟧ₙ (c c₂) ≡ ⟦ b ⟧₂ c₂
preserves-r = {!!}
```


### Old proofs

Now we prove that conversion to binary normal form is variant-preserving (i.e., the set of described variants is the same).
```
-- CCC→BCC-left : ∀ {i : Size} {A : Domain}
--   → (e : CCC i A)
--     ---------------------
--   → e ⊆-via CCC→BCC

-- CCC→BCC-right : ∀ {i : Size} {A : Domain}
--   → (e : CCC i A)
--     ---------------------
--   → e ⊇-via CCC→BCC

-- CCC→BCC-is-variant-preserving : CCC→BCC is-variant-preserving
-- CCC→BCC-is-variant-preserving e = CCC→BCC-left e , CCC→BCC-right e

-- BCC-is-at-least-as-expressive-as-CCC : BCC , ⟦_⟧₂ is-at-least-as-expressive-as CCC , ⟦_⟧ₙ
-- BCC-is-at-least-as-expressive-as-CCC = translation-proves-variant-preservation CCC→BCC CCC→BCC-is-variant-preserving
```

Comments by Jeff:

    I would think the state monad would need to keep track of proofs on the state for each bind.
    I had something like this in mind: https://idris2.readthedocs.io/en/latest/tutorial/interp.html
    which keeps a state of proofs for each term in the interpreter state. Then each proof is that the term is well typed

#### Proof of the left side

```agda
-- CCC→BCC-left (Artifactₙ a []) c₂ = refl
-- CCC→BCC-left e@(Artifactₙ a es@(_ ∷ _)) cₙ =
--   let -- open RawFunctor state-functor
--       c₂ = conf (translate e) cₙ
--   in
--   begin
--     ⟦ e ⟧ₙ cₙ
--   ≡⟨⟩
--     Artifactᵥ a (mapl (flip ⟦_⟧ₙ cₙ) es)
--   -- TODO: Somehow apply the induction hypothesis below the sequenceA below the runState below the mapl below the Artifactᵥ
--   ≡⟨ {!!}  ⟩
--     ⟦ expr (translate e) ⟧₂ c₂
--   ∎
-- CCC→BCC-left (D ⟨ e ∷ [] ⟩ₙ) cₙ =
--   let c₂ = conf (translate (D ⟨ e ∷ [] ⟩ₙ)) cₙ in
--   ⟦ D ⟨ e ∷ [] ⟩ₙ ⟧ₙ cₙ                   ≡⟨⟩
--   ⟦ e           ⟧ₙ cₙ                    ≡⟨ CCC→BCC-left e cₙ ⟩
--   ⟦ expr (translate e)              ⟧₂ c₂ ≡⟨⟩
--   ⟦ expr (translate (D ⟨ e ∷ [] ⟩ₙ)) ⟧₂ c₂ ∎
-- CCC→BCC-left e@(D ⟨ es@(_ ∷ _ ∷ _) ⟩ₙ) cₙ =
--   let c₂ = conf (translate e) cₙ
--       e₂ = translate e
--   in
--   begin
--     ⟦ e ⟧ₙ cₙ
--   ≡⟨⟩
--     ⟦ choice-elimination (cₙ D) es ⟧ₙ cₙ
--   --≡⟨ {!!} ⟩
--   --  ⟦ if (c₂ D) then {!!} else {!!} ⟧₂ c₂
--   ≡⟨ {!!} ⟩
--     ⟦ expr (translate e) ⟧₂ c₂
--   ∎
```

#### Proof of the right side

```agda
-- -- Every variant described by an n-ary CC expression, is also described by its translation to binray CC.
-- CCC→BCC-right (Artifactₙ a []) _ = refl
-- CCC→BCC-right (Artifactₙ a es@(_ ∷ _)) c₂ = {!!}
-- CCC→BCC-right (D ⟨ e ∷ [] ⟩ₙ) c₂ = CCC→BCC-right e c₂ -- just apply the induction hypothesis on the only mandatory alternative
-- CCC→BCC-right (D ⟨ es@(_ ∷ _ ∷ _) ⟩ₙ) c₂ = {!!}
```
