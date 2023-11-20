module Framework.V2.Compiler where

open import Framework.V2.Variants
open import Framework.V2.Definitions
open import Relation.Binary.PropositionalEquality as Eq using (_≗_)
open import Data.Product using (_×_)
open import Function using (id; _∘_)

ConfigTranslation : ∀ (S₁ : 𝕊) (S₂ : 𝕊) → Set
ConfigTranslation S₁ S₂ = S₁ → S₂

record ConfigCompiler (S₁ : 𝕊) (S₂ : 𝕊) : Set where
  field
    to   : ConfigTranslation S₁ S₂
    from : ConfigTranslation S₂ S₁
open ConfigCompiler public

{-|
A translated configuration is extensionally equal.
Fixme: Give me a proper name not this ugly one.
-}
ExtensionallyEqual-Translation : ∀ {F S Sel} → ConfigEvaluator F S Sel → ConfigTranslation S S → Set
ExtensionallyEqual-Translation evalConfig f = ∀ c → evalConfig (f c) ≗ evalConfig c

ExtensionallyEqual : ∀ {F S Sel} → ConfigEvaluator F S Sel → ConfigCompiler S S → Set
ExtensionallyEqual {F} {S} evalConfig record { to = to ; from = from } =
  ExtensionallyEqual-Translation {F} {S} evalConfig to × ExtensionallyEqual-Translation {F} {S} evalConfig from

-- We identify a configuration to be the same if it can be uniquely translated back
-- (i.e., if `to` is an embedding into the second configuration language via its inverse `from`).
-- We do not require the inverse direction `from`, being an embedding of configurations from `C₂` into `C₁`, because `C₂` could be larger than `C₁` (when interpreted as a set).
-- For example, the set of features in `C₂` could be bigger (e.g., when going from core choice calculus to binary choice calculus) but all information can be derived by `conf` from our initial configuration `c₁`.
Stable : ∀ {S₁ S₂} → ConfigCompiler S₁ S₂ → Set
Stable cc = from cc ∘ to cc ≗ id

record LanguageCompiler {V S₁ S₂} (Γ₁ : VariabilityLanguage V S₁) (Γ₂ : VariabilityLanguage V S₂) : Set₁ where
  private
    L₁ = Expression Γ₁
    L₂ = Expression Γ₂
    ⟦_⟧₁ = Semantics Γ₁
    ⟦_⟧₂ = Semantics Γ₂

  field
    compile         : ∀ {A} → L₁ A → L₂ A
    config-compiler : ConfigCompiler S₁ S₂
    preserves : ∀ {A} → let open IVSet V A using (_≅[_][_]_) in
                ∀ (e : L₁ A) → ⟦ e ⟧₁ ≅[ to config-compiler ][ from config-compiler ] ⟦ compile e ⟧₂
                -- TODO: It might nice to have syntax
                --   ≅[ config-compiler ]
                -- to abbreviate
                --   ≅[ to config-compiler ][ from config-compiler ].

  conf = to   config-compiler
  fnoc = from config-compiler

-- Compiles a single construct to another one without altering the underlying sub expressions.
-- FIXME: This definition might be too abstract.
--        To preserve semantics, most of the time, additional requirements on the
--        config translations are required which are currently not part of the
--        preservation theorem here. Maybe we have to add these constraints as type parameters here?
record ConstructCompiler {V S₁ S₂} (VC₁ : VariabilityConstruct V S₁) (VC₂ : VariabilityConstruct V S₂) : Set₁ where
  open VariabilityConstruct VC₁ renaming (Construct to C₁; construct-semantics to sem₁)
  open VariabilityConstruct VC₂ renaming (Construct to C₂; construct-semantics to sem₂)

  field
    compile : ∀ {E A} → C₁ E A → C₂ E A
    config-compiler : ConfigCompiler S₁ S₂
    stable : Stable config-compiler
    preserves : ∀ {Γ : VariabilityLanguage V S₁} {A}
      → (c : C₁ (Expression Γ) A)
      → let open IVSet V A using (_≅_) in
        sem₁ id Γ c ≅ sem₂ (to config-compiler) Γ (compile c)

{-|
Compiles languages below constructs.
This means that an expression in a language Γ₁ of which we know that it has a specific
syntactic construct VC at the top is compiled to Γ₂ retaining the very same construct at the top.
-}
record ConstructFunctor {V S} (VC : VariabilityConstruct V S) : Set₁ where
  open VariabilityConstruct VC
  open LanguageCompiler using (conf; fnoc; compile; config-compiler)

  field
    map : ∀ {A} {L₁ L₂ : 𝔼}
      → (L₁ A → L₂ A)
      → Construct L₁ A
      → Construct L₂ A
    preserves : ∀ {S'} {Γ₁ : VariabilityLanguage V S} {Γ₂ : VariabilityLanguage V S'} {A}
      → let open IVSet V A using (_≅[_][_]_) in
      ∀ (t : LanguageCompiler Γ₁ Γ₂)
      → (c : Construct (Expression Γ₁) A)
      → Stable (config-compiler t)
      → construct-semantics id Γ₁ c
          ≅[ conf t ][ fnoc t ]
        construct-semantics (fnoc t) Γ₂ (map (compile t) c)

_⊕ᶜᶜ_ : ∀ {S₁ S₂ S₃}
  → ConfigCompiler S₁ S₂
  → ConfigCompiler S₂ S₃
  → ConfigCompiler S₁ S₃
1→2 ⊕ᶜᶜ 2→3 = record
  { to   = to   2→3 ∘ to   1→2
  ; from = from 1→2 ∘ from 2→3
  }

⊕ᶜᶜ-stable :
  ∀ {S₁ S₂ S₃}
    (1→2 : ConfigCompiler S₁ S₂) (2→3 : ConfigCompiler S₂ S₃)
  → Stable 1→2
  → Stable 2→3
    --------------------
  → Stable (1→2 ⊕ᶜᶜ 2→3)
⊕ᶜᶜ-stable 1→2 2→3 s1 s2 c₁ =
  let open Eq.≡-Reasoning in
  begin
    from 1→2 (from 2→3 (to 2→3 (to 1→2 c₁)))
  ≡⟨⟩
    from 1→2 ((from 2→3 ∘ to 2→3) (to 1→2 c₁))
  ≡⟨ Eq.cong (from 1→2) (s2 (to 1→2 c₁)) ⟩
    from 1→2 (id (to 1→2 c₁))
  ≡⟨⟩
    from 1→2 (to 1→2 c₁)
  ≡⟨ s1 c₁ ⟩
    id c₁
  ∎

_⊕ˡ_ : ∀ {V} {S₁ S₂ S₃}
        {Γ₁ : VariabilityLanguage V S₁}
        {Γ₂ : VariabilityLanguage V S₂}
        {Γ₃ : VariabilityLanguage V S₃}
      → LanguageCompiler Γ₁ Γ₂
      → LanguageCompiler Γ₂ Γ₃
      → LanguageCompiler Γ₁ Γ₃
_⊕ˡ_ {V} {S₁} {S₂} {S₃} {Γ₁} {Γ₂} {Γ₃} L₁→L₂ L₂→L₃ = record
  { compile = compile L₂→L₃ ∘ compile L₁→L₂
  ; config-compiler = record { to = conf'; from = fnoc' }
  ; preserves = p
  }
  where open LanguageCompiler
        L₁ = Expression Γ₁
        ⟦_⟧₁ = Semantics Γ₁
        ⟦_⟧₃ = Semantics Γ₃

        conf' : S₁ → S₃
        conf' = conf L₂→L₃ ∘ conf L₁→L₂

        fnoc' : S₃ → S₁
        fnoc' = fnoc L₁→L₂ ∘ fnoc L₂→L₃

        module _ {A : 𝔸} where
          open IVSet V A using (_≅[_][_]_; ≅[]-trans)

          -- this pattern is very similar of ⊆[]-trans
          p : ∀ (e : L₁ A) → ⟦ e ⟧₁ ≅[ conf' ][ fnoc' ] ⟦ compile L₂→L₃ (compile L₁→L₂ e) ⟧₃
          p e = ≅[]-trans (preserves L₁→L₂ e) (preserves L₂→L₃ (compile L₁→L₂ e))

-- _⊕ᶜ_ : ∀ {F S} {VC₁ VC₂ VC₃ : VariabilityConstruct F S}
--   → ConstructCompiler VC₁ VC₂
--   → ConstructCompiler VC₂ VC₃
--   → ConstructCompiler VC₁ VC₃
-- _⊕ᶜ_ {F} {S} {VC₁} {_} {VC₃} 1→2 2→3 = record
--   { compile = compile 2→3 ∘ compile 1→2
--   ; config-compiler = cc
--   ; stable = stb
--   ; preserves = Pres.p
--   }
--   where open ConstructCompiler
--         open VariabilityConstruct VC₁ renaming (Construct to C₁; construct-semantics to sem₁)
--         open VariabilityConstruct VC₃ renaming (construct-semantics to sem₃)

--         cc : ConfigCompiler F S F S
--         cc = config-compiler 1→2 ⊕ᶜᶜ config-compiler 2→3

--         stb : Stable cc
--         stb = ⊕ᶜᶜ-stable (config-compiler 1→2) (config-compiler 2→3) (stable 1→2) (stable 2→3)

--         module Pres {V : 𝕍} {A : 𝔸} where
--           open IVSet V A using (_≅_; ≅-trans)

--           p : ∀ {Γ : VariabilityLanguage V F S}
--               → (c : C₁ F (Expression Γ) A)
--               → sem₁ Γ id c ≅ sem₃ Γ (to cc) (compile 2→3 (compile 1→2 c))
--           p c = ≅-trans (preserves 1→2 c) {!preserves 2→3 (compile 1→2 c)!} --
--           -- p c₁ = ≅-trans (preserves 1→2 c₁) (preserves 2→3 (compile 1→2 c₁))
