import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq using (_≗_)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

eta-equivalence : ∀ {A B : Set} {f : A → B}
    ---------------
  → f ≡ λ {x → f x}
eta-equivalence = refl

≗→≡ : ∀ {A B : Set} {f g : A → B} → f ≗ g → f ≡ g
≗→≡ f≗g = extensionality f≗g

≡→≗ : ∀ {A B : Set} {f g : A → B} → f ≡ g → f ≗ g
≡→≗ f≡g rewrite f≡g = λ x → refl

