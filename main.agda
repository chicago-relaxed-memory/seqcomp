open import prelude
open import data-model
import command
import pomset
import semantics
import examples

module main (Event : Set) (MM : MemoryModel(Event)) where

  open MemoryModel MM
  open command(Event)(MM)
  open pomset(Event)(DM)
  open semantics(Event)(MM)

  open import augmentation(Event)(MM) as augmentation using (_≲_)
  import monoid(Event)(MM) as monoid

  -- PROPOSITION: semantics is augment-closed

  sem-resp-≲ : ∀ {P P′} C → (P ≲ P′) → (P ∈ ⟦ C ⟧) → (P′ ∈ ⟦ C ⟧)

  -- PROOF in augmentation.agda  

  sem-resp-≲ = augmentation.sem-resp-≲

  -- PROPOSITION: sequential composition forms a monoid
  
  ⟦C⟧⊆⟦C∙skip⟧ : ∀ C → ⟦ C ⟧ ⊆ ⟦ C ∙ skip ⟧
  ⟦C∙skip⟧⊆⟦C⟧ : ∀ C → ⟦ C ∙ skip ⟧ ⊆ ⟦ C ⟧

  ⟦C⟧⊆⟦skip∙C⟧ : ∀ C → ⟦ C ⟧ ⊆ ⟦ skip ∙ C ⟧
  ⟦skip∙C⟧⊆⟦C⟧ : ∀ C → ⟦ skip ∙ C ⟧ ⊆ ⟦ C ⟧

  ⟦C₁∙⟨C₂∙C₃⟩⟧⊆⟦⟨C₁∙C₂⟩∙C₃⟧ : ∀ C₁ C₂ C₃ → ⟦ C₁ ∙ (C₂ ∙ C₃) ⟧ ⊆ ⟦ (C₁ ∙ C₂) ∙ C₃ ⟧
  ⟦⟨C₁∙C₂⟩∙C₃⟧⊆⟦C₁∙⟨C₂∙C₃⟩⟧ : ∀ C₁ C₂ C₃ → ⟦ (C₁ ∙ C₂) ∙ C₃ ⟧ ⊆ ⟦ C₁ ∙ (C₂ ∙ C₃) ⟧

  -- PROOF in monoid.agda

  ⟦C⟧⊆⟦C∙skip⟧ = monoid.⟦C⟧⊆⟦C∙skip⟧
  ⟦C∙skip⟧⊆⟦C⟧ = monoid.⟦C∙skip⟧⊆⟦C⟧

  ⟦C⟧⊆⟦skip∙C⟧ = monoid.⟦C⟧⊆⟦skip∙C⟧
  ⟦skip∙C⟧⊆⟦C⟧ = monoid.⟦skip∙C⟧⊆⟦C⟧

  ⟦C₁∙⟨C₂∙C₃⟩⟧⊆⟦⟨C₁∙C₂⟩∙C₃⟧ = monoid.⟦C₁∙⟨C₂∙C₃⟩⟧⊆⟦⟨C₁∙C₂⟩∙C₃⟧
  ⟦⟨C₁∙C₂⟩∙C₃⟧⊆⟦C₁∙⟨C₂∙C₃⟩⟧ = monoid.⟦⟨C₁∙C₂⟩∙C₃⟧⊆⟦C₁∙⟨C₂∙C₃⟩⟧

  ------------
  
