open import prelude
open import data-model using ( DataModel )
import command
import pomset
import semantics
import examples

module main (DM : DataModel) (Event : Set) where

  open DataModel DM
  open command(DM)
  open pomset(DM)(Event)
  open semantics(DM)(Event)

  open import augmentation(DM)(Event) as augmentation using (_≲p_ ; _≲τ_)
  import monoid(DM)(Event) as monoid

  -- PROPOSITION: semantics is augment-closed

  sem-resp-≲τ : ∀ {P P′} C → (P ≲τ P′) → (P ∈ ⟦ C ⟧) → (P′ ∈ ⟦ C ⟧)
  sem-resp-≲p : ∀ {P P′} G → (P ≲p P′) → (P ∈ ⟪ G ⟫) → (P′ ∈ ⟪ G ⟫)

  -- PROOF in augmentation.agda  

  sem-resp-≲τ = augmentation.sem-resp-≲τ
  sem-resp-≲p = augmentation.sem-resp-≲p

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
  
