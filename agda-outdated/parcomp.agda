open import prelude
open import data-model using (DataModel)
import pomset

module parcomp (Event : Set) (DM : DataModel(Event)) where

  open DataModel DM
  open pomset(Event)(DM)
   
  record _|||_ (𝒫₁ 𝒫₂ : PomsetWithPredicateTransformers → Set₁) (P₀ : PomsetWithPredicateTransformers) : Set₁ where

   field P₁ : PomsetWithPredicateTransformers
   field P₂ : PomsetWithPredicateTransformers

   field P₁∈𝒫₁ : P₁ ∈ 𝒫₁
   field P₂∈𝒫₂ : P₂ ∈ 𝒫₂
   
   open PomsetWithPredicateTransformers P₀ using () renaming (E to E₀ ; ℓ to ℓ₀ ; κ to κ₀ ; _≤_ to _≤₀_ ; ✓ to ✓₀)
   open PomsetWithPredicateTransformers P₁ using () renaming (E to E₁ ; ℓ to ℓ₁ ; κ to κ₁ ; _≤_ to _≤₁_ ; ✓ to ✓₁)
   open PomsetWithPredicateTransformers P₂ using () renaming (E to E₂ ; ℓ to ℓ₂ ; κ to κ₂ ; _≤_ to _≤₂_ ; ✓ to ✓₂)

   field E₀⊆E₁⊎E₂ : (E₀ ⊆ (E₁ ⊎ E₂))
   field E₁⊆E₀ : (E₁ ⊆ E₀)
   field E₂⊆E₀ : (E₂ ⊆ E₀)
   field E₁∩E₂⊆∅ : (E₁ ∩ E₂) ⊆ ∅ 
   
   field ≤₁⊆≤₀ : ∀ d e → (d ≤₁ e) → (d ≤₀ e)
   field ≤₂⊆≤₀ : ∀ d e → (d ≤₂ e) → (d ≤₀ e)
   
   field κ₀⊨κ₁ : ∀ e → (e ∈ E₁) → (κ₀(e) ⊨ κ₁(e))
   field κ₀⊨κ₂ : ∀ e → (e ∈ E₂) → (κ₀(e) ⊨ κ₂(e))
   
   field ✓₀⊨✓₁ : (✓₀ ⊨ ✓₁)
   field ✓₀⊨✓₂ : (✓₀ ⊨ ✓₂)
   
   field ℓ₀=ℓ₁ : ∀ e → (e ∈ E₁) → (ℓ₀(e) ≡ ℓ₁(e))
   field ℓ₀=ℓ₂ : ∀ e → (e ∈ E₂) → (ℓ₀(e) ≡ ℓ₂(e))
