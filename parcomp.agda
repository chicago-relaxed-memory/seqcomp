open import prelude
open import data-model using (DataModel)
import pomset

module parcomp (Event : Set) (DM : DataModel(Event)) where

  open DataModel DM
  open pomset(Event)(DM)
   
  record NIL (P₀ : PomsetWithPreconditions) : Set₁ where
  
   open PomsetWithPreconditions P₀ using () renaming (E to E₀)
   field E₀⊆∅ :  (E₀ ⊆ ∅)

  record _|||_ (𝒫₁ 𝒫₂ : PomsetWithPreconditions → Set₁) (P₀ : PomsetWithPreconditions) : Set₁ where

   field P₁ : PomsetWithPreconditions
   field P₂ : PomsetWithPreconditions

   field P₁∈𝒫₁ : P₁ ∈ 𝒫₁
   field P₂∈𝒫₂ : P₂ ∈ 𝒫₂
   
   open PomsetWithPreconditions P₀ using () renaming (E to E₀ ; ℓ to ℓ₀ ; κ to κ₀ ; _≤_ to _≤₀_)
   open PomsetWithPreconditions P₁ using () renaming (E to E₁ ; ℓ to ℓ₁ ; κ to κ₁ ; _≤_ to _≤₁_)
   open PomsetWithPreconditions P₂ using () renaming (E to E₂ ; ℓ to ℓ₂ ; κ to κ₂ ; _≤_ to _≤₂_)

   field E₀⊆E₁⊎E₂ : (E₀ ⊆ (E₁ ⊎ E₂))
   field E₁⊆E₀ : (E₁ ⊆ E₀)
   field E₂⊆E₀ : (E₂ ⊆ E₀)
   field E₁∩E₂⊆∅ : (E₁ ∩ E₂) ⊆ ∅ 
   
   field ≤₁⊆≤₀ : ∀ d e → (d ≤₁ e) → (d ≤₀ e)
   field ≤₂⊆≤₀ : ∀ d e → (d ≤₂ e) → (d ≤₀ e)
   
   field κ₀⊨κ₁ : ∀ e → (e ∈ E₁) → (κ₀(e) ⊨ κ₁(e))
   field κ₀⊨κ₂ : ∀ e → (e ∈ E₂) → (κ₀(e) ⊨ κ₂(e))
   
   field ℓ₀=ℓ₁ : ∀ e → (e ∈ E₁) → (ℓ₀(e) ≡ ℓ₁(e))
   field ℓ₀=ℓ₂ : ∀ e → (e ∈ E₂) → (ℓ₀(e) ≡ ℓ₂(e))

  record THREAD (𝒫 : PomsetWithPredicateTransformers → Set₁) (P₀ : PomsetWithPreconditions) : Set₁ where

   field P₁ : PomsetWithPredicateTransformers
   field P₁∈𝒫 : P₁ ∈ 𝒫
   
   open PomsetWithPreconditions P₀ using () renaming (E to E₀ ; ℓ to ℓ₀ ; κ to κ₀ ; _≤_ to _≤₀_)
   open PomsetWithPredicateTransformers P₁ using () renaming (E to E₁ ; ℓ to ℓ₁ ; κ to κ₁ ; _≤_ to _≤₁_ ; τ to τ₁)

   field E₁⊆E₀ : (E₁ ⊆ E₀)
   field E₀⊆E₁ : (E₀ ⊆ E₁)
   
   field ≤₁⊆≤₀ : ∀ d e → (d ≤₁ e) → (d ≤₀ e)
   
   field κ₀⊨κ₁ : ∀ e → (e ∈ E₁) → (κ₀(e) ⊨ κ₁(e))
   field ℓ₀=ℓ₁ : ∀ e → (e ∈ E₁) → (ℓ₀(e) ≡ ℓ₁(e))
