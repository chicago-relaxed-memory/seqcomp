open import prelude
open import data-model
import pomset

module parcomp (DM : DataModel) (Event : Set) where

  open DataModel DM
  open pomset(DM)(Event)
   
  record NIL (P₀ : PomsetWithPreconditions) : Set₁ where
  
   open PomsetWithPreconditions P₀ using () renaming (E to E₀)
   field E₀⊆∅ :  (E₀ ⊆ ∅)

  record _|||_ (𝒫₁ 𝒫₂ : PomsetWithPreconditions → Set₁) (P₀ : PomsetWithPreconditions) : Set₁ where

   field P₁ : PomsetWithPreconditions
   field P₂ : PomsetWithPreconditions

   field P₁∈𝒫₁ : P₁ ∈ 𝒫₁
   field P₂∈𝒫₂ : P₂ ∈ 𝒫₂
   
   open PomsetWithPreconditions P₀ using () renaming (E to E₀ ; act to act₀ ; pre to pre₀ ; _≤_ to _≤₀_)
   open PomsetWithPreconditions P₁ using () renaming (E to E₁ ; act to act₁ ; pre to pre₁ ; _≤_ to _≤₁_)
   open PomsetWithPreconditions P₂ using () renaming (E to E₂ ; act to act₂ ; pre to pre₂ ; _≤_ to _≤₂_)

   field E₀⊆E₁⊎E₂ : (E₀ ⊆ (E₁ ⊎ E₂))
   field E₁⊆E₀ : (E₁ ⊆ E₀)
   field E₂⊆E₀ : (E₂ ⊆ E₀)
   field E₁∩E₂⊆∅ : (E₁ ∩ E₂) ⊆ ∅ 
   
   field ≤₁⊆≤₀ : ∀ d e → (d ≤₁ e) → (d ≤₀ e)
   field ≤₂⊆≤₀ : ∀ d e → (d ≤₂ e) → (d ≤₀ e)
   
   field pre₀⊨pre₁ : ∀ e → (e ∈ E₁) → (pre₀(e) ⊨ pre₁(e))
   field pre₀⊨pre₂ : ∀ e → (e ∈ E₂) → (pre₀(e) ⊨ pre₂(e))
   
   field act₀=act₁ : ∀ e → (e ∈ E₁) → (act₀(e) ≡ act₁(e))
   field act₀=act₂ : ∀ e → (e ∈ E₂) → (act₀(e) ≡ act₂(e))

  record THREAD (𝒫 : PomsetWithPredicateTransformers → Set₁) (P₀ : PomsetWithPreconditions) : Set₁ where

   field P₁ : PomsetWithPredicateTransformers
   field P₁∈𝒫 : P₁ ∈ 𝒫
   
   open PomsetWithPreconditions P₀ using () renaming (E to E₀ ; act to act₀ ; pre to pre₀ ; _≤_ to _≤₀_)
   open PomsetWithPredicateTransformers P₁ using () renaming (E to E₁ ; act to act₁ ; pre to pre₁ ; _≤_ to _≤₁_ ; τ to τ₁)

   field E₁⊆E₀ : (E₁ ⊆ E₀)
   field E₀⊆E₁ : (E₀ ⊆ E₁)
   
   field ≤₁⊆≤₀ : ∀ d e → (d ≤₁ e) → (d ≤₀ e)
   
   field pre₀⊨pre₁ : ∀ e → (e ∈ E₁) → (pre₀(e) ⊨ pre₁(e))
   field act₀=act₁ : ∀ e → (e ∈ E₁) → (act₀(e) ≡ act₁(e))
