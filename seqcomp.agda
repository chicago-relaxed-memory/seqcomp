open import prelude
open import data-model
import pomset

module seqcomp (DM : DataModel) (Event : Set) where

  open DataModel DM
  open pomset(DM)(Event)

  record SKIP (P₀ : PomsetWithPredicateTransformers) : Set₁ where
   
    open PomsetWithPredicateTransformers P₀ using () renaming (E to E₀ ; τ to τ₀)
    field E₀⊆∅ :  (E₀ ⊆ ∅)
    field τ₀ϕ⊨ϕ : ∀ C ϕ → τ₀(C)(ϕ) ⊨ ϕ

  record _●_ (𝒫₁ 𝒫₂ : PomsetWithPredicateTransformers → Set₁) (P₀ : PomsetWithPredicateTransformers) : Set₁ where

   field P₁ : PomsetWithPredicateTransformers
   field P₂ : PomsetWithPredicateTransformers

   field P₁∈𝒫₁ : P₁ ∈ 𝒫₁
   field P₂∈𝒫₂ : P₂ ∈ 𝒫₂
   
   open PomsetWithPredicateTransformers P₀ using () renaming (E to E₀ ; ℓ to ℓ₀ ; κ to κ₀ ; _≤_ to _≤₀_ ; ↓ to ↓₀ ; τ to τ₀)
   open PomsetWithPredicateTransformers P₁ using () renaming (E to E₁ ; ℓ to ℓ₁ ; κ to κ₁ ; _≤_ to _≤₁_ ; ↓ to ↓₁ ; τ to τ₁)
   open PomsetWithPredicateTransformers P₂ using () renaming (E to E₂ ; ℓ to ℓ₂ ; κ to κ₂ ; _≤_ to _≤₂_ ; ↓ to ↓₂ ; τ to τ₂)

   field E₀⊆E₁∪E₂ : (E₀ ⊆ (E₁ ∪ E₂))
   field E₁⊆E₀ : (E₁ ⊆ E₀)
   field E₂⊆E₀ : (E₂ ⊆ E₀)

   E₁∪E₂⊆E₀ : ((E₁ ∪ E₂) ⊆ E₀)
   E₁∪E₂⊆E₀ = ⊆-elim-∪ E₁⊆E₀ E₂⊆E₀
   
   field ≤₁⊆≤₀ : ∀ d e → (d ≤₁ e) → (d ≤₀ e)
   field ≤₂⊆≤₀ : ∀ d e → (d ≤₂ e) → (d ≤₀ e)

   lhs₀ : Event → Formula
   lhs₀ = κ₁

   rhs₀ : Event → Formula
   rhs₀(e) = τ₁(↓₀(e))(κ₂(e))
   
   field κ₀⊨lhs₀ : ∀ e → (e ∈ E₁) → (e ∉ E₂) → (κ₀(e) ⊨ lhs₀(e))
   field κ₀⊨rhs₀ : ∀ e → (e ∉ E₁) → (e ∈ E₂) → (κ₀(e) ⊨ rhs₀(e))
   field κ₀⊨lhs₀∨rhs₀ : ∀ e → (e ∈ E₁) → (e ∈ E₂) → (κ₀(e) ⊨ (lhs₀(e) ∨ rhs₀(e)))
   
   field ℓ₀=ℓ₁ : ∀ e → (e ∈ E₁) → (ℓ₀(e) ≡ ℓ₁(e))
   field ℓ₀=ℓ₂ : ∀ e → (e ∈ E₂) → (ℓ₀(e) ≡ ℓ₂(e))
   
   field τ₀ϕ⊨τ₁τ₂ϕ : ∀ C ϕ → τ₀(C)(ϕ) ⊨ τ₁(C)(τ₂(C)(ϕ))
  
  record IF (ψ : Formula) (𝒫₁ 𝒫₂ : PomsetWithPredicateTransformers → Set₁) (P₀ : PomsetWithPredicateTransformers) : Set₁ where

   field P₁ : PomsetWithPredicateTransformers
   field P₂ : PomsetWithPredicateTransformers
   field P₁∈𝒫₁ : P₁ ∈ 𝒫₁
   field P₂∈𝒫₂ : P₂ ∈ 𝒫₂
   
   open PomsetWithPredicateTransformers P₀ using () renaming (E to E₀ ; ℓ to ℓ₀ ; κ to κ₀ ; _≤_ to _≤₀_ ; τ to τ₀)
   open PomsetWithPredicateTransformers P₁ using () renaming (E to E₁ ; ℓ to ℓ₁ ; κ to κ₁ ; _≤_ to _≤₁_ ; τ to τ₁)
   open PomsetWithPredicateTransformers P₂ using () renaming (E to E₂ ; ℓ to ℓ₂ ; κ to κ₂ ; _≤_ to _≤₂_ ; τ to τ₂)

   field E₀⊆E₁∪E₂ : (E₀ ⊆ (E₁ ∪ E₂))
   field E₁⊆E₀ : (E₁ ⊆ E₀)
   field E₂⊆E₀ : (E₂ ⊆ E₀)

   field ≤₁⊆≤₀ : ∀ d e → (d ≤₁ e) → (d ≤₀ e)
   field ≤₂⊆≤₀ : ∀ d e → (d ≤₂ e) → (d ≤₀ e)

   lhs₀ = λ e → (ψ ∧ κ₁(e))
   rhs₀ = λ e → ((¬ ψ) ∧ κ₂(e))
   
   field κ₀⊨lhs₀ : ∀ e → (e ∈ E₁) → (e ∉ E₂) → (κ₀(e) ⊨ lhs₀(e))
   field κ₀⊨rhs₀ : ∀ e → (e ∉ E₁) → (e ∈ E₂) → (κ₀(e) ⊨ rhs₀(e))
   field κ₀⊨lhs₀∨rhs₀ : ∀ e → (e ∈ E₁) → (e ∈ E₂) → (κ₀(e) ⊨ (lhs₀(e) ∨ rhs₀(e)))
   
   field ℓ₀=ℓ₁ : ∀ e → (e ∈ E₁) → (ℓ₀(e) ≡ ℓ₁(e))
   field ℓ₀=ℓ₂ : ∀ e → (e ∈ E₂) → (ℓ₀(e) ≡ ℓ₂(e))
   
   field τ₀ϕ⊨τ₁ϕ : ∀ C ϕ → (ψ ∧ τ₀(C)(ϕ)) ⊨ τ₁(C)(ϕ)
   field τ₀ϕ⊨τ₂ϕ : ∀ C ϕ → ((¬ ψ) ∧ τ₀(C)(ϕ)) ⊨ τ₂(C)(ϕ)
