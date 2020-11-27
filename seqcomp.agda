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
   
   open PomsetWithPredicateTransformers P₀ using () renaming (E to E₀ ; act to act₀ ; pre to pre₀ ; _≤_ to _≤₀_ ; ↓ to ↓₀ ; τ to τ₀)
   open PomsetWithPredicateTransformers P₁ using () renaming (E to E₁ ; act to act₁ ; pre to pre₁ ; _≤_ to _≤₁_ ; ↓ to ↓₁ ; τ to τ₁)
   open PomsetWithPredicateTransformers P₂ using () renaming (E to E₂ ; act to act₂ ; pre to pre₂ ; _≤_ to _≤₂_ ; ↓ to ↓₂ ; τ to τ₂)

   field E₀⊆E₁∪E₂ : (E₀ ⊆ (E₁ ∪ E₂))
   field E₁⊆E₀ : (E₁ ⊆ E₀)
   field E₂⊆E₀ : (E₂ ⊆ E₀)

   E₁∪E₂⊆E₀ : ((E₁ ∪ E₂) ⊆ E₀)
   E₁∪E₂⊆E₀ = ⊆-elim-∪ E₁⊆E₀ E₂⊆E₀
   
   field ≤₁⊆≤₀ : ∀ d e → (d ≤₁ e) → (d ≤₀ e)
   field ≤₂⊆≤₀ : ∀ d e → (d ≤₂ e) → (d ≤₀ e)
   field causal :  ∀ d e → (d ∈ E₁) → (e ∈ E₂) → (Causal (act₁(d)) (act₂(e))) → (d ≤₀ e)

   lhs₀ : Event → Formula
   lhs₀ = pre₁

   rhs₀ : Event → Formula
   rhs₀(e) = τ₁(↓₀(e))(pre₂(e))
   
   field pre₀⊨lhs₀ : ∀ e → (e ∈ E₁) → (e ∉ E₂) → (pre₀(e) ⊨ lhs₀(e))
   field pre₀⊨rhs₀ : ∀ e → (e ∉ E₁) → (e ∈ E₂) → (pre₀(e) ⊨ rhs₀(e))
   field pre₀⊨lhs₀∨rhs₀ : ∀ e → (e ∈ E₁) → (e ∈ E₂) → (pre₀(e) ⊨ (lhs₀(e) ∨ rhs₀(e)))
   
   field act₀=act₁ : ∀ e → (e ∈ E₁) → (act₀(e) ≡ act₁(e))
   field act₀=act₂ : ∀ e → (e ∈ E₂) → (act₀(e) ≡ act₂(e))
   
   field τ₀ϕ⊨τ₁τ₂ϕ : ∀ C ϕ → τ₀(C)(ϕ) ⊨ τ₁(C)(τ₂(C)(ϕ))
  
  record IF (ψ : Formula) (𝒫₁ 𝒫₂ : PomsetWithPredicateTransformers → Set₁) (P₀ : PomsetWithPredicateTransformers) : Set₁ where

   field P₁ : PomsetWithPredicateTransformers
   field P₂ : PomsetWithPredicateTransformers
   field P₁∈𝒫₁ : P₁ ∈ 𝒫₁
   field P₂∈𝒫₂ : P₂ ∈ 𝒫₂
   
   open PomsetWithPredicateTransformers P₀ using () renaming (E to E₀ ; act to act₀ ; pre to pre₀ ; _≤_ to _≤₀_ ; τ to τ₀)
   open PomsetWithPredicateTransformers P₁ using () renaming (E to E₁ ; act to act₁ ; pre to pre₁ ; _≤_ to _≤₁_ ; τ to τ₁)
   open PomsetWithPredicateTransformers P₂ using () renaming (E to E₂ ; act to act₂ ; pre to pre₂ ; _≤_ to _≤₂_ ; τ to τ₂)

   field E₀⊆E₁∪E₂ : (E₀ ⊆ (E₁ ∪ E₂))
   field E₁⊆E₀ : (E₁ ⊆ E₀)
   field E₂⊆E₀ : (E₂ ⊆ E₀)

   field ≤₁⊆≤₀ : ∀ d e → (d ≤₁ e) → (d ≤₀ e)
   field ≤₂⊆≤₀ : ∀ d e → (d ≤₂ e) → (d ≤₀ e)

   lhs₀ = λ e → (ψ ∧ pre₁(e))
   rhs₀ = λ e → ((¬ ψ) ∧ pre₂(e))
   
   field pre₀⊨lhs₀ : ∀ e → (e ∈ E₁) → (e ∉ E₂) → (pre₀(e) ⊨ lhs₀(e))
   field pre₀⊨rhs₀ : ∀ e → (e ∉ E₁) → (e ∈ E₂) → (pre₀(e) ⊨ rhs₀(e))
   field pre₀⊨lhs₀∨rhs₀ : ∀ e → (e ∈ E₁) → (e ∈ E₂) → (pre₀(e) ⊨ (lhs₀(e) ∨ rhs₀(e)))
   
   field act₀=act₁ : ∀ e → (e ∈ E₁) → (act₀(e) ≡ act₁(e))
   field act₀=act₂ : ∀ e → (e ∈ E₂) → (act₀(e) ≡ act₂(e))
   
   field τ₀ϕ⊨τ₁ϕ : ∀ C ϕ → (ψ ∧ τ₀(C)(ϕ)) ⊨ τ₁(C)(ϕ)
   field τ₀ϕ⊨τ₂ϕ : ∀ C ϕ → ((¬ ψ) ∧ τ₀(C)(ϕ)) ⊨ τ₂(C)(ϕ)
