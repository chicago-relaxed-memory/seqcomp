open import prelude
open import data-model using ( DataModel )
import command
import pomset

module semantics (DM : DataModel) (Event : Set) where

  open DataModel DM
  open command(DM)
  open pomset(DM)(Event)

  data SKIP (P₀ : Pomset) (e : Event) : Set where
  
    impl : ∀ {ϕ₀ ψ₀} →
      let open Pomset P₀ using () renaming (ℓ to ℓ₀) in
      (ℓ₀(e) ≡ (ϕ₀ , ✓ ψ₀)) →
      (ϕ₀ ⊨ ψ₀) →
      -------------------------
      (e ∈ SKIP P₀)

  data E-COMP (P₀ P₁ P₂ : Pomset) (e : Event) : Set where

    left :
      let open Pomset P₁ using () renaming (E to E₁ ; act to act₁) in
      (e ∈ E₁) →
      (act₁(e) ∈ ReadWrites) →
      (e ∈ E-COMP P₀ P₁ P₂)
      
    right :
      let open Pomset P₂ using () renaming (E to E₂ ; act to act₂) in
      (e ∈ E₂) →
      (act₂(e) ∈ ReadWrites) →
      (e ∈ E-COMP P₀ P₁ P₂)
      
  data ℓ-COMP (P₀ P₁ P₂ : Pomset) (e : Event) : Set where

    cut : ∀ {ϕ₀ ψ₀ ϕ₁ χ₁ χ₂ ψ₂} →
      let open Pomset P₀ using () renaming (ℓ to ℓ₀) in
      let open Pomset P₁ using () renaming (E to E₁ ; ℓ to ℓ₁) in
      let open Pomset P₂ using () renaming (E to E₂ ; ℓ to ℓ₂) in
      (e ∈ E₁) →
      (e ∈ E₂) →
      (ℓ₀(e) ≡ (ϕ₀ , ✓ ψ₀)) →
      (ℓ₁(e) ≡ (ϕ₁ , ✓ χ₁)) →
      (ℓ₂(e) ≡ (χ₂ , ✓ ψ₂)) →
      (ϕ₀ ⊨ ϕ₁) →
      (χ₁ ⊨ χ₂) →
      (ψ₂ ⊨ ψ₀) →
      -------------------------
      (e ∈ ℓ-COMP P₀ P₁ P₂)

    left : ∀ {a ϕ₀ ϕ₁} →
      let open Pomset P₀ using () renaming (ℓ to ℓ₀) in
      let open Pomset P₁ using () renaming (E to E₁ ; ℓ to ℓ₁) in
      let open Pomset P₂ using () renaming (E to E₂) in
      (a ∈ ReadWrites) →
      (e ∈ E₁) →
      (e ∉ E₂) →
      (ℓ₀(e) ≡ (ϕ₀ , a)) →
      (ℓ₁(e) ≡ (ϕ₁ , a)) →
      (ϕ₀ ⊨ ϕ₁) →
      -------------------------
      (e ∈ ℓ-COMP P₀ P₁ P₂)

    right : ∀ {a ϕ χ} →
      let open Pomset P₀ using () renaming (ℓ to ℓ₀ ; ↓ to ↓₀) in
      let open Pomset P₁ using () renaming (E to E₁ ; _⊨_⇝_ to _⊨₁_⇝_) in
      let open Pomset P₂ using () renaming (E to E₂ ; ℓ to ℓ₂) in
      (a ∈ ReadWrites) →
      (e ∉ E₁) →
      (e ∈ E₂) →
      (ℓ₀(e) ≡ (ϕ , a)) →
      (ℓ₂(e) ≡ (χ , a)) →
      (↓₀(e) ⊨₁ ϕ ⇝ χ) →
      -------------------------
      (e ∈ ℓ-COMP P₀ P₁ P₂)

    both : ∀ {a ϕ₀ ϕ₁ ϕ₂ χ₂} →
      let open Pomset P₀ using () renaming (ℓ to ℓ₀ ; ↓ to ↓₀) in
      let open Pomset P₁ using () renaming (E to E₁ ; ℓ to ℓ₁ ; _⊨_⇝_ to _⊨₁_⇝_) in
      let open Pomset P₂ using () renaming (E to E₂ ; ℓ to ℓ₂) in
      (a ∈ ReadWrites) →
      (e ∈ E₁) →
      (e ∈ E₂) →
      (ℓ₀(e) ≡ (ϕ₀ , a)) →
      (ℓ₁(e) ≡ (ϕ₁ , a)) →
      (ℓ₂(e) ≡ (χ₂ , a)) →
      (↓₀(e) ⊨₁ ϕ₂ ⇝ χ₂) →
      (ϕ₀ ⊨ (ϕ₁ ∨ ϕ₂)) →
      -------------------------
      (e ∈ ℓ-COMP P₀ P₁ P₂)

  data ≤-COMP (P₀ P₁ P₂ : Pomset) : (Event × Event) → Set where

    TODO : ∀ {d e} →
      -------------------------
      ((d , e) ∈ ≤-COMP P₀ P₁ P₂)

  data ⟦_⟧ : Command → Pomset → Set₁ where

    ⟦skip⟧ : ∀ P₀ →
      let open Pomset P₀ using () renaming (E to E₀) in
      (∀ {e} → (e ∈ E₀) → (e ∈ SKIP P₀)) →
      (P₀ ∈ ⟦ skip ⟧)
      
    ⟦comp⟧ : ∀ C₁ C₂ P₀ P₁ P₂ →    
      let open Pomset P₀ using () renaming (_≤_ to _≤₀_ ; E to E₀) in
      (P₁ ∈ ⟦ C₁ ⟧) →
      (P₂ ∈ ⟦ C₂ ⟧) →
      (∀ {e} → (e ∈ E-COMP P₀ P₁ P₂) → (e ∈ E₀)) →
      (∀ {e} → (e ∈ E₀) → (e ∈ ℓ-COMP P₀ P₁ P₂)) →
      (∀ {d e} → ((d , e) ∈ ≤-COMP P₀ P₁ P₂) → (d ≤₀ e)) →
      (P₀ ∈ ⟦ C₁ ∙ C₂ ⟧)
