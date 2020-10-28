open import prelude
open import data-model using ( DataModel )
import command
import pomset

module semantics (DM : DataModel) (Event : Set) where

  open DataModel DM
  open command(DM)
  open pomset(DM)(Event)

  data SKIP (P₀ : Pomset) (e : Event) : Set where
  
    impl :
      let open Pomset P₀ using () renaming (pre to pre₀ ; post to post₀ ; act to act₀; V to V₀) in
      (e ∉ V₀) →
      (pre₀(e) ⊨ post₀(e)) →
      -------------------------
      (e ∈ SKIP P₀)

  data E-COMP (P₀ P₁ P₂ : Pomset) (e : Event) : Set where

    left :
      let open Pomset P₁ using () renaming (E to E₁ ; act to act₁ ; V to V₁) in
      (e ∈ V₁) →
      -------------------------      
      (e ∈ E-COMP P₀ P₁ P₂)
      
    right :
      let open Pomset P₂ using () renaming (E to E₂ ; act to act₂ ; V to V₂) in
      (e ∈ V₂) →
      -------------------------
      (e ∈ E-COMP P₀ P₁ P₂)
      
  data ℓ-COMP (P₀ P₁ P₂ : Pomset) (e : Event) : Set where

    cut :
      let open Pomset P₀ using () renaming (act to act₀ ; pre to pre₀ ; post to post₀ ; V to V₀) in
      let open Pomset P₁ using () renaming (E to E₁ ; act to act₁ ; pre to pre₁ ; post to post₁ ; V to V₁) in
      let open Pomset P₂ using () renaming (E to E₂ ; act to act₂ ; pre to pre₂ ; post to post₂ ; V to V₂) in
      (e ∈ E₁) →
      (e ∈ E₂) →
      (e ∉ V₀) →
      (e ∉ V₁) →
      (e ∉ V₂) →
      (pre₀(e) ⊨ pre₁(e)) →
      (post₁(e) ⊨ pre₂(e)) →
      (post₂(e) ⊨ post₀(e)) →
      -------------------------
      (e ∈ ℓ-COMP P₀ P₁ P₂)

    left :
      let open Pomset P₀ using () renaming (act to act₀ ; pre to pre₀ ; post to post₀) in
      let open Pomset P₁ using () renaming (E to E₁ ; act to act₁ ; pre to pre₁ ; post to post₁ ; V to V₁) in
      let open Pomset P₂ using () renaming (E to E₂) in
      (e ∈ V₁) →
      (e ∉ E₂) →
      (act₀(e) ≡ act₁(e)) →
      (pre₀(e) ⊨ pre₁(e)) →
      -------------------------
      (e ∈ ℓ-COMP P₀ P₁ P₂)

    right : ∀ {ϕ} →
      let open Pomset P₀ using () renaming (act to act₀ ; pre to pre₀ ; ↓ to ↓₀) in
      let open Pomset P₁ using () renaming (E to E₁ ; _⊨_⇝_ to _⊨₁_⇝_) in
      let open Pomset P₂ using () renaming (act to act₂ ; pre to pre₂ ; post to post₂ ; V to V₂) in
      (e ∉ E₁) →
      (e ∈ V₂) →
      (act₀(e) ≡ act₂(e)) →
      (pre₀(e) ⊨ ϕ) →
      (↓₀(e) ⊨₁ ϕ ⇝ pre₂(e)) →
      -------------------------
      (e ∈ ℓ-COMP P₀ P₁ P₂)

    both : ∀ {ϕ} →
      let open Pomset P₀ using () renaming (act to act₀ ; pre to pre₀ ; ↓ to ↓₀) in
      let open Pomset P₁ using () renaming (act to act₁ ; pre to pre₁ ; _⊨_⇝_ to _⊨₁_⇝_ ; V to V₁) in
      let open Pomset P₂ using () renaming (act to act₂ ; pre to pre₂ ; V to V₂) in
      (e ∈ V₁) →
      (e ∈ V₂) →
      (act₀(e) ≡ act₁(e)) →
      (act₀(e) ≡ act₂(e)) →
      (pre₀(e) ⊨ (pre₁(e) ∨ ϕ)) →
      (↓₀(e) ⊨₁ ϕ ⇝ pre₂(e)) →
      -------------------------
      (e ∈ ℓ-COMP P₀ P₁ P₂)

  data ≤-COMP (P₁ P₂ : Pomset) : (Event × Event) → Set where

    left : ∀ {d e} →
      let open Pomset P₁ using () renaming (_≤_ to _≤₁_) in
      (d ≤₁ e) →
      -------------------------
      ((d , e) ∈ ≤-COMP P₁ P₂)

    right : ∀ {d e} →
      let open Pomset P₂ using () renaming (_≤_ to _≤₂_) in
      (d ≤₂ e) →
      -------------------------
      ((d , e) ∈ ≤-COMP P₁ P₂)

    coherence : ∀ {d e} →
      let open Pomset P₁ using () renaming (E to E₁ ; act to act₁) in
      let open Pomset P₂ using () renaming (E to E₂ ; act to act₂) in
      (d ∈ E₁) →
      (e ∈ E₂) →
      (act₁(d) , act₂(e)) ∈ Conflicts →
      -------------------------
      ((d , e) ∈ ≤-COMP P₁ P₂)

  data ⟦_⟧ : Command → Pomset → Set₁ where

    ⟦skip⟧ : ∀ P₀ →
      let open Pomset P₀ using () renaming (E to E₀) in
      (∀ e → (e ∈ E₀) → (e ∈ SKIP P₀)) →
      (P₀ ∈ ⟦ skip ⟧)
      
    ⟦comp⟧ : ∀ C₁ C₂ P₀ P₁ P₂ →    
      let open Pomset P₀ using () renaming (_≤_ to _≤₀_ ; E to E₀) in
      (P₁ ∈ ⟦ C₁ ⟧) →
      (P₂ ∈ ⟦ C₂ ⟧) →
      (∀ e → (e ∈ E-COMP P₀ P₁ P₂) → (e ∈ E₀)) →
      (∀ e → (e ∈ E₀) → (e ∈ ℓ-COMP P₀ P₁ P₂)) →
      (∀ d e → ((d , e) ∈ ≤-COMP P₁ P₂) → (d ≤₀ e)) →
      (P₀ ∈ ⟦ C₁ ∙ C₂ ⟧)
