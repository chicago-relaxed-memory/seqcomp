open import prelude
open import data-model using ( DataModel )
import command
import pomset

module semantics (DM : DataModel) (Event : Set) where

  open DataModel DM
  open command(DM)
  open pomset(DM)(Event)
      
  data ℓ-COMP (P₀ P₁ P₂ : Pomset) (e : Event) : Set where

    cut :
      let open Pomset P₀ using () renaming (I to I₀ ; pre to pre₀ ; post to post₀) in
      let open Pomset P₁ using () renaming (I to I₁ ; pre to pre₁ ; post to post₁) in
      let open Pomset P₂ using () renaming (I to I₂ ; pre to pre₂ ; post to post₂) in
      (e ∈ I₀) →
      (e ∈ I₁) →
      (e ∈ I₂) →
      (pre₀(e) ⊨ pre₁(e)) →
      (post₁(e) ⊨ pre₂(e)) →
      (post₂(e) ⊨ post₀(e)) →
      -------------------------
      (e ∈ ℓ-COMP P₀ P₁ P₂)

    left :
      let open Pomset P₀ using () renaming (V to V₀ ; act to act₀ ; pre to pre₀) in
      let open Pomset P₁ using () renaming (V to V₁ ; act to act₁ ; pre to pre₁) in
      let open Pomset P₂ using () renaming (E to E₂) in
      (e ∈ V₀) →
      (e ∈ V₁) →
      (e ∉ E₂) →
      (act₀(e) ≡ act₁(e)) →
      (pre₀(e) ⊨ pre₁(e)) →
      -------------------------
      (e ∈ ℓ-COMP P₀ P₁ P₂)

    right : ∀ {ϕ} →
      let open Pomset P₀ using () renaming (V to V₀ ; act to act₀ ; pre to pre₀ ; ↓ to ↓₀) in
      let open Pomset P₁ using () renaming (E to E₁ ; _⊨_⇝_ to _⊨₁_⇝_) in
      let open Pomset P₂ using () renaming (V to V₂ ; act to act₂ ; pre to pre₂) in
      (e ∈ V₀) →
      (e ∉ E₁) →
      (e ∈ V₂) →
      (act₀(e) ≡ act₂(e)) →
      (pre₀(e) ⊨ ϕ) →
      (↓₀(e) ⊨₁ ϕ ⇝ pre₂(e)) →
      -------------------------
      (e ∈ ℓ-COMP P₀ P₁ P₂)

    both : ∀ {ϕ} →
      let open Pomset P₀ using () renaming (V to V₀ ; act to act₀ ; pre to pre₀ ; ↓ to ↓₀) in
      let open Pomset P₁ using () renaming (V to V₁ ; act to act₁ ; pre to pre₁ ; _⊨_⇝_ to _⊨₁_⇝_) in
      let open Pomset P₂ using () renaming (V to V₂ ; act to act₂ ; pre to pre₂) in
      (e ∈ V₀) →
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
      let open Pomset P₀ using () renaming (E to E₀ ; I to I₀ ; pre to pre₀ ; post to post₀) in
      (E₀ ⊆ I₀) →
      (∀ e → (e ∈ E₀) → (pre₀(e) ⊨ post₀(e))) →
      (P₀ ∈ ⟦ skip ⟧)
      
    ⟦comp⟧ : ∀ C₁ C₂ P₀ P₁ P₂ →    
      let open Pomset P₀ using () renaming (E to E₀ ; V to V₀ ; _≤_ to _≤₀_) in
      let open Pomset P₁ using () renaming (V to V₁) in
      let open Pomset P₂ using () renaming (V to V₂) in
      (P₁ ∈ ⟦ C₁ ⟧) →
      (P₂ ∈ ⟦ C₂ ⟧) →
      ((V₁ ∪ V₂) ⊆ V₀) →
      (∀ e → (e ∈ E₀) → (e ∈ ℓ-COMP P₀ P₁ P₂)) →
      (∀ d e → ((d , e) ∈ ≤-COMP P₁ P₂) → (d ≤₀ e)) →
      (P₀ ∈ ⟦ C₁ ∙ C₂ ⟧)
