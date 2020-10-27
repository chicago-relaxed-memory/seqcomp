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
      let open Pomset P₀ using () renaming (pre to pre₀ ; post to post₀ ; act to act₀) in
      (act₀(e) ∉ Visibles) →
      (pre₀(e) ⊨ post₀(e)) →
      -------------------------
      (e ∈ SKIP P₀)

  data E-COMP (P₀ P₁ P₂ : Pomset) (e : Event) : Set where

    left :
      let open Pomset P₁ using () renaming (E to E₁ ; act to act₁) in
      (e ∈ E₁) →
      (act₁(e) ∈ Visibles) →
      (e ∈ E-COMP P₀ P₁ P₂)
      
    right :
      let open Pomset P₂ using () renaming (E to E₂ ; act to act₂) in
      (e ∈ E₂) →
      (act₂(e) ∈ Visibles) →
      (e ∈ E-COMP P₀ P₁ P₂)
      
  data ℓ-COMP (P₀ P₁ P₂ : Pomset) (e : Event) : Set where

    cut :
      let open Pomset P₀ using () renaming (act to act₀ ; pre to pre₀ ; post to post₀) in
      let open Pomset P₁ using () renaming (E to E₁ ; act to act₁ ; pre to pre₁ ; post to post₁) in
      let open Pomset P₂ using () renaming (E to E₂ ; act to act₂ ; pre to pre₂ ; post to post₂) in
      (e ∈ E₁) →
      (e ∈ E₂) →
      (act₀(e) ∉ Visibles) →
      (act₁(e) ∉ Visibles) →
      (act₂(e) ∉ Visibles) →
      (pre₀(e) ⊨ pre₁(e)) →
      (post₁(e) ⊨ pre₂(e)) →
      (post₂(e) ⊨ post₀(e)) →
      -------------------------
      (e ∈ ℓ-COMP P₀ P₁ P₂)

    left :
      let open Pomset P₀ using () renaming (act to act₀ ; pre to pre₀ ; post to post₀) in
      let open Pomset P₁ using () renaming (E to E₁ ; act to act₁ ; pre to pre₁ ; post to post₁) in
      let open Pomset P₂ using () renaming (E to E₂) in
      (e ∈ E₁) →
      (e ∉ E₂) →
      (act₀(e) ∈ Visibles) →
      (act₀(e) ≡ act₁(e)) →
      (pre₀(e) ⊨ pre₁(e)) →
      -------------------------
      (e ∈ ℓ-COMP P₀ P₁ P₂)

    right :
      let open Pomset P₀ using () renaming (act to act₀ ; pre to pre₀ ; ↓ to ↓₀) in
      let open Pomset P₁ using () renaming (E to E₁ ; _⊨_⇝_ to _⊨₁_⇝_) in
      let open Pomset P₂ using () renaming (E to E₂ ; act to act₂ ; pre to pre₂ ; post to post₂) in
      (e ∉ E₁) →
      (e ∈ E₂) →
      (act₀(e) ∈ Visibles) →
      (act₀(e) ≡ act₂(e)) →
      (↓₀(e) ⊨₁ pre₀(e) ⇝ pre₂(e)) →
      -------------------------
      (e ∈ ℓ-COMP P₀ P₁ P₂)

    both : ∀ {ϕ} →
      let open Pomset P₀ using () renaming (pre to pre₀ ; ↓ to ↓₀) in
      let open Pomset P₁ using () renaming (E to E₁ ; pre to pre₁ ; _⊨_⇝_ to _⊨₁_⇝_) in
      let open Pomset P₂ using () renaming (E to E₂ ; pre to pre₂) in
      (e ∈ E₁) →
      (e ∈ E₂) →
      (↓₀(e) ⊨₁ ϕ ⇝ pre₂(e)) →
      (pre₀(e) ⊨ (pre₁(e) ∨ ϕ)) →
      -------------------------
      (e ∈ ℓ-COMP P₀ P₁ P₂)

  data ≤-COMP (P₀ P₁ P₂ : Pomset) : (Event × Event) → Set where

    left : ∀ {d e} →
      let open Pomset P₁ using () renaming (_≤_ to _≤₁_) in
      (d ≤₁ e) →
      -------------------------
      ((d , e) ∈ ≤-COMP P₀ P₁ P₂)

    right : ∀ {d e} →
      let open Pomset P₂ using () renaming (_≤_ to _≤₂_) in
      (d ≤₂ e) →
      -------------------------
      ((d , e) ∈ ≤-COMP P₀ P₁ P₂)

    coherence : ∀ {d e} →
      let open Pomset P₂ using () renaming (E to E₁ ; act to act₁) in
      let open Pomset P₂ using () renaming (E to E₂ ; act to act₂) in
      (d ∈ E₁) →
      (e ∈ E₂) →
      (act₁(d) , act₂(e)) ∈ Conflicts →
      -------------------------
      ((d , e) ∈ ≤-COMP P₀ P₁ P₂)

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
      (∀ d e → ((d , e) ∈ ≤-COMP P₀ P₁ P₂) → (d ≤₀ e)) →
      (P₀ ∈ ⟦ C₁ ∙ C₂ ⟧)
