open import prelude
open import data-model using ( DataModel )
import command
import pomset
import semantics

module properties (DM : DataModel) (Event : Set) where

  open DataModel DM
  open command(DM)
  open pomset(DM)(Event)
  open semantics(DM)(Event)

  right-unit-sub : ∀ C → ⟦ C ⟧ ⊆ ⟦ C ∙ skip ⟧
  right-unit-sub C P₀ P₀∈C = ⟦comp⟧ C skip P₀ P₀ P₂ P₀∈C P₂∈⟦skip⟧ lemma-E lemma-ℓ lemma-≤ where

    open Pomset P₀ renaming (E to E₀ ; ℓ to ℓ₀ ; act to act₀ ; post to post₀ ; pre to pre₀ ; _≤_ to _≤₀_ ; ≤-refl to ≤₀-refl )

    E₂ : Event → Set
    E₂ e = (e ∈ E₀) × (act₀(e) ∉ Visibles)

    ℓ₂ : Event → (Formula × Action)
    ℓ₂ e = (post₀(e) , ✓(post₀(e)))

    ✓-max₂ : ∀ {d e} → ((d ≡ e) × (d ≢ e)) → _
    ✓-max₂ (d=e , d≠e) = CONTRADICTION (d≠e d=e)
    
    P₂ : Pomset
    P₂ = record { E = E₂ ; _≤_ = _≡_ ; ℓ = ℓ₂ ; ✓-max = ✓-max₂ ; ≤-refl = refl ; ≤-trans = ≡-trans ; ≤-asym = (λ _ d=e → d=e) }

    open Pomset P₂ using () renaming (pre to pre₂)
    
    P₂∈⟦skip⟧ : P₂ ∈ ⟦ skip ⟧
    P₂∈⟦skip⟧ = ⟦skip⟧ P₂ (λ _ _ → impl (λ ()) ⊨-refl)

    lemma-E : (∀ e → (e ∈ E-COMP P₀ P₀ P₂) → (e ∈ E₀))
    lemma-E e (left e∈E₀ _) = e∈E₀
    
    lemma-ℓ : (∀ e → (e ∈ E₀) → (e ∈ ℓ-COMP P₀ P₀ P₂))
    lemma-ℓ e e∈E₀ with dec-vis(act₀(e)) 
    lemma-ℓ e e∈E₀ | yes a₀e∈V = left e∈E₀ (λ{ (_ , a₀e∉V) → a₀e∉V a₀e∈V }) a₀e∈V refl ⊨-refl
    lemma-ℓ e e∈E₀ | no  a₀e∉V = cut e∈E₀ (e∈E₀ , a₀e∉V) a₀e∉V a₀e∉V (λ ()) ⊨-refl ⊨-refl ⊨-refl
    
    lemma-≤ : (∀ d e → ((d , e) ∈ ≤-COMP P₀ P₀ P₂) → (d ≤₀ e))
    lemma-≤ d e (left d≤₀e) = d≤₀e
    lemma-≤ d .d (right refl) = ≤₀-refl
  
