open import prelude
open import data-model using ( DataModel )
import command
import pomset
import semantics
import augmentation
import examples

module monoid (DM : DataModel) (Event : Set) where

  open DataModel DM
  open command(DM)
  open pomset(DM)(Event)
  open semantics(DM)(Event)
  open augmentation(DM)(Event)
  open examples(DM)(Event)

  -- PROPOSITION: sequential composition forms a monoid
  
  ⟦C⟧⊆⟦C∙skip⟧ : ∀ C → ⟦ C ⟧ ⊆ ⟦ C ∙ skip ⟧
  ⟦C∙skip⟧⊆⟦C⟧ : ∀ C → ⟦ C ∙ skip ⟧ ⊆ ⟦ C ⟧

  ⟦C⟧⊆⟦skip∙C⟧ : ∀ C → ⟦ C ⟧ ⊆ ⟦ skip ∙ C ⟧
  ⟦skip∙C⟧⊆⟦C⟧ : ∀ C → ⟦ skip ∙ C ⟧ ⊆ ⟦ C ⟧

  ⟦C₁∙⟨C₂∙C₃⟩⟧⊆⟦⟨C₁∙C₂⟩∙C₃⟧ : ∀ C₁ C₂ C₃ → ⟦ C₁ ∙ (C₂ ∙ C₃) ⟧ ⊆ ⟦ (C₁ ∙ C₂) ∙ C₃ ⟧
  ⟦⟨C₁∙C₂⟩∙C₃⟧⊆⟦C₁∙⟨C₂∙C₃⟩⟧ : ∀ C₁ C₂ C₃ → ⟦ (C₁ ∙ C₂) ∙ C₃ ⟧ ⊆ ⟦ C₁ ∙ (C₂ ∙ C₃) ⟧

  -- PROOF that skip is a right unit
  
  ⟦C⟧⊆⟦C∙skip⟧ C P₀ P₀∈⟦C⟧ = P₀∈⟦C∙skip⟧ where

    open Pomset P₀ using () renaming (act to act₀ ; ≤-refl to ≤₀-refl)

    P₀∈⟦C∙skip⟧ : P₀ ∈ ⟦ C ∙ skip ⟧
    P₀∈⟦C∙skip⟧ = record
                    { P₁ = P₀
                    ; P₂ = skipP act₀
                    ; P₁∈𝒫₁ = P₀∈⟦C⟧
                    ; P₂∈𝒫₂ = skipP∈⟦skip⟧ act₀
                    ; E₀⊆E₁∪E₂ = ⊆-left-∪
                    ; E₁⊆E₀ = ⊆-refl
                    ; E₂⊆E₀ = ⊆-elim-∅
                    ; ≤₁⊆≤₀ = λ d e d≤₀e → d≤₀e
                    ; ≤₂⊆≤₀ = λ { e .e refl → ≤₀-refl }
                    ; coherence = λ d e d∈E₀ ()
                    ; pre₀⊨lhs₀ = λ e e∈E₀ e∉E₂ → ⊨-refl
                    ; pre₀⊨rhs₀ = λ e e∉E₀ ()
                    ; pre₀⊨lhs₀∨rhs₀ = λ e e∈E₀ () 
                    ; act₀=act₁ = λ e e∈E₀ → refl
                    ; act₀=act₂ = λ e ()
                    ; τ₀ϕ⊨τ₁τ₂ϕ = λ C ϕ → ⊨-refl
                    }

  ⟦C∙skip⟧⊆⟦C⟧ C P₀ P₀∈⟦C∙skip⟧ = P₀∈⟦C⟧ where

    open _●_ P₀∈⟦C∙skip⟧ using (P₁ ; P₂ ; E₀⊆E₁∪E₂ ; E₁⊆E₀ ; E₂⊆E₀ ; act₀=act₁ ; pre₀⊨lhs₀ ; ≤₁⊆≤₀ ; τ₀ϕ⊨τ₁τ₂ϕ) renaming (P₁∈𝒫₁ to P₁∈⟦C⟧ ; P₂∈𝒫₂ to P₂∈⟦skip⟧)
    open SKIP P₂∈⟦skip⟧ using () renaming (E₀⊆∅ to E₂⊆∅ ; τ₀ϕ⊨ϕ to τ₂ϕ⊨ϕ)

    open Pomset P₀ using () renaming (E to E₀)
    open Pomset P₁ using () renaming (E to E₁ ; τ-resp-⊨ to τ₁-resp-⊨)
    open Pomset P₂ using () renaming (E to E₂)

    P₁≲P₀ : P₁ ≲ P₀
    P₁≲P₀ = record
              { E′⊆E = ⊆-trans E₀⊆E₁∪E₂ (⊆-elim-∪ ⊆-refl (⊆-trans E₂⊆∅ ⊆-elim-∅))
              ; E⊆E′ = E₁⊆E₀
              ; act=act′ = λ e e∈E₁ → ≡-symm (act₀=act₁ e e∈E₁)
              ; pre′⊨pre = λ e e∈E₁ → pre₀⊨lhs₀ e e∈E₁ (E₂⊆∅ e)
              ; ≤⊆≤′ = ≤₁⊆≤₀
              ; τ′⊨τ = λ C ϕ → ⊨-trans (τ₀ϕ⊨τ₁τ₂ϕ C ϕ) (τ₁-resp-⊨ (τ₂ϕ⊨ϕ C ϕ))
              }
    
    P₀∈⟦C⟧ = sem-resp-≲ P₁≲P₀ P₁∈⟦C⟧

  -- PROOF that skip is a left unit

  ⟦C⟧⊆⟦skip∙C⟧ C P₀ P₀∈⟦C⟧ = P₀∈⟦skip∙C⟧ where

    open Pomset P₀ using () renaming (act to act₀ ; ≤-refl to ≤₀-refl)

    P₀∈⟦skip∙C⟧ : P₀ ∈ ⟦ skip ∙ C ⟧
    P₀∈⟦skip∙C⟧ = record
                    { P₁ = skipP act₀
                    ; P₂ = P₀
                    ; P₁∈𝒫₁ = skipP∈⟦skip⟧ act₀
                    ; P₂∈𝒫₂ = P₀∈⟦C⟧
                    ; E₀⊆E₁∪E₂ = ⊆-right-∪
                    ; E₁⊆E₀ = ⊆-elim-∅
                    ; E₂⊆E₀ = ⊆-refl
                    ; ≤₁⊆≤₀ = λ { e .e refl → ≤₀-refl }
                    ; ≤₂⊆≤₀ = λ d e d≤₀e → d≤₀e
                    ; coherence = λ d e ()
                    ; pre₀⊨lhs₀ = λ e ()
                    ; pre₀⊨rhs₀ = λ e e∉E₁ e∈E₀ → ⊨-refl
                    ; pre₀⊨lhs₀∨rhs₀ = λ e ()
                    ; act₀=act₁ = λ e ()
                    ; act₀=act₂ = λ e e∈E₀ → refl
                    ; τ₀ϕ⊨τ₁τ₂ϕ = λ C ϕ → ⊨-refl
                    }
  
  ⟦skip∙C⟧⊆⟦C⟧ C P₀ P₀∈⟦skip∙C⟧ = P₀∈⟦C⟧ where
  
    open _●_ P₀∈⟦skip∙C⟧ using (P₁ ; P₂ ; E₀⊆E₁∪E₂ ; E₁⊆E₀ ; E₂⊆E₀ ; act₀=act₂ ; rhs₀ ; pre₀⊨rhs₀ ; ≤₂⊆≤₀ ; τ₀ϕ⊨τ₁τ₂ϕ) renaming (P₁∈𝒫₁ to P₁∈⟦skip⟧ ; P₂∈𝒫₂ to P₂∈⟦C⟧)
    open SKIP P₁∈⟦skip⟧ using () renaming (E₀⊆∅ to E₁⊆∅ ; τ₀ϕ⊨ϕ to τ₁ϕ⊨ϕ)

    open Pomset P₀ using () renaming (E to E₀ ; ↓RW to ↓RW₀)
    open Pomset P₁ using () renaming (E to E₁)
    open Pomset P₂ using () renaming (E to E₂ ; pre to pre₂ ; τ to τ₂ ; τ-resp-⊨ to τ₂-resp-⊨)

    P₂≲P₀ : P₂ ≲ P₀
    P₂≲P₀ = record
              { E′⊆E = ⊆-trans E₀⊆E₁∪E₂ (⊆-elim-∪ (⊆-trans E₁⊆∅ ⊆-elim-∅) ⊆-refl)
              ; E⊆E′ = E₂⊆E₀
              ; act=act′ = λ e e∈E₀ → ≡-symm (act₀=act₂ e e∈E₀)
              ; pre′⊨pre = λ e e∈E₂ → ⊨-trans (pre₀⊨rhs₀ e (E₁⊆∅ e) e∈E₂) (τ₁ϕ⊨ϕ (↓RW₀(e)) (pre₂(e)))
              ; ≤⊆≤′ =  ≤₂⊆≤₀
              ; τ′⊨τ = λ C ϕ → ⊨-trans (τ₀ϕ⊨τ₁τ₂ϕ C ϕ) (τ₁ϕ⊨ϕ C (τ₂ C ϕ))
              }
    
    P₀∈⟦C⟧ = sem-resp-≲ P₂≲P₀ P₂∈⟦C⟧
  
  -- PROOF of associativity

  ⟦C₁∙⟨C₂∙C₃⟩⟧⊆⟦⟨C₁∙C₂⟩∙C₃⟧ C₁ C₂ C₃ P₀ P₀∈⟦C₁∙⟨C₂∙C₃⟩⟧ =  P₀∈⟦⟨C₁∙C₂⟩∙C₃⟧ where

     open _●_ P₀∈⟦C₁∙⟨C₂∙C₃⟩⟧ using (P₁ ; E₁⊆E₀ ; ≤₁⊆≤₀ ; act₀=act₁ ; rhs₀ ; pre₀⊨lhs₀ ; pre₀⊨rhs₀ ; pre₀⊨lhs₀∨rhs₀) renaming (P₂ to P₂₃ ; P₁∈𝒫₁ to P₁∈⟦C₁⟧ ; P₂∈𝒫₂ to P₂₃∈⟦C₂∙C₃⟧ ; E₂⊆E₀ to E₂₃⊆E₀ ; E₀⊆E₁∪E₂ to E₀⊆E₁∪E₂₃ ; RE₀∩E₂⊆RE₂ to RE₀∩E₂₃⊆RE₂₃ ; WE₀∩E₂⊆WE₂ to WE₀∩E₂₃⊆WE₂₃ ; act₀=act₂ to act₀=act₂₃ ; ≤₂⊆≤₀ to ≤₂₃⊆≤₀ ; coherence to coherence₀ ; τ₀ϕ⊨τ₁τ₂ϕ to τ₀ϕ⊨τ₁τ₂₃ϕ)
     open _●_ P₂₃∈⟦C₂∙C₃⟧ using () renaming (P₁ to P₂ ; P₂ to P₃ ; P₁∈𝒫₁ to P₂∈⟦C₂⟧ ; P₂∈𝒫₂ to P₃∈⟦C₃⟧ ; rhs₀ to rhs₂₃ ; E₁⊆E₀ to E₂⊆E₂₃ ; E₂⊆E₀ to E₃⊆E₂₃ ; E₀⊆E₁∪E₂ to E₂₃⊆E₂∪E₃ ; ≤₁⊆≤₀ to ≤₂⊆≤₂₃ ; ≤₂⊆≤₀ to ≤₃⊆≤₂₃ ; act₀=act₁ to act₂₃=act₂ ; act₀=act₂ to act₂₃=act₃ ; pre₀⊨lhs₀ to pre₂₃⊨lhs₂₃ ; pre₀⊨rhs₀ to pre₂₃⊨rhs₂₃ ; pre₀⊨lhs₀∨rhs₀ to pre₂₃⊨lhs₂₃∨rhs₂₃ ; coherence to coherence₂₃; τ₀ϕ⊨τ₁τ₂ϕ to τ₂₃ϕ⊨τ₂τ₃ϕ)
     
     open Pomset P₀ using () renaming (E to E₀ ; act to act₀ ; pre to pre₀ ; _≤_ to _≤₀_ ; ≤-refl to ≤₀-refl ; ≤-trans to ≤₀-trans ; ≤-asym to ≤₀-asym ; RE to RE₀ ; WE to WE₀ ; ↓RW to ↓RW₀ ; PO to PO₀)
     open Pomset P₁ using () renaming (E to E₁ ; dec-E to dec-E₁ ; ℓ to ℓ₁ ; act to act₁ ; pre to pre₁ ; τ to τ₁ ; τ-resp-⊆ to τ₁-resp-⊆ ; τ-resp-∩⊆ to τ₁-resp-∩⊆ ; τ-resp-⊨ to τ₁-resp-⊨ ; τ-resp-∨ to τ₁-resp-∨)
     open Pomset P₂ using () renaming (E to E₂ ; dec-E to dec-E₂ ; ℓ to ℓ₂ ; act to act₂ ; pre to pre₂ ; τ to τ₂ ; τ-resp-⊆ to τ₂-resp-⊆ ; τ-resp-∩⊆ to τ₂-resp-∩⊆ ; τ-resp-⊨ to τ₂-resp-⊨)
     open Pomset P₃ using () renaming (E to E₃ ; act to act₃ ; pre to pre₃ ; τ to τ₃)
     open Pomset P₂₃ using () renaming (E to E₂₃ ; τ to τ₂₃ ; pre to pre₂₃; ↓RW to ↓RW₂₃ ; RE to RE₂₃ ; WE to WE₂₃)

     P₁₂ : Pomset
     P₁₂ = compP act₀ PO₀ P₁ P₂

     P₁₂₃ : Pomset
     P₁₂₃ = compP act₀ PO₀ P₁₂ P₃

     open Pomset P₁₂ using () renaming (E to E₁₂ ; pre to pre₁₂ ; dec-E to dec-E₁₂ ; RE to RE₁₂ ; WE to WE₁₂ ; ↓RW to ↓RW₁₂)
     open Pomset P₁₂₃ using () renaming (E to E₁₂₃ ; pre to pre₁₂₃ ; dec-E to dec-E₁₂₃ ; RE to RE₁₂₃ ; WE to WE₁₂₃ ; ↓RW to ↓RW₁₂₃)
     
     act₀=act₂ : ∀ e → (e ∈ E₂) → (act₀(e) ≡ act₂(e))
     act₀=act₂ e e∈E₂ = ≡-trans (act₀=act₂₃ e (E₂⊆E₂₃ e e∈E₂)) (act₂₃=act₂ e e∈E₂)
     
     act₀=act₃ : ∀ e → (e ∈ E₃) → (act₀(e) ≡ act₃(e))
     act₀=act₃ e e∈E₃ = ≡-trans (act₀=act₂₃ e (E₃⊆E₂₃ e e∈E₃)) (act₂₃=act₃ e e∈E₃)

     coherence₁₂ : ∀ d e → (d ∈ E₁) → (e ∈ E₂) → Conflicts (act₁ d) (act₂ e) → (d ≤₀ e)
     coherence₁₂ d e d∈E₁ e∈E₂ a₁#a₂ = coherence₀ d e d∈E₁ (E₂⊆E₂₃ e e∈E₂) (≡-subst₂ Conflicts refl (≡-symm (act₂₃=act₂ e e∈E₂)) a₁#a₂)
     
     coherence₁₂₃ : ∀ d e → (d ∈ E₁₂) → (e ∈ E₃) → Conflicts (act₀ d) (act₃ e) → (d ≤₀ e)
     coherence₁₂₃ d e (left d∈E₁ _) e∈E₃ a₁₂#a₃ = coherence₀ d e d∈E₁ (E₃⊆E₂₃ e e∈E₃) (≡-subst₂ Conflicts (act₀=act₁ d d∈E₁) (≡-symm (act₂₃=act₃ e e∈E₃)) a₁₂#a₃)
     coherence₁₂₃ d e (right _ d∈E₂) e∈E₃ a₁₂#a₃ = ≤₂₃⊆≤₀ d e (coherence₂₃ d e d∈E₂ e∈E₃ (≡-subst₂ Conflicts (act₀=act₂ d d∈E₂) refl a₁₂#a₃))
     coherence₁₂₃ d e (both d∈E₁ _) e∈E₃ a₁₂#a₃ = coherence₀ d e d∈E₁ (E₃⊆E₂₃ e e∈E₃) (≡-subst₂ Conflicts (act₀=act₁ d d∈E₁) (≡-symm (act₂₃=act₃ e e∈E₃)) a₁₂#a₃)
     
     PO₀∈CompP₁P₂ : Compatible act₀ PO₀ P₁ P₂
     PO₀∈CompP₁P₂ = record
                      { act₀=act₁ = act₀=act₁
                      ; act₀=act₂ = act₀=act₂
                      ; ≤₁⊆≤₀ = ≤₁⊆≤₀
                      ; ≤₂⊆≤₀ = λ d e d≤₂e → ≤₂₃⊆≤₀ d e (≤₂⊆≤₂₃ d e d≤₂e)
                      ; coherence = coherence₁₂ }
     
     PO₀∈CompP₁₂P₃ : Compatible act₀ PO₀ P₁₂ P₃
     PO₀∈CompP₁₂P₃ = record
                       { act₀=act₁ = λ e e∈E₁₂ → refl
                       ; act₀=act₂ = act₀=act₃
                       ; ≤₁⊆≤₀ = λ d e d≤₀e → d≤₀e
                       ; ≤₂⊆≤₀ = λ d e d≤₃e → ≤₂₃⊆≤₀ d e (≤₃⊆≤₂₃ d e d≤₃e)
                       ; coherence = coherence₁₂₃ }
     
     P₁₂∈⟦C₁∙C₂⟧ : P₁₂ ∈ ⟦ C₁ ∙ C₂ ⟧
     P₁₂∈⟦C₁∙C₂⟧ = compP∈⟦C₁∙C₂⟧ C₁ C₂ act₀ PO₀ P₁ P₂ P₁∈⟦C₁⟧ P₂∈⟦C₂⟧ PO₀∈CompP₁P₂
     
     P₁₂₃∈⟦⟨C₁∙C₂⟩∙C₃⟧ : P₁₂₃ ∈ ⟦ (C₁ ∙ C₂) ∙ C₃ ⟧
     P₁₂₃∈⟦⟨C₁∙C₂⟩∙C₃⟧ = compP∈⟦C₁∙C₂⟧ (C₁ ∙ C₂) C₃ act₀ PO₀ P₁₂ P₃ P₁₂∈⟦C₁∙C₂⟧ P₃∈⟦C₃⟧ PO₀∈CompP₁₂P₃

     open _●_ P₁₂∈⟦C₁∙C₂⟧ using () renaming (E₁⊆E₀ to E₁⊆E₁₂ ; E₂⊆E₀ to E₂⊆E₁₂ ; rhs₀ to rhs₁₂ ; pre₀⊨rhs₀ to pre₁₂⊨rhs₁₂)
     open _●_ P₁₂₃∈⟦⟨C₁∙C₂⟩∙C₃⟧ using () renaming (lhs₀ to lhs₁₂₃ ; rhs₀ to rhs₁₂₃ ; pre₀⊨rhs₀ to pre₁₂₃⊨rhs₁₂₃)
     
     E₁₂⊆E₀ : E₁₂ ⊆ E₀
     E₁₂⊆E₀ = ⊆-elim-∪ E₁⊆E₀ (⊆-trans E₂⊆E₂₃ E₂₃⊆E₀)
     
     E₁₂₃⊆E₀ : E₁₂₃ ⊆ E₀
     E₁₂₃⊆E₀ = ⊆-elim-∪ E₁₂⊆E₀ (⊆-trans E₃⊆E₂₃ E₂₃⊆E₀) 
     
     E₀⊆E₁₂₃ : E₀ ⊆ E₁₂₃
     E₀⊆E₁₂₃ = ⊆-trans E₀⊆E₁∪E₂₃ (⊆-trans (⊆-resp-∪ ⊆-refl E₂₃⊆E₂∪E₃) ⊆-assocl-∪)

     E₂₃⊆E₁₂₃ : E₂₃ ⊆ E₁₂₃
     E₂₃⊆E₁₂₃ = ⊆-trans E₂₃⊆E₀ E₀⊆E₁₂₃

     RE₁₂⊆RE₀ : RE₁₂ ⊆ RE₀
     RE₁₂⊆RE₀ = ⊆-resp-∩⁻¹ (λ _ _ → refl) E₁₂⊆E₀ Reads

     RE₁₂₃⊆RE₀ : RE₁₂₃ ⊆ RE₀
     RE₁₂₃⊆RE₀  = ⊆-resp-∩⁻¹ (λ _ _ → refl) E₁₂₃⊆E₀ Reads

     RE₁₂₃∩E₂₃⊆RE₂₃ : (RE₁₂₃ ∩ E₂₃) ⊆ RE₂₃
     RE₁₂₃∩E₂₃⊆RE₂₃ = ⊆-refl-∩⁻¹ act₀=act₂₃ E₂₃⊆E₁₂₃ Reads

     WE₁₂⊆WE₀ : WE₁₂ ⊆ WE₀
     WE₁₂⊆WE₀ = ⊆-resp-∩⁻¹ (λ _ _ → refl) E₁₂⊆E₀ Writes

     WE₁₂₃⊆WE₀ : WE₁₂₃ ⊆ WE₀
     WE₁₂₃⊆WE₀  = ⊆-resp-∩⁻¹ (λ _ _ → refl) E₁₂₃⊆E₀ Writes

     WE₁₂₃∩E₂₃⊆WE₂₃ : (WE₁₂₃ ∩ E₂₃) ⊆ WE₂₃
     WE₁₂₃∩E₂₃⊆WE₂₃ = ⊆-refl-∩⁻¹ act₀=act₂₃ E₂₃⊆E₁₂₃ Writes
     
     RW↓₀⊆↓RW₁₂₃ : ∀ e → (↓RW₀(e) ⊆ ↓RW₁₂₃(e))
     RW↓₀⊆↓RW₁₂₃ e = ⊆-resp-∩ E₀⊆E₁₂₃ (λ d d∈↓RWe d∈RE₁₂₃ e∈WE₁₂₃ → d∈↓RWe (RE₁₂₃⊆RE₀ d d∈RE₁₂₃) (WE₁₂₃⊆WE₀ e e∈WE₁₂₃))
     
     RW↓₀∩E₁₂⊆↓RW₁₂ : ∀ e → (e ∈ E₁₂) → ((↓RW₀(e) ∩ E₁₂) ⊆ ↓RW₁₂(e))
     RW↓₀∩E₁₂⊆↓RW₁₂ e e∈E₁₂  d ((d∈E₀ , d∈↓RWe) , d∈E₁₂) = (d∈E₁₂ , λ d∈RE₁₂ e∈RE₁₂ → d∈↓RWe (RE₁₂⊆RE₀ d d∈RE₁₂) (WE₁₂⊆WE₀ e e∈RE₁₂))
     
     RW↓₀∩E₁⊆↓RW₁₂ : ∀ e → (e ∈ E₁₂) → ((↓RW₀(e) ∩ E₁) ⊆ ↓RW₁₂(e))
     RW↓₀∩E₁⊆↓RW₁₂ e e∈E₁₂ d (d∈↓RWe , d∈E₁) = RW↓₀∩E₁₂⊆↓RW₁₂ e e∈E₁₂ d (d∈↓RWe , (E₁⊆E₁₂ d d∈E₁))
     
     RW↓₂₃⊆↓RW₁₂₃ : ∀ e → (e ∈ E₂₃) → (↓RW₂₃(e) ⊆ ↓RW₁₂₃(e))
     RW↓₂₃⊆↓RW₁₂₃ e e∈E₂₃ d (d∈E₂₃ , d∈↓RWe) = (E₂₃⊆E₁₂₃ d d∈E₂₃ , λ d∈RE₁₂₃ e∈WE₁₂₃ → ≤₂₃⊆≤₀ d e (d∈↓RWe (RE₁₂₃∩E₂₃⊆RE₂₃ d (d∈RE₁₂₃ , d∈E₂₃)) (WE₁₂₃∩E₂₃⊆WE₂₃ e (e∈WE₁₂₃ , e∈E₂₃))))
          
     rhs₀⊨rhs₁₂ : ∀ e → (e ∈ E₂) → (e ∉ E₃) → (rhs₀ e) ⊨ (rhs₁₂ e)
     rhs₀⊨rhs₁₂ e e∈E₂ e∉E₂ = ⊨-trans (τ₁-resp-∩⊆ (RW↓₀∩E₁⊆↓RW₁₂ e (E₂⊆E₁₂ e e∈E₂))) (τ₁-resp-⊨ (pre₂₃⊨lhs₂₃ e e∈E₂ e∉E₂))
     
     rhs₀⊨rhs₁₂₃ : ∀ e → (e ∉ E₂) → (e ∈ E₃) → (rhs₀ e) ⊨ (rhs₁₂₃ e)
     rhs₀⊨rhs₁₂₃ e e∉E₂ e∈E₃ = ⊨-trans (τ₁-resp-⊆ (RW↓₀⊆↓RW₁₂₃ e)) (τ₁-resp-⊨ (⊨-trans (pre₂₃⊨rhs₂₃ e e∉E₂ e∈E₃) (τ₂-resp-⊆ (RW↓₂₃⊆↓RW₁₂₃ e (E₃⊆E₂₃ e e∈E₃)))))
     
     rhs₀⊨rhs₁₂∨rhs₁₂₃ : ∀ e → (e ∈ E₂) → (e ∈ E₃) → (rhs₀ e) ⊨ ((rhs₁₂ e) ∨ (rhs₁₂₃ e))
     rhs₀⊨rhs₁₂∨rhs₁₂₃ e e∈E₂ e∈E₃ = ⊨-trans (τ₁-resp-⊨ (pre₂₃⊨lhs₂₃∨rhs₂₃ e e∈E₂ e∈E₃)) (⊨-trans τ₁-resp-∨ (⊨-resp-∨ (τ₁-resp-∩⊆ (RW↓₀∩E₁⊆↓RW₁₂ e (E₂⊆E₁₂ e e∈E₂))) (⊨-trans (τ₁-resp-⊆ (RW↓₀⊆↓RW₁₂₃ e)) (τ₁-resp-⊨ (τ₂-resp-⊆ (RW↓₂₃⊆↓RW₁₂₃ e (E₃⊆E₂₃ e e∈E₃)))))))

     pre₀⊨lhs₁₂₃ : ∀ e → (e ∈ E₁₂) → (e ∉ E₃) → (pre₀(e) ⊨ lhs₁₂₃(e))
     pre₀⊨lhs₁₂₃ e _ e∉E₃ with dec-E₁₂(e)
     pre₀⊨lhs₁₂₃ e _ e∉E₃ | yes (left e∈E₁ e∉E₂) = pre₀⊨lhs₀ e e∈E₁ (λ e∈E₂₃ → neither e∉E₂ e∉E₃ (E₂₃⊆E₂∪E₃ e e∈E₂₃))
     pre₀⊨lhs₁₂₃ e _ e∉E₃ | yes (right e∉E₁ e∈E₂) = ⊨-trans (pre₀⊨rhs₀ e e∉E₁ (E₂⊆E₂₃ e e∈E₂)) (rhs₀⊨rhs₁₂ e e∈E₂ e∉E₃)
     pre₀⊨lhs₁₂₃ e _ e∉E₃ | yes (both e∈E₁ e∈E₂) = ⊨-trans (pre₀⊨lhs₀∨rhs₀ e e∈E₁ (E₂⊆E₂₃ e e∈E₂)) (⊨-resp-∨ ⊨-refl (rhs₀⊨rhs₁₂ e e∈E₂ e∉E₃))
     pre₀⊨lhs₁₂₃ e e∈E₁₂ e∉E₃ | no e∉E₁₂ = CONTRADICTION (e∉E₁₂ e∈E₁₂)
     
     pre₀⊨rhs₁₂₃ : ∀ e → (e ∉ E₁₂) → (e ∈ E₃) → (pre₀(e) ⊨ rhs₁₂₃(e))
     pre₀⊨rhs₁₂₃ e e∉E₁₂ e∈E₃ = ⊨-trans (pre₀⊨rhs₀ e (λ e∈E₁ → e∉E₁₂ (E₁⊆E₁₂ e e∈E₁)) (E₃⊆E₂₃ e e∈E₃)) (rhs₀⊨rhs₁₂₃ e (λ e∈E₂ → e∉E₁₂ (E₂⊆E₁₂ e e∈E₂)) e∈E₃)
     
     pre₀⊨lhs₁₂₃∨rhs₁₂₃ : ∀ e → (e ∈ E₁₂) → (e ∈ E₃) → (pre₀(e) ⊨ (lhs₁₂₃(e) ∨ rhs₁₂₃(e)))
     pre₀⊨lhs₁₂₃∨rhs₁₂₃ e _ e∈E₃ with dec-E₁₂(e)
     pre₀⊨lhs₁₂₃∨rhs₁₂₃ e _ e∈E₃ | yes (left  e∈E₁ e∉E₂) = ⊨-trans (pre₀⊨lhs₀∨rhs₀ e e∈E₁ (E₃⊆E₂₃ e e∈E₃)) (⊨-resp-∨ ⊨-refl (rhs₀⊨rhs₁₂₃ e e∉E₂ e∈E₃))
     pre₀⊨lhs₁₂₃∨rhs₁₂₃ e _ e∈E₃ | yes (right e∉E₁ e∈E₂) = ⊨-trans (pre₀⊨rhs₀ e e∉E₁ (E₃⊆E₂₃ e e∈E₃)) (rhs₀⊨rhs₁₂∨rhs₁₂₃ e e∈E₂ e∈E₃)
     pre₀⊨lhs₁₂₃∨rhs₁₂₃ e _ e∈E₃ | yes (both e∈E₁ e∈E₂) = ⊨-trans (pre₀⊨lhs₀∨rhs₀ e e∈E₁ (E₃⊆E₂₃ e e∈E₃)) (⊨-trans (⊨-resp-∨ ⊨-refl (rhs₀⊨rhs₁₂∨rhs₁₂₃ e e∈E₂ e∈E₃)) ⊨-assocl-∨)
     pre₀⊨lhs₁₂₃∨rhs₁₂₃ e e∈E₁₂ e∈E₃ | no e∉E₁₂ = CONTRADICTION (e∉E₁₂ e∈E₁₂)
     
     pre₀⊨pre₁₂₃ : ∀ e → (e ∈ E₁₂₃) → (pre₀(e) ⊨ pre₁₂₃(e))
     pre₀⊨pre₁₂₃ e _ with dec-E₁₂₃(e)
     pre₀⊨pre₁₂₃ e _ | yes (left e∈E₁₂ e∉E₃) = pre₀⊨lhs₁₂₃ e e∈E₁₂ e∉E₃
     pre₀⊨pre₁₂₃ e _ | yes (right e∉E₁₂ e∈E₃) = pre₀⊨rhs₁₂₃ e e∉E₁₂ e∈E₃
     pre₀⊨pre₁₂₃ e _ | yes (both e∈E₁₂ e∈E₃) = pre₀⊨lhs₁₂₃∨rhs₁₂₃ e e∈E₁₂ e∈E₃
     pre₀⊨pre₁₂₃ e e∈E₁₂₃ | no e∉E₁₂₃ = CONTRADICTION (e∉E₁₂₃ e∈E₁₂₃)
     
     P₁₂₃≲P₀ : P₁₂₃ ≲ P₀
     P₁₂₃≲P₀ = record
                 { E′⊆E = E₀⊆E₁₂₃
                 ; E⊆E′ = E₁₂₃⊆E₀
                 ; act=act′ = λ e e∈E₁₂₃ → refl
                 ; pre′⊨pre = pre₀⊨pre₁₂₃
                 ; ≤⊆≤′ = λ d e d≤₀e → d≤₀e
                 ; τ′⊨τ = λ C ϕ → ⊨-trans (τ₀ϕ⊨τ₁τ₂₃ϕ C ϕ) (τ₁-resp-⊨ (τ₂₃ϕ⊨τ₂τ₃ϕ C ϕ))
                 }

     P₀∈⟦⟨C₁∙C₂⟩∙C₃⟧ : P₀ ∈ ⟦ (C₁ ∙ C₂) ∙ C₃ ⟧
     P₀∈⟦⟨C₁∙C₂⟩∙C₃⟧ = sem-resp-≲ P₁₂₃≲P₀ P₁₂₃∈⟦⟨C₁∙C₂⟩∙C₃⟧
     
  ⟦⟨C₁∙C₂⟩∙C₃⟧⊆⟦C₁∙⟨C₂∙C₃⟩⟧ = {!!}

  -- QED
