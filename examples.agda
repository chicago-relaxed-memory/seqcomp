open import prelude
open import data-model using ( DataModel )
import command
import pomset
import semantics

module examples (DM : DataModel) (Event : Set) where

  open DataModel DM
  open command(DM)
  open pomset(DM)(Event)
  open semantics(DM)(Event)

  -- The canonical pomset in ⟦ skip ⟧
  
  skipP : (Event → Action) → Pomset
  skipP act = record
            { E = ∅
            ; _≤_ = λ d e → (d ≡ e)
            ; ℓ = λ e → (ff , act(e))
            ; τ = λ C ϕ → ϕ
            ; ✓ = tt
            ; ≤-refl = refl
            ; ≤-trans = ≡-trans
            ; ≤-asym = λ d=e e=d → e=d
            ; τ-resp-∩⊆ = λ C∩E⊆D → ⊨-refl
            ; τ-resp-⊨ = λ ϕ⊨ψ → ϕ⊨ψ
            ; τ-resp-∨ = ⊨-refl
            ; τ-refl-∨ = ⊨-refl
            ; τ-refl-∧ = ⊨-refl
            ; ✓⊨τtt = ⊨-refl
            }

  skipP∈⟦skip⟧ : ∀ act → skipP act ∈ ⟦ skip ⟧
  skipP∈⟦skip⟧ act = record
                  { E₀⊆∅ = λ e ()
                  ; τ₀ϕ⊨ϕ = λ C ϕ → ⊨-refl }
  
  -- The caconical way to build a pomset in ⟦ C₁ ∙ C₂ ⟧ from pomsets in ⟦ C₁ ⟧ and ⟦ C₂ ⟧

  compP : (Event → Action) → PartialOrder → Pomset → Pomset → Pomset
  compP act₀ PO₀ P₁ P₂ = P₀ where

     open PartialOrder PO₀ using () renaming (_≤_ to _≤₀_ ; ≤-refl to ≤₀-refl ; ≤-trans to ≤₀-trans ; ≤-asym to ≤₀-asym)
     open Pomset P₁ using () renaming (E to E₁ ; dec-E to dec-E₁ ; ℓ to ℓ₁ ; act to act₁ ; pre to pre₁ ; τ to τ₁ ; τ-resp-⊆ to τ₁-resp-⊆ ; τ-resp-∩⊆ to τ₁-resp-∩⊆ ; τ-resp-⊨ to τ₁-resp-⊨ ; τ-resp-∨ to τ₁-resp-∨ ; τ-refl-∨ to τ₁-refl-∨ ; τ-refl-∧ to τ₁-refl-∧ ; ✓ to ✓₁)
     open Pomset P₂ using () renaming (E to E₂ ; dec-E to dec-E₂ ; ℓ to ℓ₂ ; act to act₂ ; pre to pre₂ ; τ to τ₂ ; τ-resp-⊆ to τ₂-resp-⊆ ; τ-resp-∩⊆ to τ₂-resp-∩⊆ ; τ-resp-⊨ to τ₂-resp-⊨ ; τ-resp-∨ to τ₂-resp-∨ ; τ-refl-∨ to τ₂-refl-∨ ; τ-refl-∧ to τ₂-refl-∧ ; ✓ to ✓₂ ; ✓⊨τtt to ✓₂⊨τ₂tt)

     E₀ = E₁ ∪ E₂
     dec-E₀ = λ e → EXCLUDED_MIDDLE(e ∈ E₀)
     RE₀ = E₀ ∩ (act₀ ⁻¹[ Reads ])
     WE₀ = E₀ ∩ (act₀ ⁻¹[ Writes ])
     ↓RW₀ = λ e → E₀ ∩ (λ d → (d ∈ RE₀) → (e ∈ WE₀) → (d ≤₀ e))
     lhs₀ = pre₁
     rhs₀ = λ e → τ₁(↓RW₀(e))(pre₂(e))

     pre₀ : Event → Formula
     pre₀ e with dec-E₀(e)
     pre₀ e | yes (left _ _)  = lhs₀(e)
     pre₀ e | yes (right _ _) = rhs₀(e)
     pre₀ e | yes (both _ _)  = lhs₀(e) ∨ rhs₀(e)
     pre₀ e | no _ = ff

     P₀ : Pomset
     P₀ = record
             { E = E₀
             ; _≤_ = _≤₀_
             ; ℓ = λ e → (pre₀ e , act₀ e)
             ; τ = λ C ϕ → τ₁(C)(τ₂(C)(ϕ))
             ; ≤-refl = ≤₀-refl
             ; ≤-trans = ≤₀-trans
             ; ≤-asym = ≤₀-asym
             ; τ-resp-∩⊆ = λ C∩E⊆D → ⊨-trans (τ₁-resp-∩⊆ (⊆-trans (⊆-resp-∩ ⊆-refl ⊆-left-∪) C∩E⊆D)) (τ₁-resp-⊨ (τ₂-resp-∩⊆ (⊆-trans (⊆-resp-∩ ⊆-refl ⊆-right-∪) C∩E⊆D)))
             ; τ-resp-⊨ = λ ϕ⊨ψ → τ₁-resp-⊨ (τ₂-resp-⊨ ϕ⊨ψ)
             ; τ-resp-∨ = ⊨-trans (τ₁-resp-⊨ τ₂-resp-∨) τ₁-resp-∨
             ; τ-refl-∨ = ⊨-trans τ₁-refl-∨ (τ₁-resp-⊨ τ₂-refl-∨)
             ; ✓ = ✓₁ ∧ τ₁(E₁)(✓₂)
             ; τ-refl-∧ = ⊨-trans τ₁-refl-∧ (τ₁-resp-⊨ τ₂-refl-∧)
             ; ✓⊨τtt = ⊨-trans ⊨-right-∧ (⊨-trans (τ₁-resp-⊆ ⊆-left-∪) (τ₁-resp-⊨ (⊨-trans ✓₂⊨τ₂tt (τ₂-resp-⊆ ⊆-right-∪))))
             }

  record Compatible (act₀ : Event → Action) (PO₀ : PartialOrder) (P₁ P₂ : Pomset) : Set₁ where
  
     open PartialOrder PO₀ using () renaming (_≤_ to _≤₀_ ; ≤-refl to ≤₀-refl ; ≤-trans to ≤₀-trans ; ≤-asym to ≤₀-asym)
     open Pomset P₁ using () renaming (E to E₁ ; act to act₁ ; _≤_ to _≤₁_)
     open Pomset P₂ using () renaming (E to E₂ ; act to act₂ ; _≤_ to _≤₂_)

     field act₀=act₁ : ∀ e → (e ∈ E₁) → (act₀(e) ≡ act₁(e))
     field act₀=act₂ : ∀ e → (e ∈ E₂) → (act₀(e) ≡ act₂(e))
     field ≤₁⊆≤₀ : ∀ d e → (d ≤₁ e) → (d ≤₀ e)
     field ≤₂⊆≤₀ : ∀ d e → (d ≤₂ e) → (d ≤₀ e)
     field coherence :  ∀ d e → (d ∈ E₁) → (e ∈ E₂) → (Conflicts (act₁(d)) (act₂(e))) → (d ≤₀ e)
            
  compP∈⟦C₁∙C₂⟧ : ∀ C₁ C₂ act₀ PO₀ P₁ P₂ →
      (P₁ ∈ ⟦ C₁ ⟧) → (P₂ ∈ ⟦ C₂ ⟧) →
      (Compatible act₀ PO₀ P₁ P₂) →
      (compP act₀ PO₀ P₁ P₂ ∈ ⟦ C₁ ∙ C₂ ⟧)
  compP∈⟦C₁∙C₂⟧ C₁ C₂ act₀ PO₀ P₁ P₂ P₁∈⟦C₁⟧ P₂∈⟦C₂⟧ PO₀∈CompatP₁P₂ = P₀∈⟦C₁∙C₂⟧ where

     open Compatible PO₀∈CompatP₁P₂
     
     P₀ = compP act₀ PO₀ P₁ P₂

     open Pomset P₀ using () renaming (dec-E to dec-E₀ ; pre to pre₀ ; ↓RW to ↓RW₀)
     open Pomset P₁ using () renaming (E to E₁ ; dec-E to dec-E₁ ; ℓ to ℓ₁ ; act to act₁ ; pre to pre₁ ; τ to τ₁ ; τ-resp-⊆ to τ₁-resp-⊆ ; τ-resp-⊨ to τ₁-resp-⊨)
     open Pomset P₂ using () renaming (E to E₂ ; dec-E to dec-E₂ ; ℓ to ℓ₂ ; act to act₂ ; pre to pre₂ ; τ to τ₂ ; τ-resp-⊆ to τ₂-resp-⊆ ; τ-resp-⊨ to τ₂-resp-⊨)

     lhs₀ = pre₁
     rhs₀ = λ e → τ₁(↓RW₀(e))(pre₂(e))
     
     pre₀⊨lhs₀ : ∀ e → (e ∈ E₁) → (e ∉ E₂) → (pre₀(e) ⊨ lhs₀(e))
     pre₀⊨lhs₀ e e∈E₁ e∉E₂ with dec-E₀(e)
     pre₀⊨lhs₀ e e∈E₁ e∉E₂ | yes (left _ _) = ⊨-refl
     pre₀⊨lhs₀ e e∈E₁ e∉E₂ | yes (right _ e∈E₂) = CONTRADICTION (e∉E₂ e∈E₂)
     pre₀⊨lhs₀ e e∈E₁ e∉E₂ | yes (both _ e∈E₂) = CONTRADICTION (e∉E₂ e∈E₂)
     pre₀⊨lhs₀ e e∈E₁ e∉E₂ | no e∉E₀ = CONTRADICTION (e∉E₀ (left e∈E₁ e∉E₂))

     pre₀⊨rhs₀ : ∀ e → (e ∉ E₁) → (e ∈ E₂) → (pre₀(e) ⊨ rhs₀(e))
     pre₀⊨rhs₀ e e∉E₁ e∈E₂ with dec-E₀(e)
     pre₀⊨rhs₀ e e∉E₁ e∈E₂ | yes (left e∈E₁ _) = CONTRADICTION (e∉E₁ e∈E₁)
     pre₀⊨rhs₀ e e∉E₁ e∈E₂ | yes (right _ _) = ⊨-refl
     pre₀⊨rhs₀ e e∉E₁ e∈E₂ | yes (both e∈E₁ _) = CONTRADICTION (e∉E₁ e∈E₁)
     pre₀⊨rhs₀ e e∉E₁ e∈E₂ | no e∉E₀ = CONTRADICTION (e∉E₀ (right e∉E₁ e∈E₂))
     
     pre₀⊨lhs₀∨rhs₀ : ∀ e → (e ∈ E₁) → (e ∈ E₂) → (pre₀(e) ⊨ (lhs₀(e) ∨ rhs₀(e)))
     pre₀⊨lhs₀∨rhs₀ e e∈E₁ e∈E₂ with dec-E₀(e)
     pre₀⊨lhs₀∨rhs₀ e e∈E₁ e∈E₂ | yes (left _ e∉E₂) = CONTRADICTION (e∉E₂ e∈E₂)
     pre₀⊨lhs₀∨rhs₀ e e∈E₁ e∈E₂ | yes (right e∉E₁ _) = CONTRADICTION (e∉E₁ e∈E₁)
     pre₀⊨lhs₀∨rhs₀ e e∈E₁ e∈E₂ | yes (both _ _) = ⊨-refl
     pre₀⊨lhs₀∨rhs₀ e e∈E₁ e∈E₂ | no e∉E₀ = CONTRADICTION (e∉E₀ (both e∈E₁ e∈E₂))
     
     P₀∈⟦C₁∙C₂⟧ : P₀ ∈ ⟦ C₁ ∙ C₂ ⟧
     P₀∈⟦C₁∙C₂⟧ = record
                     { P₁ = P₁
                     ; P₂ = P₂
                     ; P₁∈𝒫₁ = P₁∈⟦C₁⟧
                     ; P₂∈𝒫₂ = P₂∈⟦C₂⟧
                     ; E₀⊆E₁∪E₂ = ⊆-refl
                     ; E₁⊆E₀ = ⊆-left-∪
                     ; E₂⊆E₀ = ⊆-right-∪
                     ; ≤₁⊆≤₀ = ≤₁⊆≤₀
                     ; ≤₂⊆≤₀ = ≤₂⊆≤₀
                     ; coherence = coherence
                     ; pre₀⊨lhs₀ = pre₀⊨lhs₀
                     ; pre₀⊨rhs₀ = pre₀⊨rhs₀
                     ; pre₀⊨lhs₀∨rhs₀ = pre₀⊨lhs₀∨rhs₀
                     ; act₀=act₁ = act₀=act₁
                     ; act₀=act₂ = act₀=act₂
                     ; τ₀ϕ⊨τ₁τ₂ϕ = λ C ϕ → ⊨-refl
                     ; ✓₀⊨✓₁ = ⊨-left-∧
                     ; ✓₀⊨τ₁✓₂ = ⊨-right-∧
                     }

  record compLemmas (C₁ C₂ : Command) (act₀ : Event → Action) (PO₀ : PartialOrder) (P₁ P₂ : Pomset) : Set₁ where

     field P₁∈⟦C₁⟧ : (P₁ ∈ ⟦ C₁ ⟧)
     field P₂∈⟦C₂⟧ : (P₂ ∈ ⟦ C₂ ⟧)
     field PO₀∈CompP₁P₂ : (Compatible act₀ PO₀ P₁ P₂)
 
     open Compatible PO₀∈CompP₁P₂
     
     P₀ = compP act₀ PO₀ P₁ P₂
     
     open Pomset P₀ using () renaming (dec-E to dec-E₀ ; pre to pre₀)
     open Pomset P₁ using () renaming (E to E₁)
     open Pomset P₂ using () renaming (E to E₂)

     P₀∈⟦C₁∙C₂⟧ : P₀ ∈ ⟦ C₁ ∙ C₂ ⟧
     P₀∈⟦C₁∙C₂⟧ = compP∈⟦C₁∙C₂⟧ C₁ C₂ act₀ PO₀ P₁ P₂ P₁∈⟦C₁⟧ P₂∈⟦C₂⟧ PO₀∈CompP₁P₂

     open _●_ P₀∈⟦C₁∙C₂⟧ using (lhs₀ ; rhs₀)
     
     lhs₀⊨pre₀ : ∀ e → (e ∈ E₁) → (e ∉ E₂) → (lhs₀(e) ⊨ pre₀(e))
     lhs₀⊨pre₀ e e∈E₁ e∉E₂ with dec-E₀(e)
     lhs₀⊨pre₀ e e∈E₁ e∉E₂ | yes (left _ _) = ⊨-refl
     lhs₀⊨pre₀ e e∈E₁ e∉E₂ | yes (right _ e∈E₂) = CONTRADICTION (e∉E₂ e∈E₂)
     lhs₀⊨pre₀ e e∈E₁ e∉E₂ | yes (both _ e∈E₂) = CONTRADICTION (e∉E₂ e∈E₂)
     lhs₀⊨pre₀ e e∈E₁ e∉E₂ | no e∉E₀ = CONTRADICTION (e∉E₀ (left e∈E₁ e∉E₂))

     rhs₀⊨pre₀ : ∀ e → (e ∉ E₁) → (e ∈ E₂) → (rhs₀(e) ⊨ pre₀(e))
     rhs₀⊨pre₀ e e∉E₁ e∈E₂ with dec-E₀(e)
     rhs₀⊨pre₀ e e∉E₁ e∈E₂ | yes (left e∈E₁ _) = CONTRADICTION (e∉E₁ e∈E₁)
     rhs₀⊨pre₀ e e∉E₁ e∈E₂ | yes (right _ _) = ⊨-refl
     rhs₀⊨pre₀ e e∉E₁ e∈E₂ | yes (both e∈E₁ _) = CONTRADICTION (e∉E₁ e∈E₁)
     rhs₀⊨pre₀ e e∉E₁ e∈E₂ | no e∉E₀ = CONTRADICTION (e∉E₀ (right e∉E₁ e∈E₂))

     lhs₀∨rhs₀⊨pre₀ : ∀ e → (e ∈ E₁) → (e ∈ E₂) → ((lhs₀(e) ∨ rhs₀(e)) ⊨ pre₀(e))
     lhs₀∨rhs₀⊨pre₀ e e∈E₁ e∈E₂ with dec-E₀(e)
     lhs₀∨rhs₀⊨pre₀ e e∈E₁ e∈E₂ | yes (left _ e∉E₂) = CONTRADICTION (e∉E₂ e∈E₂)
     lhs₀∨rhs₀⊨pre₀ e e∈E₁ e∈E₂ | yes (right e∉E₁ _) = CONTRADICTION (e∉E₁ e∈E₁)
     lhs₀∨rhs₀⊨pre₀ e e∈E₁ e∈E₂ | yes (both _ _) = ⊨-refl
     lhs₀∨rhs₀⊨pre₀ e e∈E₁ e∈E₂ | no e∉E₀ = CONTRADICTION (e∉E₀ (both e∈E₁ e∈E₂))
