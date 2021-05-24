open import prelude
open import data-model using (MemoryModel)
import command
import pomset
import seqcomp
import semantics

module examples (Event : Set) (MM : MemoryModel(Event)) where

  open MemoryModel MM
  open command(Event)(MM)
  open pomset(Event)(DM)
  open seqcomp(Event)(DM)
  open semantics(Event)(MM)

  -- The canonical pomset in ⟦ skip ⟧
  
  skipP : (Event → Action) → PomsetWithPredicateTransformers
  skipP ℓ = record
            { E = ∅
            ; PO = ≡PO
            ; κ = λ e → ff
            ; ℓ = ℓ
            ; τ = λ C ϕ → ϕ
            ; ✓ = tt
            ; rf = ∅
            ; τ-resp-∩⊆ = λ C∩E⊆D → ⊨-refl
            ; τ-resp-⊨ = λ ϕ⊨ψ → ϕ⊨ψ
            ; τ-resp-∨ = ⊨-refl
            ; τ-refl-∧ = ⊨-refl
            ; τ-resp-ff = ⊨-refl
            ; ✓⊨τtt = ⊨-refl
            ; rf-match = λ ()
            }

  skipP∈⟦skip⟧ : ∀ ℓ → skipP ℓ ∈ ⟦ skip ⟧
  skipP∈⟦skip⟧ ℓ = record
                  { E₀⊆∅ = λ e ()
                  ; τ₀ϕ⊨ϕ = λ C ϕ → ⊨-refl }
  
  -- The canonical way to build a pomset in ⟦ C₁ ∙ C₂ ⟧ from pomsets in ⟦ C₁ ⟧ and ⟦ C₂ ⟧

  compP : PomsetWithPredicateTransformers → PomsetWithPredicateTransformers → PomsetWithPredicateTransformers → PomsetWithPredicateTransformers
  compP P₀ P₁ P₂ = P₁₂ where

     open PomsetWithPredicateTransformers P₀ using () renaming (ℓ to ℓ₁₂ ; rf to rf₁₂ ; rf-match to rf₁₂-match ; PO to PO₁₂ ; _≤_ to _≤₁₂_ ; ≤-refl to ≤₁₂-refl ; ≤-trans to ≤₁₂-trans ; ≤-asym to ≤₁₂-asym)
     open PomsetWithPredicateTransformers P₁ using () renaming (E to E₁ ; dec-E to dec-E₁ ; ℓ to ℓ₁ ; κ to κ₁ ; τ to τ₁ ; ✓ to ✓₁ ; rf to rf₁ ; τ-resp-⊆ to τ₁-resp-⊆ ; τ-resp-∩⊆ to τ₁-resp-∩⊆ ; τ-resp-⊨ to τ₁-resp-⊨ ; τ-resp-∨ to τ₁-resp-∨ ; τ-refl-∨ to τ₁-refl-∨n ; τ-resp-ff to τ₁-resp-ff; τ-refl-∧ to τ₁-refl-∧ ; rf-match to rf₁-match)
     open PomsetWithPredicateTransformers P₂ using () renaming (E to E₂ ; dec-E to dec-E₂ ; ℓ to ℓ₂ ; κ to κ₂ ; τ to τ₂ ; ✓ to ✓₂ ; rf to rf₂ ; τ-resp-⊆ to τ₂-resp-⊆ ; τ-resp-∩⊆ to τ₂-resp-∩⊆ ; τ-resp-⊨ to τ₂-resp-⊨ ; τ-resp-∨ to τ₂-resp-∨ ; τ-refl-∨ to τ₂-refl-∨ ; τ-resp-ff to τ₂-resp-ff ; τ-refl-∧ to τ₂-refl-∧ ; ✓⊨τtt to ✓₂⊨τ₂tt ; rf-match to rf₂-match)

     E₁₂ = E₁ ∪ E₂
     dec-E₁₂ = λ e → EXCLUDED_MIDDLE(e ∈ E₁₂)
     ↓₁₂ = λ e → E₁₂ ∩ (λ d → (d ≤₁₂ e))
     lhs₁₂ = κ₁
     rhs₁₂ = λ e → τ₁(↓₁₂(e))(κ₂(e))

     κ₁₂ : Event → Formula
     κ₁₂ e with dec-E₁₂(e)
     κ₁₂ e | yes (left _ _)  = lhs₁₂(e)
     κ₁₂ e | yes (right _ _) = rhs₁₂(e)
     κ₁₂ e | yes (both _ _)  = lhs₁₂(e) ∨ rhs₁₂(e)
     κ₁₂ e | no _ = ff

     P₁₂ : PomsetWithPredicateTransformers
     P₁₂ = record
             { E = E₁₂
             ; PO = PO₁₂
             ; κ = κ₁₂
             ; ℓ = ℓ₁₂
             ; τ = λ C ϕ → τ₁(C)(τ₂(C)(ϕ))
             ; ✓ = ✓₁ ∧ τ₁(E₁)(✓₂)
             ; rf = rf₁₂
             ; τ-resp-∩⊆ = λ C∩E⊆D → ⊨-trans (τ₁-resp-∩⊆ (⊆-trans (⊆-resp-∩ ⊆-refl ⊆-left-∪) C∩E⊆D)) (τ₁-resp-⊨ (τ₂-resp-∩⊆ (⊆-trans (⊆-resp-∩ ⊆-refl ⊆-right-∪) C∩E⊆D)))
             ; τ-resp-⊨ = λ ϕ⊨ψ → τ₁-resp-⊨ (τ₂-resp-⊨ ϕ⊨ψ)
             ; τ-resp-∨ = ⊨-trans (τ₁-resp-⊨ τ₂-resp-∨) τ₁-resp-∨
             ; τ-resp-ff = ⊨-trans (τ₁-resp-⊨ τ₂-resp-ff) τ₁-resp-ff
             ; τ-refl-∧ = ⊨-trans τ₁-refl-∧ (τ₁-resp-⊨ τ₂-refl-∧)
             ; ✓⊨τtt = ⊨-trans ⊨-right-∧ (⊨-trans (τ₁-resp-⊆ ⊆-left-∪) (τ₁-resp-⊨ (⊨-trans ✓₂⊨τ₂tt (τ₂-resp-⊆ ⊆-right-∪))))
             ; rf-match = rf₁₂-match
             }

  record Compatible (P₀ P₁ P₂ : PomsetWithPredicateTransformers) : Set₁ where
  
     open PomsetWithPredicateTransformers P₀ using () renaming (ℓ to ℓ₀ ; _≤_ to _≤₀_ ; ≤-refl to ≤₀-refl ; ≤-trans to ≤₀-trans ; ≤-asym to ≤₀-asym)
     open PomsetWithPredicateTransformers P₁ using () renaming (E to E₁ ; ℓ to ℓ₁ ; _≤_ to _≤₁_)
     open PomsetWithPredicateTransformers P₂ using () renaming (E to E₂ ; ℓ to ℓ₂ ; _≤_ to _≤₂_)

     field ℓ₀=ℓ₁ : ∀ e → (e ∈ E₁) → (ℓ₀(e) ≡ ℓ₁(e))
     field ℓ₀=ℓ₂ : ∀ e → (e ∈ E₂) → (ℓ₀(e) ≡ ℓ₂(e))
     field ≤₁⊆≤₀ : ∀ d e → (d ≤₁ e) → (d ≤₀ e)
     field ≤₂⊆≤₀ : ∀ d e → (d ≤₂ e) → (d ≤₀ e)
            
  compP∈⟦C₁∙C₂⟧ : ∀ C₁ C₂ P₀ P₁ P₂ →
      (P₁ ∈ ⟦ C₁ ⟧) → (P₂ ∈ ⟦ C₂ ⟧) →
      (Compatible P₀ P₁ P₂) →
      (compP P₀ P₁ P₂ ∈ ⟦ C₁ ∙ C₂ ⟧)
  compP∈⟦C₁∙C₂⟧ C₁ C₂ P₀ P₁ P₂ P₁∈⟦C₁⟧ P₂∈⟦C₂⟧ P₀∈CompatP₁P₂ = P₁₂∈⟦C₁∙C₂⟧ where

     open Compatible P₀∈CompatP₁P₂
     
     P₁₂ = compP P₀ P₁ P₂

     open PomsetWithPredicateTransformers P₁₂ using () renaming (dec-E to dec-E₁₂ ; κ to κ₁₂ ; ↓ to ↓₁₂)
     open PomsetWithPredicateTransformers P₁ using () renaming (E to E₁ ; dec-E to dec-E₁ ; ℓ to ℓ₁ ; κ to κ₁ ; τ to τ₁ ; τ-resp-⊆ to τ₁-resp-⊆ ; τ-resp-⊨ to τ₁-resp-⊨)
     open PomsetWithPredicateTransformers P₂ using () renaming (E to E₂ ; dec-E to dec-E₂ ; ℓ to ℓ₂ ; κ to κ₂ ; τ to τ₂ ; τ-resp-⊆ to τ₂-resp-⊆ ; τ-resp-⊨ to τ₂-resp-⊨)

     lhs₁₂ = κ₁
     rhs₁₂ = λ e → τ₁(↓₁₂(e))(κ₂(e))
     
     κ₁₂⊨lhs₁₂ : ∀ e → (e ∈ E₁) → (e ∉ E₂) → (κ₁₂(e) ⊨ lhs₁₂(e))
     κ₁₂⊨lhs₁₂ e e∈E₁ e∉E₂ with dec-E₁₂(e)
     κ₁₂⊨lhs₁₂ e e∈E₁ e∉E₂ | yes (left _ _) = ⊨-refl
     κ₁₂⊨lhs₁₂ e e∈E₁ e∉E₂ | yes (right _ e∈E₂) = CONTRADICTION (e∉E₂ e∈E₂)
     κ₁₂⊨lhs₁₂ e e∈E₁ e∉E₂ | yes (both _ e∈E₂) = CONTRADICTION (e∉E₂ e∈E₂)
     κ₁₂⊨lhs₁₂ e e∈E₁ e∉E₂ | no e∉E₁₂ = CONTRADICTION (e∉E₁₂ (left e∈E₁ e∉E₂))

     κ₁₂⊨rhs₁₂ : ∀ e → (e ∉ E₁) → (e ∈ E₂) → (κ₁₂(e) ⊨ rhs₁₂(e))
     κ₁₂⊨rhs₁₂ e e∉E₁ e∈E₂ with dec-E₁₂(e)
     κ₁₂⊨rhs₁₂ e e∉E₁ e∈E₂ | yes (left e∈E₁ _) = CONTRADICTION (e∉E₁ e∈E₁)
     κ₁₂⊨rhs₁₂ e e∉E₁ e∈E₂ | yes (right _ _) = ⊨-refl
     κ₁₂⊨rhs₁₂ e e∉E₁ e∈E₂ | yes (both e∈E₁ _) = CONTRADICTION (e∉E₁ e∈E₁)
     κ₁₂⊨rhs₁₂ e e∉E₁ e∈E₂ | no e∉E₁₂ = CONTRADICTION (e∉E₁₂ (right e∉E₁ e∈E₂))
     
     κ₁₂⊨lhs₁₂∨rhs₁₂ : ∀ e → (e ∈ E₁) → (e ∈ E₂) → (κ₁₂(e) ⊨ (lhs₁₂(e) ∨ rhs₁₂(e)))
     κ₁₂⊨lhs₁₂∨rhs₁₂ e e∈E₁ e∈E₂ with dec-E₁₂(e)
     κ₁₂⊨lhs₁₂∨rhs₁₂ e e∈E₁ e∈E₂ | yes (left _ e∉E₂) = CONTRADICTION (e∉E₂ e∈E₂)
     κ₁₂⊨lhs₁₂∨rhs₁₂ e e∈E₁ e∈E₂ | yes (right e∉E₁ _) = CONTRADICTION (e∉E₁ e∈E₁)
     κ₁₂⊨lhs₁₂∨rhs₁₂ e e∈E₁ e∈E₂ | yes (both _ _) = ⊨-refl
     κ₁₂⊨lhs₁₂∨rhs₁₂ e e∈E₁ e∈E₂ | no e∉E₁₂ = CONTRADICTION (e∉E₁₂ (both e∈E₁ e∈E₂))
     
     P₁₂∈⟦C₁∙C₂⟧ : P₁₂ ∈ ⟦ C₁ ∙ C₂ ⟧
     P₁₂∈⟦C₁∙C₂⟧ = record
                     { P₁ = P₁
                     ; P₂ = P₂
                     ; P₁∈𝒫₁ = P₁∈⟦C₁⟧
                     ; P₂∈𝒫₂ = P₂∈⟦C₂⟧
                     ; E₀⊆E₁∪E₂ = ⊆-refl
                     ; E₁⊆E₀ = ⊆-left-∪
                     ; E₂⊆E₀ = ⊆-right-∪
                     ; ≤₁⊆≤₀ = ≤₁⊆≤₀
                     ; ≤₂⊆≤₀ = ≤₂⊆≤₀
                     ; κ₀⊨lhs₀ = κ₁₂⊨lhs₁₂
                     ; κ₀⊨rhs₀ = κ₁₂⊨rhs₁₂
                     ; κ₀⊨lhs₀∨rhs₀ = κ₁₂⊨lhs₁₂∨rhs₁₂
                     ; ℓ₀=ℓ₁ = ℓ₀=ℓ₁
                     ; ℓ₀=ℓ₂ = ℓ₀=ℓ₂
                     ; τ₀ϕ⊨τ₁τ₂ϕ = λ C ϕ → ⊨-refl
                     ; ✓₀⊨✓₁ = ⊨-left-∧
                     ; ✓₀⊨τ₁✓₂ = ⊨-right-∧
                     }

  record compLemmas (C₁ C₂ : Command) (P₀ P₁ P₂ : PomsetWithPredicateTransformers) : Set₁ where

     field P₁∈⟦C₁⟧ : (P₁ ∈ ⟦ C₁ ⟧)
     field P₂∈⟦C₂⟧ : (P₂ ∈ ⟦ C₂ ⟧)
     field PO₀∈CompP₁P₂ : (Compatible P₀ P₁ P₂)
 
     open Compatible PO₀∈CompP₁P₂
     
     P₁₂ = compP P₀ P₁ P₂
     
     open PomsetWithPredicateTransformers P₁₂ using () renaming (dec-E to dec-E₁₂ ; κ to κ₁₂)
     open PomsetWithPredicateTransformers P₁ using () renaming (E to E₁)
     open PomsetWithPredicateTransformers P₂ using () renaming (E to E₂)

     P₁₂∈⟦C₁∙C₂⟧ : P₁₂ ∈ ⟦ C₁ ∙ C₂ ⟧
     P₁₂∈⟦C₁∙C₂⟧ = compP∈⟦C₁∙C₂⟧ C₁ C₂ P₀ P₁ P₂ P₁∈⟦C₁⟧ P₂∈⟦C₂⟧ PO₀∈CompP₁P₂

     open _●_ P₁₂∈⟦C₁∙C₂⟧ using () renaming (lhs₀ to lhs₁₂ ; rhs₀ to rhs₁₂)
     
     lhs₁₂⊨κ₁₂ : ∀ e → (e ∈ E₁) → (e ∉ E₂) → (lhs₁₂(e) ⊨ κ₁₂(e))
     lhs₁₂⊨κ₁₂ e e∈E₁ e∉E₂ with dec-E₁₂(e)
     lhs₁₂⊨κ₁₂ e e∈E₁ e∉E₂ | yes (left _ _) = ⊨-refl
     lhs₁₂⊨κ₁₂ e e∈E₁ e∉E₂ | yes (right _ e∈E₂) = CONTRADICTION (e∉E₂ e∈E₂)
     lhs₁₂⊨κ₁₂ e e∈E₁ e∉E₂ | yes (both _ e∈E₂) = CONTRADICTION (e∉E₂ e∈E₂)
     lhs₁₂⊨κ₁₂ e e∈E₁ e∉E₂ | no e∉E₁₂ = CONTRADICTION (e∉E₁₂ (left e∈E₁ e∉E₂))

     rhs₁₂⊨κ₁₂ : ∀ e → (e ∉ E₁) → (e ∈ E₂) → (rhs₁₂(e) ⊨ κ₁₂(e))
     rhs₁₂⊨κ₁₂ e e∉E₁ e∈E₂ with dec-E₁₂(e)
     rhs₁₂⊨κ₁₂ e e∉E₁ e∈E₂ | yes (left e∈E₁ _) = CONTRADICTION (e∉E₁ e∈E₁)
     rhs₁₂⊨κ₁₂ e e∉E₁ e∈E₂ | yes (right _ _) = ⊨-refl
     rhs₁₂⊨κ₁₂ e e∉E₁ e∈E₂ | yes (both e∈E₁ _) = CONTRADICTION (e∉E₁ e∈E₁)
     rhs₁₂⊨κ₁₂ e e∉E₁ e∈E₂ | no e∉E₁₂ = CONTRADICTION (e∉E₁₂ (right e∉E₁ e∈E₂))

     lhs₁₂∨rhs₁₂⊨κ₁₂ : ∀ e → (e ∈ E₁) → (e ∈ E₂) → ((lhs₁₂(e) ∨ rhs₁₂(e)) ⊨ κ₁₂(e))
     lhs₁₂∨rhs₁₂⊨κ₁₂ e e∈E₁ e∈E₂ with dec-E₁₂(e)
     lhs₁₂∨rhs₁₂⊨κ₁₂ e e∈E₁ e∈E₂ | yes (left _ e∉E₂) = CONTRADICTION (e∉E₂ e∈E₂)
     lhs₁₂∨rhs₁₂⊨κ₁₂ e e∈E₁ e∈E₂ | yes (right e∉E₁ _) = CONTRADICTION (e∉E₁ e∈E₁)
     lhs₁₂∨rhs₁₂⊨κ₁₂ e e∈E₁ e∈E₂ | yes (both _ _) = ⊨-refl
     lhs₁₂∨rhs₁₂⊨κ₁₂ e e∈E₁ e∈E₂ | no e∉E₁₂ = CONTRADICTION (e∉E₁₂ (both e∈E₁ e∈E₂))
