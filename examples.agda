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
            ; τ-resp-∩⊆ = λ C∩E⊆D → ⊨-refl
            ; τ-resp-⊨ = λ ϕ⊨ψ → ϕ⊨ψ
            ; τ-resp-∨ = ⊨-refl
            ; τ-refl-∧ = ⊨-refl
            ; τ-resp-ff = ⊨-refl
            ; ✓⊨τtt = ⊨-refl
            }

  skipP∈⟦skip⟧ : ∀ ℓ → skipP ℓ ∈ ⟦ skip ⟧
  skipP∈⟦skip⟧ ℓ = record
                  { E₀⊆∅ = λ e ()
                  ; τ₀ϕ⊨ϕ = λ C ϕ → ⊨-refl }
  
  -- The canonical way to build a pomset in ⟦ C₁ ∙ C₂ ⟧ from pomsets in ⟦ C₁ ⟧ and ⟦ C₂ ⟧

  compP : (Event → Action) → PartialOrder → PomsetWithPredicateTransformers → PomsetWithPredicateTransformers → PomsetWithPredicateTransformers
  compP ℓ₀ PO₀ P₁ P₂ = P₀ where

     open PartialOrder PO₀ using () renaming (_≤_ to _≤₀_ ; ≤-refl to ≤₀-refl ; ≤-trans to ≤₀-trans ; ≤-asym to ≤₀-asym)
     open PomsetWithPredicateTransformers P₁ using () renaming (E to E₁ ; dec-E to dec-E₁ ; ℓ to ℓ₁ ; κ to κ₁ ; τ to τ₁ ; ✓ to ✓₁ ; τ-resp-⊆ to τ₁-resp-⊆ ; τ-resp-∩⊆ to τ₁-resp-∩⊆ ; τ-resp-⊨ to τ₁-resp-⊨ ; τ-resp-∨ to τ₁-resp-∨ ; τ-refl-∨ to τ₁-refl-∨n ; τ-resp-ff to τ₁-resp-ff; τ-refl-∧ to τ₁-refl-∧)
     open PomsetWithPredicateTransformers P₂ using () renaming (E to E₂ ; dec-E to dec-E₂ ; ℓ to ℓ₂ ; κ to κ₂ ; τ to τ₂ ; ✓ to ✓₂ ; τ-resp-⊆ to τ₂-resp-⊆ ; τ-resp-∩⊆ to τ₂-resp-∩⊆ ; τ-resp-⊨ to τ₂-resp-⊨ ; τ-resp-∨ to τ₂-resp-∨ ; τ-refl-∨ to τ₂-refl-∨ ; τ-resp-ff to τ₂-resp-ff ; τ-refl-∧ to τ₂-refl-∧ ; ✓⊨τtt to ✓₂⊨τ₂tt)

     E₀ = E₁ ∪ E₂
     dec-E₀ = λ e → EXCLUDED_MIDDLE(e ∈ E₀)
     ↓₀ = λ e → E₀ ∩ (λ d → (d ≤₀ e))
     lhs₀ = κ₁
     rhs₀ = λ e → τ₁(↓₀(e))(κ₂(e))

     κ₀ : Event → Formula
     κ₀ e with dec-E₀(e)
     κ₀ e | yes (left _ _)  = lhs₀(e)
     κ₀ e | yes (right _ _) = rhs₀(e)
     κ₀ e | yes (both _ _)  = lhs₀(e) ∨ rhs₀(e)
     κ₀ e | no _ = ff

     P₀ : PomsetWithPredicateTransformers
     P₀ = record
             { E = E₀
             ; PO = PO₀
             ; κ = κ₀
             ; ℓ = ℓ₀
             ; τ = λ C ϕ → τ₁(C)(τ₂(C)(ϕ))
             ; ✓ = ✓₁ ∧ τ₁(E₁)(✓₂)
             ; τ-resp-∩⊆ = λ C∩E⊆D → ⊨-trans (τ₁-resp-∩⊆ (⊆-trans (⊆-resp-∩ ⊆-refl ⊆-left-∪) C∩E⊆D)) (τ₁-resp-⊨ (τ₂-resp-∩⊆ (⊆-trans (⊆-resp-∩ ⊆-refl ⊆-right-∪) C∩E⊆D)))
             ; τ-resp-⊨ = λ ϕ⊨ψ → τ₁-resp-⊨ (τ₂-resp-⊨ ϕ⊨ψ)
             ; τ-resp-∨ = ⊨-trans (τ₁-resp-⊨ τ₂-resp-∨) τ₁-resp-∨
             ; τ-resp-ff = ⊨-trans (τ₁-resp-⊨ τ₂-resp-ff) τ₁-resp-ff
             ; τ-refl-∧ = ⊨-trans τ₁-refl-∧ (τ₁-resp-⊨ τ₂-refl-∧)
             ; ✓⊨τtt = ⊨-trans ⊨-right-∧ (⊨-trans (τ₁-resp-⊆ ⊆-left-∪) (τ₁-resp-⊨ (⊨-trans ✓₂⊨τ₂tt (τ₂-resp-⊆ ⊆-right-∪))))
             }

  record Compatible (ℓ₀ : Event → Action) (PO₀ : PartialOrder) (P₁ P₂ : PomsetWithPredicateTransformers) : Set₁ where
  
     open PartialOrder PO₀ using () renaming (_≤_ to _≤₀_ ; ≤-refl to ≤₀-refl ; ≤-trans to ≤₀-trans ; ≤-asym to ≤₀-asym)
     open PomsetWithPredicateTransformers P₁ using () renaming (E to E₁ ; ℓ to ℓ₁ ; _≤_ to _≤₁_)
     open PomsetWithPredicateTransformers P₂ using () renaming (E to E₂ ; ℓ to ℓ₂ ; _≤_ to _≤₂_)

     field ℓ₀=ℓ₁ : ∀ e → (e ∈ E₁) → (ℓ₀(e) ≡ ℓ₁(e))
     field ℓ₀=ℓ₂ : ∀ e → (e ∈ E₂) → (ℓ₀(e) ≡ ℓ₂(e))
     field ≤₁⊆≤₀ : ∀ d e → (d ≤₁ e) → (d ≤₀ e)
     field ≤₂⊆≤₀ : ∀ d e → (d ≤₂ e) → (d ≤₀ e)
            
  compP∈⟦C₁∙C₂⟧ : ∀ C₁ C₂ ℓ₀ PO₀ P₁ P₂ →
      (P₁ ∈ ⟦ C₁ ⟧) → (P₂ ∈ ⟦ C₂ ⟧) →
      (Compatible ℓ₀ PO₀ P₁ P₂) →
      (compP ℓ₀ PO₀ P₁ P₂ ∈ ⟦ C₁ ∙ C₂ ⟧)
  compP∈⟦C₁∙C₂⟧ C₁ C₂ ℓ₀ PO₀ P₁ P₂ P₁∈⟦C₁⟧ P₂∈⟦C₂⟧ PO₀∈CompatP₁P₂ = P₀∈⟦C₁∙C₂⟧ where

     open Compatible PO₀∈CompatP₁P₂
     
     P₀ = compP ℓ₀ PO₀ P₁ P₂

     open PomsetWithPredicateTransformers P₀ using () renaming (dec-E to dec-E₀ ; κ to κ₀ ; ↓ to ↓₀)
     open PomsetWithPredicateTransformers P₁ using () renaming (E to E₁ ; dec-E to dec-E₁ ; ℓ to ℓ₁ ; κ to κ₁ ; τ to τ₁ ; τ-resp-⊆ to τ₁-resp-⊆ ; τ-resp-⊨ to τ₁-resp-⊨)
     open PomsetWithPredicateTransformers P₂ using () renaming (E to E₂ ; dec-E to dec-E₂ ; ℓ to ℓ₂ ; κ to κ₂ ; τ to τ₂ ; τ-resp-⊆ to τ₂-resp-⊆ ; τ-resp-⊨ to τ₂-resp-⊨)

     lhs₀ = κ₁
     rhs₀ = λ e → τ₁(↓₀(e))(κ₂(e))
     
     κ₀⊨lhs₀ : ∀ e → (e ∈ E₁) → (e ∉ E₂) → (κ₀(e) ⊨ lhs₀(e))
     κ₀⊨lhs₀ e e∈E₁ e∉E₂ with dec-E₀(e)
     κ₀⊨lhs₀ e e∈E₁ e∉E₂ | yes (left _ _) = ⊨-refl
     κ₀⊨lhs₀ e e∈E₁ e∉E₂ | yes (right _ e∈E₂) = CONTRADICTION (e∉E₂ e∈E₂)
     κ₀⊨lhs₀ e e∈E₁ e∉E₂ | yes (both _ e∈E₂) = CONTRADICTION (e∉E₂ e∈E₂)
     κ₀⊨lhs₀ e e∈E₁ e∉E₂ | no e∉E₀ = CONTRADICTION (e∉E₀ (left e∈E₁ e∉E₂))

     κ₀⊨rhs₀ : ∀ e → (e ∉ E₁) → (e ∈ E₂) → (κ₀(e) ⊨ rhs₀(e))
     κ₀⊨rhs₀ e e∉E₁ e∈E₂ with dec-E₀(e)
     κ₀⊨rhs₀ e e∉E₁ e∈E₂ | yes (left e∈E₁ _) = CONTRADICTION (e∉E₁ e∈E₁)
     κ₀⊨rhs₀ e e∉E₁ e∈E₂ | yes (right _ _) = ⊨-refl
     κ₀⊨rhs₀ e e∉E₁ e∈E₂ | yes (both e∈E₁ _) = CONTRADICTION (e∉E₁ e∈E₁)
     κ₀⊨rhs₀ e e∉E₁ e∈E₂ | no e∉E₀ = CONTRADICTION (e∉E₀ (right e∉E₁ e∈E₂))
     
     κ₀⊨lhs₀∨rhs₀ : ∀ e → (e ∈ E₁) → (e ∈ E₂) → (κ₀(e) ⊨ (lhs₀(e) ∨ rhs₀(e)))
     κ₀⊨lhs₀∨rhs₀ e e∈E₁ e∈E₂ with dec-E₀(e)
     κ₀⊨lhs₀∨rhs₀ e e∈E₁ e∈E₂ | yes (left _ e∉E₂) = CONTRADICTION (e∉E₂ e∈E₂)
     κ₀⊨lhs₀∨rhs₀ e e∈E₁ e∈E₂ | yes (right e∉E₁ _) = CONTRADICTION (e∉E₁ e∈E₁)
     κ₀⊨lhs₀∨rhs₀ e e∈E₁ e∈E₂ | yes (both _ _) = ⊨-refl
     κ₀⊨lhs₀∨rhs₀ e e∈E₁ e∈E₂ | no e∉E₀ = CONTRADICTION (e∉E₀ (both e∈E₁ e∈E₂))
     
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
                     ; κ₀⊨lhs₀ = κ₀⊨lhs₀
                     ; κ₀⊨rhs₀ = κ₀⊨rhs₀
                     ; κ₀⊨lhs₀∨rhs₀ = κ₀⊨lhs₀∨rhs₀
                     ; ℓ₀=ℓ₁ = ℓ₀=ℓ₁
                     ; ℓ₀=ℓ₂ = ℓ₀=ℓ₂
                     ; τ₀ϕ⊨τ₁τ₂ϕ = λ C ϕ → ⊨-refl
                     ; ✓₀⊨✓₁ = ⊨-left-∧
                     ; ✓₀⊨τ₁✓₂ = ⊨-right-∧
                     }

  record compLemmas (C₁ C₂ : Command) (ℓ₀ : Event → Action) (PO₀ : PartialOrder) (P₁ P₂ : PomsetWithPredicateTransformers) : Set₁ where

     field P₁∈⟦C₁⟧ : (P₁ ∈ ⟦ C₁ ⟧)
     field P₂∈⟦C₂⟧ : (P₂ ∈ ⟦ C₂ ⟧)
     field PO₀∈CompP₁P₂ : (Compatible ℓ₀ PO₀ P₁ P₂)
 
     open Compatible PO₀∈CompP₁P₂
     
     P₀ = compP ℓ₀ PO₀ P₁ P₂
     
     open PomsetWithPredicateTransformers P₀ using () renaming (dec-E to dec-E₀ ; κ to κ₀)
     open PomsetWithPredicateTransformers P₁ using () renaming (E to E₁)
     open PomsetWithPredicateTransformers P₂ using () renaming (E to E₂)

     P₀∈⟦C₁∙C₂⟧ : P₀ ∈ ⟦ C₁ ∙ C₂ ⟧
     P₀∈⟦C₁∙C₂⟧ = compP∈⟦C₁∙C₂⟧ C₁ C₂ ℓ₀ PO₀ P₁ P₂ P₁∈⟦C₁⟧ P₂∈⟦C₂⟧ PO₀∈CompP₁P₂

     open _●_ P₀∈⟦C₁∙C₂⟧ using (lhs₀ ; rhs₀)
     
     lhs₀⊨κ₀ : ∀ e → (e ∈ E₁) → (e ∉ E₂) → (lhs₀(e) ⊨ κ₀(e))
     lhs₀⊨κ₀ e e∈E₁ e∉E₂ with dec-E₀(e)
     lhs₀⊨κ₀ e e∈E₁ e∉E₂ | yes (left _ _) = ⊨-refl
     lhs₀⊨κ₀ e e∈E₁ e∉E₂ | yes (right _ e∈E₂) = CONTRADICTION (e∉E₂ e∈E₂)
     lhs₀⊨κ₀ e e∈E₁ e∉E₂ | yes (both _ e∈E₂) = CONTRADICTION (e∉E₂ e∈E₂)
     lhs₀⊨κ₀ e e∈E₁ e∉E₂ | no e∉E₀ = CONTRADICTION (e∉E₀ (left e∈E₁ e∉E₂))

     rhs₀⊨κ₀ : ∀ e → (e ∉ E₁) → (e ∈ E₂) → (rhs₀(e) ⊨ κ₀(e))
     rhs₀⊨κ₀ e e∉E₁ e∈E₂ with dec-E₀(e)
     rhs₀⊨κ₀ e e∉E₁ e∈E₂ | yes (left e∈E₁ _) = CONTRADICTION (e∉E₁ e∈E₁)
     rhs₀⊨κ₀ e e∉E₁ e∈E₂ | yes (right _ _) = ⊨-refl
     rhs₀⊨κ₀ e e∉E₁ e∈E₂ | yes (both e∈E₁ _) = CONTRADICTION (e∉E₁ e∈E₁)
     rhs₀⊨κ₀ e e∉E₁ e∈E₂ | no e∉E₀ = CONTRADICTION (e∉E₀ (right e∉E₁ e∈E₂))

     lhs₀∨rhs₀⊨κ₀ : ∀ e → (e ∈ E₁) → (e ∈ E₂) → ((lhs₀(e) ∨ rhs₀(e)) ⊨ κ₀(e))
     lhs₀∨rhs₀⊨κ₀ e e∈E₁ e∈E₂ with dec-E₀(e)
     lhs₀∨rhs₀⊨κ₀ e e∈E₁ e∈E₂ | yes (left _ e∉E₂) = CONTRADICTION (e∉E₂ e∈E₂)
     lhs₀∨rhs₀⊨κ₀ e e∈E₁ e∈E₂ | yes (right e∉E₁ _) = CONTRADICTION (e∉E₁ e∈E₁)
     lhs₀∨rhs₀⊨κ₀ e e∈E₁ e∈E₂ | yes (both _ _) = ⊨-refl
     lhs₀∨rhs₀⊨κ₀ e e∈E₁ e∈E₂ | no e∉E₀ = CONTRADICTION (e∉E₀ (both e∈E₁ e∈E₂))
