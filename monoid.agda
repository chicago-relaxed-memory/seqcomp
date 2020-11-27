open import prelude
open import data-model
import command
import pomset
import seqcomp
import semantics
import augmentation
import examples

module monoid (MM : MemoryModel) (Event : Set) where

  open MemoryModel MM
  open command(MM)
  open pomset(DM)(Event)
  open seqcomp(DM)(Event)
  open semantics(MM)(Event)
  open augmentation(MM)(Event)
  open examples(MM)(Event)

  -- PROPOSITION: sequential composition forms a monoid
  
  ⟦C⟧⊆⟦C∙skip⟧ : ∀ C → ⟦ C ⟧ ⊆ ⟦ C ∙ skip ⟧
  ⟦C∙skip⟧⊆⟦C⟧ : ∀ C → ⟦ C ∙ skip ⟧ ⊆ ⟦ C ⟧

  ⟦C⟧⊆⟦skip∙C⟧ : ∀ C → ⟦ C ⟧ ⊆ ⟦ skip ∙ C ⟧
  ⟦skip∙C⟧⊆⟦C⟧ : ∀ C → ⟦ skip ∙ C ⟧ ⊆ ⟦ C ⟧

  ⟦C₁∙⟨C₂∙C₃⟩⟧⊆⟦⟨C₁∙C₂⟩∙C₃⟧ : ∀ C₁ C₂ C₃ → ⟦ C₁ ∙ (C₂ ∙ C₃) ⟧ ⊆ ⟦ (C₁ ∙ C₂) ∙ C₃ ⟧
  ⟦⟨C₁∙C₂⟩∙C₃⟧⊆⟦C₁∙⟨C₂∙C₃⟩⟧ : ∀ C₁ C₂ C₃ → ⟦ (C₁ ∙ C₂) ∙ C₃ ⟧ ⊆ ⟦ C₁ ∙ (C₂ ∙ C₃) ⟧

  -- PROOF that skip is a right unit
  
  ⟦C⟧⊆⟦C∙skip⟧ C P₀ P₀∈⟦C⟧ = P₀∈⟦C∙skip⟧ where

    open PomsetWithPredicateTransformers P₀ using () renaming (act to act₀ ; ≤-refl to ≤₀-refl)

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
                    ; causal = λ d e d∈E₀ ()
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

    open PomsetWithPredicateTransformers P₀ using () renaming (PwP to PwP₀ ; E to E₀)
    open PomsetWithPredicateTransformers P₁ using () renaming (PwP to PwP₁ ; E to E₁ ; τ-resp-⊨ to τ₁-resp-⊨)
    open PomsetWithPredicateTransformers P₂ using () renaming (E to E₂)

    PwP₁≲PwP₀ : PwP₁ ≲p PwP₀
    PwP₁≲PwP₀ = record
              { E′⊆E = ⊆-trans E₀⊆E₁∪E₂ (⊆-elim-∪ ⊆-refl (⊆-trans E₂⊆∅ ⊆-elim-∅))
              ; E⊆E′ = E₁⊆E₀
              ; act=act′ = λ e e∈E₁ → ≡-symm (act₀=act₁ e e∈E₁)
              ; pre′⊨pre = λ e e∈E₁ → pre₀⊨lhs₀ e e∈E₁ (E₂⊆∅ e)
              ; ≤⊆≤′ = ≤₁⊆≤₀
              }
    
    P₁≲P₀ : P₁ ≲τ P₀
    P₁≲P₀ = record
              { PwP≲PwP′ = PwP₁≲PwP₀
              ; τ′⊨τ = λ C ϕ → ⊨-trans (τ₀ϕ⊨τ₁τ₂ϕ C ϕ) (τ₁-resp-⊨ (τ₂ϕ⊨ϕ C ϕ))
              }
    
    P₀∈⟦C⟧ = sem-resp-≲τ C P₁≲P₀ P₁∈⟦C⟧

  -- PROOF that skip is a left unit

  ⟦C⟧⊆⟦skip∙C⟧ C P₀ P₀∈⟦C⟧ = P₀∈⟦skip∙C⟧ where

    open PomsetWithPredicateTransformers P₀ using () renaming (act to act₀ ; ≤-refl to ≤₀-refl)

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
                    ; causal = λ d e ()
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

    open PomsetWithPredicateTransformers P₀ using () renaming (PwP to PwP₀ ; E to E₀ ; ↓ to ↓₀)
    open PomsetWithPredicateTransformers P₁ using () renaming (E to E₁)
    open PomsetWithPredicateTransformers P₂ using () renaming (PwP to PwP₂ ; E to E₂ ; pre to pre₂ ; τ to τ₂ ; τ-resp-⊨ to τ₂-resp-⊨)

    PwP₂≲PwP₀ : PwP₂ ≲p PwP₀
    PwP₂≲PwP₀ = record
              { E′⊆E = ⊆-trans E₀⊆E₁∪E₂ (⊆-elim-∪ (⊆-trans E₁⊆∅ ⊆-elim-∅) ⊆-refl)
              ; E⊆E′ = E₂⊆E₀
              ; act=act′ = λ e e∈E₀ → ≡-symm (act₀=act₂ e e∈E₀)
              ; pre′⊨pre = λ e e∈E₂ → ⊨-trans (pre₀⊨rhs₀ e (E₁⊆∅ e) e∈E₂) (τ₁ϕ⊨ϕ (↓₀(e)) (pre₂(e)))
              ; ≤⊆≤′ =  ≤₂⊆≤₀
              }
    
    P₂≲P₀ : P₂ ≲τ P₀
    P₂≲P₀ = record
              { PwP≲PwP′ = PwP₂≲PwP₀
              ; τ′⊨τ = λ C ϕ → ⊨-trans (τ₀ϕ⊨τ₁τ₂ϕ C ϕ) (τ₁ϕ⊨ϕ C (τ₂ C ϕ))
              }
    
    P₀∈⟦C⟧ = sem-resp-≲τ C P₂≲P₀ P₂∈⟦C⟧
  
  -- PROOF of associativity

  ⟦C₁∙⟨C₂∙C₃⟩⟧⊆⟦⟨C₁∙C₂⟩∙C₃⟧ C₁ C₂ C₃ P₀ P₀∈⟦C₁∙⟨C₂∙C₃⟩⟧ =  P₀∈⟦⟨C₁∙C₂⟩∙C₃⟧ where

     open _●_ P₀∈⟦C₁∙⟨C₂∙C₃⟩⟧ using (P₁ ; E₁⊆E₀ ; ≤₁⊆≤₀ ; act₀=act₁ ; rhs₀ ; pre₀⊨lhs₀ ; pre₀⊨rhs₀ ; pre₀⊨lhs₀∨rhs₀) renaming (P₂ to P₂₃ ; P₁∈𝒫₁ to P₁∈⟦C₁⟧ ; P₂∈𝒫₂ to P₂₃∈⟦C₂∙C₃⟧ ; E₂⊆E₀ to E₂₃⊆E₀ ; E₀⊆E₁∪E₂ to E₀⊆E₁∪E₂₃ ; act₀=act₂ to act₀=act₂₃ ; ≤₂⊆≤₀ to ≤₂₃⊆≤₀ ; causal to causal₀ ; τ₀ϕ⊨τ₁τ₂ϕ to τ₀ϕ⊨τ₁τ₂₃ϕ)
     open _●_ P₂₃∈⟦C₂∙C₃⟧ using () renaming (P₁ to P₂ ; P₂ to P₃ ; P₁∈𝒫₁ to P₂∈⟦C₂⟧ ; P₂∈𝒫₂ to P₃∈⟦C₃⟧ ; rhs₀ to rhs₂₃ ; E₁⊆E₀ to E₂⊆E₂₃ ; E₂⊆E₀ to E₃⊆E₂₃ ; E₀⊆E₁∪E₂ to E₂₃⊆E₂∪E₃ ; ≤₁⊆≤₀ to ≤₂⊆≤₂₃ ; ≤₂⊆≤₀ to ≤₃⊆≤₂₃ ; act₀=act₁ to act₂₃=act₂ ; act₀=act₂ to act₂₃=act₃ ; pre₀⊨lhs₀ to pre₂₃⊨lhs₂₃ ; pre₀⊨rhs₀ to pre₂₃⊨rhs₂₃ ; pre₀⊨lhs₀∨rhs₀ to pre₂₃⊨lhs₂₃∨rhs₂₃ ; causal to causal₂₃; τ₀ϕ⊨τ₁τ₂ϕ to τ₂₃ϕ⊨τ₂τ₃ϕ)
     
     open PomsetWithPredicateTransformers P₀ using () renaming (PwP to PwP₀ ; E to E₀ ; act to act₀ ; pre to pre₀ ; _≤_ to _≤₀_ ; ≤-refl to ≤₀-refl ; ≤-trans to ≤₀-trans ; ≤-asym to ≤₀-asym ; ↓ to ↓₀ ; PO to PO₀)
     open PomsetWithPredicateTransformers P₁ using () renaming (E to E₁ ; dec-E to dec-E₁ ; ℓ to ℓ₁ ; act to act₁ ; pre to pre₁ ; τ to τ₁ ; τ-resp-⊆ to τ₁-resp-⊆ ; τ-resp-∩⊆ to τ₁-resp-∩⊆ ; τ-resp-⊨ to τ₁-resp-⊨ ; τ-resp-∨ to τ₁-resp-∨)
     open PomsetWithPredicateTransformers P₂ using () renaming (E to E₂ ; dec-E to dec-E₂ ; ℓ to ℓ₂ ; act to act₂ ; pre to pre₂ ; τ to τ₂ ; τ-resp-⊆ to τ₂-resp-⊆ ; τ-resp-∩⊆ to τ₂-resp-∩⊆ ; τ-resp-⊨ to τ₂-resp-⊨)
     open PomsetWithPredicateTransformers P₃ using () renaming (E to E₃ ; act to act₃ ; pre to pre₃ ; τ to τ₃)
     open PomsetWithPredicateTransformers P₂₃ using () renaming (E to E₂₃ ; τ to τ₂₃ ; pre to pre₂₃; ↓ to ↓₂₃)

     P₁₂ : PomsetWithPredicateTransformers
     P₁₂ = compP act₀ PO₀ P₁ P₂

     P₁₂₃ : PomsetWithPredicateTransformers
     P₁₂₃ = compP act₀ PO₀ P₁₂ P₃

     open PomsetWithPredicateTransformers P₁₂ using () renaming (E to E₁₂ ; pre to pre₁₂ ; dec-E to dec-E₁₂ ; ↓ to ↓₁₂)
     open PomsetWithPredicateTransformers P₁₂₃ using () renaming (PwP to PwP₁₂₃ ; E to E₁₂₃ ; pre to pre₁₂₃ ; dec-E to dec-E₁₂₃ ; ↓ to ↓₁₂₃)
     
     act₀=act₂ : ∀ e → (e ∈ E₂) → (act₀(e) ≡ act₂(e))
     act₀=act₂ e e∈E₂ = ≡-trans (act₀=act₂₃ e (E₂⊆E₂₃ e e∈E₂)) (act₂₃=act₂ e e∈E₂)
     
     act₀=act₃ : ∀ e → (e ∈ E₃) → (act₀(e) ≡ act₃(e))
     act₀=act₃ e e∈E₃ = ≡-trans (act₀=act₂₃ e (E₃⊆E₂₃ e e∈E₃)) (act₂₃=act₃ e e∈E₃)

     causal₁₂ : ∀ d e → (d ∈ E₁) → (e ∈ E₂) → Causal (act₁ d) (act₂ e) → (d ≤₀ e)
     causal₁₂ d e d∈E₁ e∈E₂ a₁#a₂ = causal₀ d e d∈E₁ (E₂⊆E₂₃ e e∈E₂) (≡-subst₂ Causal refl (≡-symm (act₂₃=act₂ e e∈E₂)) a₁#a₂)
     
     causal₁₂₃ : ∀ d e → (d ∈ E₁₂) → (e ∈ E₃) → Causal (act₀ d) (act₃ e) → (d ≤₀ e)
     causal₁₂₃ d e (left d∈E₁ _) e∈E₃ a₁₂#a₃ = causal₀ d e d∈E₁ (E₃⊆E₂₃ e e∈E₃) (≡-subst₂ Causal (act₀=act₁ d d∈E₁) (≡-symm (act₂₃=act₃ e e∈E₃)) a₁₂#a₃)
     causal₁₂₃ d e (right _ d∈E₂) e∈E₃ a₁₂#a₃ = ≤₂₃⊆≤₀ d e (causal₂₃ d e d∈E₂ e∈E₃ (≡-subst₂ Causal (act₀=act₂ d d∈E₂) refl a₁₂#a₃))
     causal₁₂₃ d e (both d∈E₁ _) e∈E₃ a₁₂#a₃ = causal₀ d e d∈E₁ (E₃⊆E₂₃ e e∈E₃) (≡-subst₂ Causal (act₀=act₁ d d∈E₁) (≡-symm (act₂₃=act₃ e e∈E₃)) a₁₂#a₃)
     
     PO₀∈CompP₁P₂ : Compatible act₀ PO₀ P₁ P₂
     PO₀∈CompP₁P₂ = record
                      { act₀=act₁ = act₀=act₁
                      ; act₀=act₂ = act₀=act₂
                      ; ≤₁⊆≤₀ = ≤₁⊆≤₀
                      ; ≤₂⊆≤₀ = λ d e d≤₂e → ≤₂₃⊆≤₀ d e (≤₂⊆≤₂₃ d e d≤₂e)
                      ; causal = causal₁₂ }
     
     PO₀∈CompP₁₂P₃ : Compatible act₀ PO₀ P₁₂ P₃
     PO₀∈CompP₁₂P₃ = record
                       { act₀=act₁ = λ e e∈E₁₂ → refl
                       ; act₀=act₂ = act₀=act₃
                       ; ≤₁⊆≤₀ = λ d e d≤₀e → d≤₀e
                       ; ≤₂⊆≤₀ = λ d e d≤₃e → ≤₂₃⊆≤₀ d e (≤₃⊆≤₂₃ d e d≤₃e)
                       ; causal = causal₁₂₃ }
     
     P₁₂∈⟦C₁∙C₂⟧ : P₁₂ ∈ ⟦ C₁ ∙ C₂ ⟧
     P₁₂∈⟦C₁∙C₂⟧ = compP∈⟦C₁∙C₂⟧ C₁ C₂ act₀ PO₀ P₁ P₂ P₁∈⟦C₁⟧ P₂∈⟦C₂⟧ PO₀∈CompP₁P₂
     
     P₁₂₃∈⟦⟨C₁∙C₂⟩∙C₃⟧ : P₁₂₃ ∈ ⟦ (C₁ ∙ C₂) ∙ C₃ ⟧
     P₁₂₃∈⟦⟨C₁∙C₂⟩∙C₃⟧ = compP∈⟦C₁∙C₂⟧ (C₁ ∙ C₂) C₃ act₀ PO₀ P₁₂ P₃ P₁₂∈⟦C₁∙C₂⟧ P₃∈⟦C₃⟧ PO₀∈CompP₁₂P₃

     open _●_ P₁₂∈⟦C₁∙C₂⟧ using () renaming (E₁⊆E₀ to E₁⊆E₁₂ ; E₂⊆E₀ to E₂⊆E₁₂ ; rhs₀ to rhs₁₂ ; pre₀⊨rhs₀ to pre₁₂⊨rhs₁₂)
     open _●_ P₁₂₃∈⟦⟨C₁∙C₂⟩∙C₃⟧ using () renaming (lhs₀ to lhs₁₂₃ ; rhs₀ to rhs₁₂₃ ; pre₀⊨rhs₀ to pre₁₂₃⊨rhs₁₂₃)

     lemmas₁₂ : compLemmas C₁ C₂ act₀ PO₀ P₁ P₂
     lemmas₁₂ = record { P₁∈⟦C₁⟧ = P₁∈⟦C₁⟧ ; P₂∈⟦C₂⟧ = P₂∈⟦C₂⟧ ; PO₀∈CompP₁P₂ = PO₀∈CompP₁P₂ }
     
     lemmas₁₂₃ : compLemmas (C₁ ∙ C₂) C₃ act₀ PO₀ P₁₂ P₃
     lemmas₁₂₃ = record { P₁∈⟦C₁⟧ = P₁₂∈⟦C₁∙C₂⟧ ; P₂∈⟦C₂⟧ = P₃∈⟦C₃⟧ ; PO₀∈CompP₁P₂ = PO₀∈CompP₁₂P₃ }

     open compLemmas lemmas₁₂ using () renaming (lhs₀⊨pre₀ to lhs₁₂⊨pre₁₂; rhs₀⊨pre₀ to rhs₁₂⊨pre₁₂ ; lhs₀∨rhs₀⊨pre₀ to lhs₁₂∨rhs₁₂⊨pre₁₂)
     open compLemmas lemmas₁₂₃ using () renaming (lhs₀⊨pre₀ to lhs₁₂₃⊨pre₁₂₃; rhs₀⊨pre₀ to rhs₁₂₃⊨pre₁₂₃ ; lhs₀∨rhs₀⊨pre₀ to lhs₁₂₃∨rhs₁₂₃⊨pre₁₂₃)

     E₁₂⊆E₀ : E₁₂ ⊆ E₀
     E₁₂⊆E₀ = ⊆-elim-∪ E₁⊆E₀ (⊆-trans E₂⊆E₂₃ E₂₃⊆E₀)
     
     E₁₂₃⊆E₀ : E₁₂₃ ⊆ E₀
     E₁₂₃⊆E₀ = ⊆-elim-∪ E₁₂⊆E₀ (⊆-trans E₃⊆E₂₃ E₂₃⊆E₀) 
     
     E₀⊆E₁₂₃ : E₀ ⊆ E₁₂₃
     E₀⊆E₁₂₃ = ⊆-trans E₀⊆E₁∪E₂₃ (⊆-trans (⊆-resp-∪ ⊆-refl E₂₃⊆E₂∪E₃) ⊆-assocl-∪)

     E₂₃⊆E₁₂₃ : E₂₃ ⊆ E₁₂₃
     E₂₃⊆E₁₂₃ = ⊆-trans E₂₃⊆E₀ E₀⊆E₁₂₃
     
     ↓₀⊆↓₁₂₃ : ∀ e → (↓₀(e) ⊆ ↓₁₂₃(e))
     ↓₀⊆↓₁₂₃ e = ⊆-resp-∩ E₀⊆E₁₂₃ ⊆-refl
     
     ↓₀∩E₁₂⊆↓₁₂ : ∀ e → (e ∈ E₁₂) → ((↓₀(e) ∩ E₁₂) ⊆ ↓₁₂(e))
     ↓₀∩E₁₂⊆↓₁₂ e e∈E₁₂  d ((d∈E₀ , d≤e) , d∈E₁₂) = (d∈E₁₂ , d≤e)
     
     ↓₀∩E₁⊆↓₁₂ : ∀ e → (e ∈ E₁₂) → ((↓₀(e) ∩ E₁) ⊆ ↓₁₂(e))
     ↓₀∩E₁⊆↓₁₂ e e∈E₁₂ d (d∈↓₀e , d∈E₁) = ↓₀∩E₁₂⊆↓₁₂ e e∈E₁₂ d (d∈↓₀e , (E₁⊆E₁₂ d d∈E₁))
     
     ↓₂₃⊆↓₁₂₃ : ∀ e → (e ∈ E₂₃) → (↓₂₃(e) ⊆ ↓₁₂₃(e))
     ↓₂₃⊆↓₁₂₃ e e∈E₂₃ d (d∈E₂₃ , d≤₂₃e) = (E₂₃⊆E₁₂₃ d d∈E₂₃ , ≤₂₃⊆≤₀ d e d≤₂₃e)
          
     rhs₀⊨rhs₁₂ : ∀ e → (e ∈ E₂) → (e ∉ E₃) → (rhs₀ e) ⊨ (rhs₁₂ e)
     rhs₀⊨rhs₁₂ e e∈E₂ e∉E₂ = ⊨-trans (τ₁-resp-∩⊆ (↓₀∩E₁⊆↓₁₂ e (E₂⊆E₁₂ e e∈E₂))) (τ₁-resp-⊨ (pre₂₃⊨lhs₂₃ e e∈E₂ e∉E₂))
     
     rhs₀⊨rhs₁₂₃ : ∀ e → (e ∉ E₂) → (e ∈ E₃) → (rhs₀ e) ⊨ (rhs₁₂₃ e)
     rhs₀⊨rhs₁₂₃ e e∉E₂ e∈E₃ = ⊨-trans (τ₁-resp-⊆ (↓₀⊆↓₁₂₃ e)) (τ₁-resp-⊨ (⊨-trans (pre₂₃⊨rhs₂₃ e e∉E₂ e∈E₃) (τ₂-resp-⊆ (↓₂₃⊆↓₁₂₃ e (E₃⊆E₂₃ e e∈E₃)))))
     
     rhs₀⊨rhs₁₂∨rhs₁₂₃ : ∀ e → (e ∈ E₂) → (e ∈ E₃) → (rhs₀ e) ⊨ ((rhs₁₂ e) ∨ (rhs₁₂₃ e))
     rhs₀⊨rhs₁₂∨rhs₁₂₃ e e∈E₂ e∈E₃ = ⊨-trans (τ₁-resp-⊨ (pre₂₃⊨lhs₂₃∨rhs₂₃ e e∈E₂ e∈E₃)) (⊨-trans τ₁-resp-∨ (⊨-resp-∨ (τ₁-resp-∩⊆ (↓₀∩E₁⊆↓₁₂ e (E₂⊆E₁₂ e e∈E₂))) (⊨-trans (τ₁-resp-⊆ (↓₀⊆↓₁₂₃ e)) (τ₁-resp-⊨ (τ₂-resp-⊆ (↓₂₃⊆↓₁₂₃ e (E₃⊆E₂₃ e e∈E₃)))))))

     pre₀⊨lhs₁₂₃ : ∀ e → (e ∈ E₁₂) → (e ∉ E₃) → (pre₀(e) ⊨ lhs₁₂₃(e))
     pre₀⊨lhs₁₂₃ e (left e∈E₁ e∉E₂) e∉E₃ = ⊨-trans (pre₀⊨lhs₀ e e∈E₁ (λ e∈E₂₃ → neither e∉E₂ e∉E₃ (E₂₃⊆E₂∪E₃ e e∈E₂₃))) (lhs₁₂⊨pre₁₂ e e∈E₁ e∉E₂) 
     pre₀⊨lhs₁₂₃ e (right e∉E₁ e∈E₂) e∉E₃ = ⊨-trans (⊨-trans (pre₀⊨rhs₀ e e∉E₁ (E₂⊆E₂₃ e e∈E₂)) (rhs₀⊨rhs₁₂ e e∈E₂ e∉E₃)) (rhs₁₂⊨pre₁₂ e e∉E₁ e∈E₂)
     pre₀⊨lhs₁₂₃ e (both e∈E₁ e∈E₂) e∉E₃ = ⊨-trans (⊨-trans (pre₀⊨lhs₀∨rhs₀ e e∈E₁ (E₂⊆E₂₃ e e∈E₂)) (⊨-resp-∨ ⊨-refl (rhs₀⊨rhs₁₂ e e∈E₂ e∉E₃))) (lhs₁₂∨rhs₁₂⊨pre₁₂ e e∈E₁ e∈E₂)
     
     pre₀⊨rhs₁₂₃ : ∀ e → (e ∉ E₁₂) → (e ∈ E₃) → (pre₀(e) ⊨ rhs₁₂₃(e))
     pre₀⊨rhs₁₂₃ e e∉E₁₂ e∈E₃ = ⊨-trans (pre₀⊨rhs₀ e (λ e∈E₁ → e∉E₁₂ (E₁⊆E₁₂ e e∈E₁)) (E₃⊆E₂₃ e e∈E₃)) (rhs₀⊨rhs₁₂₃ e (λ e∈E₂ → e∉E₁₂ (E₂⊆E₁₂ e e∈E₂)) e∈E₃)
     
     pre₀⊨lhs₁₂₃∨rhs₁₂₃ : ∀ e → (e ∈ E₁₂) → (e ∈ E₃) → (pre₀(e) ⊨ (lhs₁₂₃(e) ∨ rhs₁₂₃(e)))
     pre₀⊨lhs₁₂₃∨rhs₁₂₃ e (left  e∈E₁ e∉E₂) e∈E₃ = ⊨-trans (pre₀⊨lhs₀∨rhs₀ e e∈E₁ (E₃⊆E₂₃ e e∈E₃)) (⊨-resp-∨ (lhs₁₂⊨pre₁₂ e e∈E₁ e∉E₂) (rhs₀⊨rhs₁₂₃ e e∉E₂ e∈E₃))
     pre₀⊨lhs₁₂₃∨rhs₁₂₃ e (right e∉E₁ e∈E₂) e∈E₃ = ⊨-trans (⊨-trans (pre₀⊨rhs₀ e e∉E₁ (E₃⊆E₂₃ e e∈E₃)) (rhs₀⊨rhs₁₂∨rhs₁₂₃ e e∈E₂ e∈E₃)) (⊨-resp-∨ (rhs₁₂⊨pre₁₂ e e∉E₁ e∈E₂) ⊨-refl)
     pre₀⊨lhs₁₂₃∨rhs₁₂₃ e (both e∈E₁ e∈E₂)  e∈E₃ = ⊨-trans (⊨-trans (pre₀⊨lhs₀∨rhs₀ e e∈E₁ (E₃⊆E₂₃ e e∈E₃)) (⊨-trans (⊨-resp-∨ ⊨-refl (rhs₀⊨rhs₁₂∨rhs₁₂₃ e e∈E₂ e∈E₃)) ⊨-assocl-∨)) (⊨-resp-∨ (lhs₁₂∨rhs₁₂⊨pre₁₂ e e∈E₁ e∈E₂) ⊨-refl)
     
     pre₀⊨pre₁₂₃ : ∀ e → (e ∈ E₁₂₃) → (pre₀(e) ⊨ pre₁₂₃(e))
     pre₀⊨pre₁₂₃ e (left e∈E₁₂ e∉E₃)  = ⊨-trans (pre₀⊨lhs₁₂₃ e e∈E₁₂ e∉E₃) (lhs₁₂₃⊨pre₁₂₃ e e∈E₁₂ e∉E₃)
     pre₀⊨pre₁₂₃ e (right e∉E₁₂ e∈E₃) = ⊨-trans (pre₀⊨rhs₁₂₃ e e∉E₁₂ e∈E₃) (rhs₁₂₃⊨pre₁₂₃ e e∉E₁₂ e∈E₃)
     pre₀⊨pre₁₂₃ e (both e∈E₁₂ e∈E₃)  = ⊨-trans (pre₀⊨lhs₁₂₃∨rhs₁₂₃ e e∈E₁₂ e∈E₃) (lhs₁₂₃∨rhs₁₂₃⊨pre₁₂₃ e e∈E₁₂ e∈E₃)
     
     PwP₁₂₃≲PwP₀ : PwP₁₂₃ ≲p PwP₀
     PwP₁₂₃≲PwP₀ = record
                 { E′⊆E = E₀⊆E₁₂₃
                 ; E⊆E′ = E₁₂₃⊆E₀
                 ; act=act′ = λ e e∈E₁₂₃ → refl
                 ; pre′⊨pre = pre₀⊨pre₁₂₃
                 ; ≤⊆≤′ = λ d e d≤₀e → d≤₀e
                 }

     P₁₂₃≲P₀ : P₁₂₃ ≲τ P₀
     P₁₂₃≲P₀ = record
                 { PwP≲PwP′ = PwP₁₂₃≲PwP₀
                 ; τ′⊨τ = λ C ϕ → ⊨-trans (τ₀ϕ⊨τ₁τ₂₃ϕ C ϕ) (τ₁-resp-⊨ (τ₂₃ϕ⊨τ₂τ₃ϕ C ϕ))
                 }

     P₀∈⟦⟨C₁∙C₂⟩∙C₃⟧ : P₀ ∈ ⟦ (C₁ ∙ C₂) ∙ C₃ ⟧
     P₀∈⟦⟨C₁∙C₂⟩∙C₃⟧ = sem-resp-≲τ ((C₁ ∙ C₂) ∙ C₃) P₁₂₃≲P₀ P₁₂₃∈⟦⟨C₁∙C₂⟩∙C₃⟧
     
  ⟦⟨C₁∙C₂⟩∙C₃⟧⊆⟦C₁∙⟨C₂∙C₃⟩⟧ C₁ C₂ C₃ P₀ P₀∈⟦⟨C₁∙C₂⟩∙C₃⟧ = P₀∈⟦C₁∙⟨C₂∙C₃⟩⟧ where

     open _●_ P₀∈⟦⟨C₁∙C₂⟩∙C₃⟧ using (lhs₀ ; rhs₀ ; pre₀⊨lhs₀ ; pre₀⊨rhs₀ ; pre₀⊨lhs₀∨rhs₀) renaming (P₁ to P₁₂ ; P₂ to P₃ ; P₁∈𝒫₁ to P₁₂∈⟦C₁∙C₂⟧ ; P₂∈𝒫₂ to P₃∈⟦C₃⟧ ; E₁⊆E₀ to E₁₂⊆E₀ ; E₂⊆E₀ to E₃⊆E₀ ; E₀⊆E₁∪E₂ to E₀⊆E₁₂∪E₃ ; act₀=act₁ to act₀=act₁₂ ; act₀=act₂ to act₀=act₃ ; ≤₁⊆≤₀ to ≤₁₂⊆≤₀ ; ≤₂⊆≤₀ to ≤₃⊆≤₀ ; causal to causal₀ ; τ₀ϕ⊨τ₁τ₂ϕ to τ₀ϕ⊨τ₁₂τ₃ϕ) 
     open _●_ P₁₂∈⟦C₁∙C₂⟧ using (P₁ ; P₂) renaming (P₁∈𝒫₁ to P₁∈⟦C₁⟧ ; P₂∈𝒫₂ to P₂∈⟦C₂⟧ ; rhs₀ to rhs₁₂ ; E₁⊆E₀ to E₁⊆E₁₂ ; E₂⊆E₀ to E₂⊆E₁₂ ; E₀⊆E₁∪E₂ to E₁₂⊆E₁∪E₂ ; ≤₁⊆≤₀ to ≤₁⊆≤₁₂ ; ≤₂⊆≤₀ to ≤₂⊆≤₁₂ ; act₀=act₁ to act₁₂=act₁ ; act₀=act₂ to act₁₂=act₂ ; pre₀⊨lhs₀ to pre₁₂⊨lhs₁₂ ; pre₀⊨rhs₀ to pre₁₂⊨rhs₁₂ ; pre₀⊨lhs₀∨rhs₀ to pre₁₂⊨lhs₁₂∨rhs₁₂ ; causal to causal₁₂; τ₀ϕ⊨τ₁τ₂ϕ to τ₁₂ϕ⊨τ₁τ₂ϕ)
     
     open PomsetWithPredicateTransformers P₀ using () renaming (PwP to PwP₀ ; E to E₀ ; act to act₀ ; pre to pre₀ ; _≤_ to _≤₀_ ; ≤-refl to ≤₀-refl ; ≤-trans to ≤₀-trans ; ≤-asym to ≤₀-asym ; ↓ to ↓₀ ; PO to PO₀)
     open PomsetWithPredicateTransformers P₁ using () renaming (E to E₁ ; dec-E to dec-E₁ ; ℓ to ℓ₁ ; act to act₁ ; pre to pre₁ ; τ to τ₁ ; τ-resp-⊆ to τ₁-resp-⊆ ; τ-resp-∩⊆ to τ₁-resp-∩⊆ ; τ-resp-⊨ to τ₁-resp-⊨ ; τ-resp-∨ to τ₁-resp-∨; τ-refl-∨ to τ₁-refl-∨ ; τ-refl-∧ to τ₁-refl-∧)
     open PomsetWithPredicateTransformers P₂ using () renaming (E to E₂ ; dec-E to dec-E₂ ; ℓ to ℓ₂ ; act to act₂ ; pre to pre₂ ; τ to τ₂ ; τ-resp-⊆ to τ₂-resp-⊆ ; τ-resp-∩⊆ to τ₂-resp-∩⊆ ; τ-resp-⊨ to τ₂-resp-⊨)
     open PomsetWithPredicateTransformers P₃ using () renaming (E to E₃ ; act to act₃ ; pre to pre₃ ; τ to τ₃)
     open PomsetWithPredicateTransformers P₁₂ using () renaming (E to E₁₂ ; τ to τ₁₂ ; pre to pre₁₂; ↓ to ↓₁₂ ; τ-resp-⊨ to τ₁₂-resp-⊨ ; τ-resp-∨ to τ₁₂-resp-∨)
     
     P₂₃ : PomsetWithPredicateTransformers
     P₂₃ = compP act₀ PO₀ P₂ P₃

     P₁₂₃ : PomsetWithPredicateTransformers
     P₁₂₃ = compP act₀ PO₀ P₁ P₂₃

     open PomsetWithPredicateTransformers P₂₃ using () renaming (E to E₂₃ ; pre to pre₂₃ ; dec-E to dec-E₂₃ ; ↓ to ↓₂₃ ; τ-resp-⊨ to τ₂₃-resp-⊨)
     open PomsetWithPredicateTransformers P₁₂₃ using () renaming (PwP to PwP₁₂₃ ; E to E₁₂₃ ; pre to pre₁₂₃ ; dec-E to dec-E₁₂₃ ; ↓ to ↓₁₂₃)
     
     act₀=act₁ : ∀ e → (e ∈ E₁) → (act₀(e) ≡ act₁(e))
     act₀=act₁ e e∈E₁ = ≡-trans (act₀=act₁₂ e (E₁⊆E₁₂ e e∈E₁)) (act₁₂=act₁ e e∈E₁)
     
     act₀=act₂ : ∀ e → (e ∈ E₂) → (act₀(e) ≡ act₂(e))
     act₀=act₂ e e∈E₂ = ≡-trans (act₀=act₁₂ e (E₂⊆E₁₂ e e∈E₂)) (act₁₂=act₂ e e∈E₂)

     causal₂₃ : ∀ d e → (d ∈ E₂) → (e ∈ E₃) → Causal (act₂ d) (act₃ e) → (d ≤₀ e)
     causal₂₃ d e d∈E₂ e∈E₃ a₂#a₃ = causal₀ d e (E₂⊆E₁₂ d d∈E₂)  e∈E₃ (≡-subst₂ Causal (≡-symm (act₁₂=act₂ d d∈E₂)) refl a₂#a₃)
     
     causal₁₂₃ : ∀ d e → (d ∈ E₁) → (e ∈ E₂₃) → Causal (act₁ d) (act₀ e) → (d ≤₀ e)
     causal₁₂₃ d e d∈E₁ (left e∈E₂ _) a₁#a₂₃ = ≤₁₂⊆≤₀ d e (causal₁₂ d e d∈E₁ e∈E₂ (≡-subst₂ Causal refl (act₀=act₂ e e∈E₂) a₁#a₂₃))
     causal₁₂₃ d e d∈E₁ (right _ e∈E₃) a₁#a₂₃ = causal₀ d e (E₁⊆E₁₂ d d∈E₁) e∈E₃ ((≡-subst₂ Causal (≡-symm (act₁₂=act₁ d d∈E₁)) (act₀=act₃ e e∈E₃) a₁#a₂₃))
     causal₁₂₃ d e d∈E₁ (both _ e∈E₃) a₁#a₂₃ = causal₀ d e (E₁⊆E₁₂ d d∈E₁) e∈E₃ (≡-subst₂ Causal (≡-symm (act₁₂=act₁ d d∈E₁)) (act₀=act₃ e e∈E₃)  a₁#a₂₃)
     
     PO₀∈CompP₂P₃ : Compatible act₀ PO₀ P₂ P₃
     PO₀∈CompP₂P₃ = record
                      { act₀=act₁ = act₀=act₂
                      ; act₀=act₂ = act₀=act₃
                      ; ≤₁⊆≤₀ = λ d e d≤₂e → ≤₁₂⊆≤₀ d e (≤₂⊆≤₁₂ d e d≤₂e)
                      ; ≤₂⊆≤₀ = ≤₃⊆≤₀
                      ; causal = causal₂₃ }
     
     PO₀∈CompP₁P₂₃ : Compatible act₀ PO₀ P₁ P₂₃
     PO₀∈CompP₁P₂₃ = record
                       { act₀=act₁ = act₀=act₁
                       ; act₀=act₂ = λ e e∈E₂₃ → refl
                       ; ≤₁⊆≤₀ = λ d e d≤₁e → ≤₁₂⊆≤₀ d e (≤₁⊆≤₁₂ d e d≤₁e)
                       ; ≤₂⊆≤₀ = λ d e d≤₀e → d≤₀e
                       ; causal = causal₁₂₃ }
     
     P₂₃∈⟦C₂∙C₃⟧ : P₂₃ ∈ ⟦ C₂ ∙ C₃ ⟧
     P₂₃∈⟦C₂∙C₃⟧ = compP∈⟦C₁∙C₂⟧ C₂ C₃ act₀ PO₀ P₂ P₃ P₂∈⟦C₂⟧ P₃∈⟦C₃⟧ PO₀∈CompP₂P₃
     
     P₁₂₃∈⟦C₁∙⟨C₂∙C₃⟩⟧ : P₁₂₃ ∈ ⟦ C₁ ∙ (C₂ ∙ C₃) ⟧
     P₁₂₃∈⟦C₁∙⟨C₂∙C₃⟩⟧ = compP∈⟦C₁∙C₂⟧ C₁ (C₂ ∙ C₃) act₀ PO₀ P₁ P₂₃ P₁∈⟦C₁⟧ P₂₃∈⟦C₂∙C₃⟧ PO₀∈CompP₁P₂₃

     open _●_ P₂₃∈⟦C₂∙C₃⟧ using () renaming (E₁⊆E₀ to E₂⊆E₂₃ ; E₂⊆E₀ to E₃⊆E₂₃ ; rhs₀ to rhs₂₃ ; pre₀⊨lhs₀ to pre₂₃⊨lhs₂₃)
     open _●_ P₁₂₃∈⟦C₁∙⟨C₂∙C₃⟩⟧ using () renaming (lhs₀ to lhs₁₂₃ ; rhs₀ to rhs₁₂₃ ; pre₀⊨rhs₀ to pre₁₂₃⊨rhs₁₂₃)
     
     lemmas₂₃ : compLemmas C₂ C₃ act₀ PO₀ P₂ P₃
     lemmas₂₃ = record { P₁∈⟦C₁⟧ = P₂∈⟦C₂⟧ ; P₂∈⟦C₂⟧ = P₃∈⟦C₃⟧ ; PO₀∈CompP₁P₂ = PO₀∈CompP₂P₃ }
     
     lemmas₁₂₃ : compLemmas C₁ (C₂ ∙ C₃) act₀ PO₀ P₁ P₂₃
     lemmas₁₂₃ = record { P₁∈⟦C₁⟧ = P₁∈⟦C₁⟧ ; P₂∈⟦C₂⟧ = P₂₃∈⟦C₂∙C₃⟧ ; PO₀∈CompP₁P₂ = PO₀∈CompP₁P₂₃ }

     open compLemmas lemmas₂₃ using () renaming (lhs₀⊨pre₀ to lhs₂₃⊨pre₂₃; rhs₀⊨pre₀ to rhs₂₃⊨pre₂₃ ; lhs₀∨rhs₀⊨pre₀ to lhs₂₃∨rhs₂₃⊨pre₂₃)
     open compLemmas lemmas₁₂₃ using () renaming (lhs₀⊨pre₀ to lhs₁₂₃⊨pre₁₂₃; rhs₀⊨pre₀ to rhs₁₂₃⊨pre₁₂₃ ; lhs₀∨rhs₀⊨pre₀ to lhs₁₂₃∨rhs₁₂₃⊨pre₁₂₃)

     E₂₃⊆E₀ : E₂₃ ⊆ E₀
     E₂₃⊆E₀ = ⊆-elim-∪ (⊆-trans E₂⊆E₁₂ E₁₂⊆E₀) E₃⊆E₀
     
     E₁₂₃⊆E₀ : E₁₂₃ ⊆ E₀
     E₁₂₃⊆E₀ = ⊆-elim-∪ (⊆-trans E₁⊆E₁₂ E₁₂⊆E₀) E₂₃⊆E₀
     
     E₀⊆E₁₂₃ : E₀ ⊆ E₁₂₃
     E₀⊆E₁₂₃ = ⊆-trans E₀⊆E₁₂∪E₃ (⊆-trans (⊆-resp-∪ E₁₂⊆E₁∪E₂ ⊆-refl) ⊆-assocr-∪)

     E₁₂⊆E₁₂₃ : E₁₂ ⊆ E₁₂₃
     E₁₂⊆E₁₂₃ = ⊆-trans E₁₂⊆E₀ E₀⊆E₁₂₃
     
     ↓₀⊆↓₁₂₃ : ∀ e → (↓₀(e) ⊆ ↓₁₂₃(e))
     ↓₀⊆↓₁₂₃ e = ⊆-resp-∩ E₀⊆E₁₂₃ ⊆-refl
     
     ↓₀∩E₂₃⊆↓₂₃ : ∀ e → (e ∈ E₂₃) → ((↓₀(e) ∩ E₂₃) ⊆ ↓₂₃(e))
     ↓₀∩E₂₃⊆↓₂₃ e e∈E₂₃  d ((d∈E₀ , d≤₀e) , d∈E₂₃) = (d∈E₂₃ , d≤₀e)
     
     ↓₀∩E₂⊆↓₂₃ : ∀ e → (e ∈ E₂₃) → ((↓₀(e) ∩ E₂) ⊆ ↓₂₃(e))
     ↓₀∩E₂⊆↓₂₃ e e∈E₂₃ d (d≤e , d∈E₂) = ↓₀∩E₂₃⊆↓₂₃ e e∈E₂₃ d (d≤e , E₂⊆E₂₃ d d∈E₂)
     
     ↓₁₂⊆↓₁₂₃ : ∀ e → (e ∈ E₁₂) → (↓₁₂(e) ⊆ ↓₁₂₃(e))
     ↓₁₂⊆↓₁₂₃ e e∈E₁₂ d (d∈E₁₂ , d≤₁₂e) = (E₁₂⊆E₁₂₃ d d∈E₁₂ , ≤₁₂⊆≤₀ d e d≤₁₂e)
     
     rhs₀⊨rhs₁₂₃ : ∀ e → (e ∉ E₂) → (e ∈ E₃) → (rhs₀ e) ⊨ (rhs₁₂₃ e)
     rhs₀⊨rhs₁₂₃ e e∉E₂ e∈E₃ = ⊨-trans (τ₁₂ϕ⊨τ₁τ₂ϕ (↓₀ e) _) (⊨-trans (τ₁-resp-⊆ (↓₀⊆↓₁₂₃ e)) (τ₁-resp-⊨ (⊨-trans (τ₂-resp-∩⊆ (↓₀∩E₂⊆↓₂₃ e (E₃⊆E₂₃ e e∈E₃))) (rhs₂₃⊨pre₂₃ e e∉E₂ e∈E₃))))

     rhs₁₂⊨rhs₁₂₃ : ∀ e → (e ∈ E₂) → (e ∉ E₃) → (rhs₁₂ e) ⊨ (rhs₁₂₃ e)
     rhs₁₂⊨rhs₁₂₃ e e∈E₂ e∉E₃ = ⊨-trans (τ₁-resp-⊆ (↓₁₂⊆↓₁₂₃ e (E₂⊆E₁₂ e e∈E₂))) (τ₁-resp-⊨ (lhs₂₃⊨pre₂₃ e e∈E₂ e∉E₃))

     rhs₁₂∨rhs₀⊨rhs₁₂₃ : ∀ e → (e ∈ E₂) → (e ∈ E₃) → ((rhs₁₂(e) ∨ rhs₀(e)) ⊨ rhs₁₂₃(e))
     rhs₁₂∨rhs₀⊨rhs₁₂₃ e e∈E₂ e∈E₃ = ⊨-trans (⊨-resp-∨ (τ₁-resp-⊆ (↓₁₂⊆↓₁₂₃ e (E₂⊆E₁₂ e e∈E₂))) (⊨-trans (τ₁₂ϕ⊨τ₁τ₂ϕ (↓₀ e) (pre₃ e)) (⊨-trans (τ₁-resp-⊆ (↓₀⊆↓₁₂₃ e)) (τ₁-resp-⊨ (τ₂-resp-∩⊆ (↓₀∩E₂⊆↓₂₃ e (E₃⊆E₂₃ e e∈E₃))))))) (⊨-trans τ₁-refl-∨  (τ₁-resp-⊨ (lhs₂₃∨rhs₂₃⊨pre₂₃ e e∈E₂ e∈E₃)))
     
     pre₀⊨lhs₁₂₃ : ∀ e → (e ∈ E₁) → (e ∉ E₂₃) → (pre₀(e) ⊨ lhs₁₂₃(e))
     pre₀⊨lhs₁₂₃ e e∈E₁ e∉E₂₃ = ⊨-trans (pre₀⊨lhs₀ e (E₁⊆E₁₂ e e∈E₁) (λ e∈E₃ → e∉E₂₃ (E₃⊆E₂₃ e e∈E₃))) (pre₁₂⊨lhs₁₂ e e∈E₁ (λ e∈E₂ → e∉E₂₃ (E₂⊆E₂₃ e e∈E₂)))
     
     pre₀⊨rhs₁₂₃ : ∀ e → (e ∉ E₁) → (e ∈ E₂₃) → (pre₀(e) ⊨ rhs₁₂₃(e))
     pre₀⊨rhs₁₂₃ e e∉E₁ (left e∈E₂ e∉E₃) = ⊨-trans (pre₀⊨lhs₀ e (E₂⊆E₁₂ e e∈E₂) e∉E₃) (⊨-trans (pre₁₂⊨rhs₁₂ e e∉E₁ e∈E₂) (rhs₁₂⊨rhs₁₂₃ e e∈E₂ e∉E₃))
     pre₀⊨rhs₁₂₃ e e∉E₁ (right e∉E₂ e∈E₃) = ⊨-trans (pre₀⊨rhs₀ e (λ e∈E₁₂ → neither e∉E₁ e∉E₂ (E₁₂⊆E₁∪E₂ e e∈E₁₂)) e∈E₃) (rhs₀⊨rhs₁₂₃ e e∉E₂ e∈E₃)
     pre₀⊨rhs₁₂₃ e e∉E₁ (both e∈E₂ e∈E₃) = ⊨-trans (pre₀⊨lhs₀∨rhs₀ e (E₂⊆E₁₂ e e∈E₂) e∈E₃) (⊨-trans (⊨-resp-∨ (pre₁₂⊨rhs₁₂ e e∉E₁ e∈E₂) ⊨-refl) (rhs₁₂∨rhs₀⊨rhs₁₂₃ e e∈E₂ e∈E₃))
     
     pre₀⊨lhs₁₂₃∨rhs₁₂₃ : ∀ e → (e ∈ E₁) → (e ∈ E₂₃) → (pre₀(e) ⊨ (lhs₁₂₃(e) ∨ rhs₁₂₃(e)))
     pre₀⊨lhs₁₂₃∨rhs₁₂₃ e e∈E₁ (left e∈E₂ e∉E₃) = ⊨-trans (pre₀⊨lhs₀ e (E₁⊆E₁₂ e e∈E₁) e∉E₃) (⊨-trans (pre₁₂⊨lhs₁₂∨rhs₁₂ e e∈E₁ e∈E₂) (⊨-resp-∨ ⊨-refl (rhs₁₂⊨rhs₁₂₃ e e∈E₂ e∉E₃)))
     pre₀⊨lhs₁₂₃∨rhs₁₂₃ e e∈E₁ (right e∉E₂ e∈E₃) = ⊨-trans (pre₀⊨lhs₀∨rhs₀ e (E₁⊆E₁₂ e e∈E₁) e∈E₃) (⊨-resp-∨ (pre₁₂⊨lhs₁₂ e e∈E₁ e∉E₂) (rhs₀⊨rhs₁₂₃ e e∉E₂ e∈E₃))
     pre₀⊨lhs₁₂₃∨rhs₁₂₃ e e∈E₁ (both e∈E₂ e∈E₃) = ⊨-trans (pre₀⊨lhs₀∨rhs₀ e (E₁⊆E₁₂ e e∈E₁) e∈E₃) (⊨-trans (⊨-resp-∨ (pre₁₂⊨lhs₁₂∨rhs₁₂ e e∈E₁ e∈E₂) ⊨-refl) (⊨-trans ⊨-assocr-∨ (⊨-resp-∨ ⊨-refl (rhs₁₂∨rhs₀⊨rhs₁₂₃ e e∈E₂ e∈E₃))))
     
     pre₀⊨pre₁₂₃ : ∀ e → (e ∈ E₁₂₃) → (pre₀(e) ⊨ pre₁₂₃(e))
     pre₀⊨pre₁₂₃ e (left e∈E₁ e∉E₂₃)  = ⊨-trans (pre₀⊨lhs₁₂₃ e e∈E₁ e∉E₂₃) (lhs₁₂₃⊨pre₁₂₃ e e∈E₁ e∉E₂₃)
     pre₀⊨pre₁₂₃ e (right e∉E₁ e∈E₂₃) = ⊨-trans (pre₀⊨rhs₁₂₃ e e∉E₁ e∈E₂₃) (rhs₁₂₃⊨pre₁₂₃ e e∉E₁ e∈E₂₃)
     pre₀⊨pre₁₂₃ e (both e∈E₁ e∈E₂₃)  = ⊨-trans (pre₀⊨lhs₁₂₃∨rhs₁₂₃ e e∈E₁ e∈E₂₃) (lhs₁₂₃∨rhs₁₂₃⊨pre₁₂₃ e e∈E₁ e∈E₂₃)

     PwP₁₂₃≲PwP₀ : PwP₁₂₃ ≲p PwP₀
     PwP₁₂₃≲PwP₀ = record
                 { E′⊆E = E₀⊆E₁₂₃
                 ; E⊆E′ = E₁₂₃⊆E₀
                 ; act=act′ = λ e e∈E₁₂₃ → refl
                 ; pre′⊨pre = pre₀⊨pre₁₂₃
                 ; ≤⊆≤′ = λ d e d≤₀e → d≤₀e
                }


     P₁₂₃≲P₀ : P₁₂₃ ≲τ P₀
     P₁₂₃≲P₀ = record
                 { PwP≲PwP′ = PwP₁₂₃≲PwP₀
                 ; τ′⊨τ = λ C ϕ → ⊨-trans (τ₀ϕ⊨τ₁₂τ₃ϕ C ϕ) (τ₁₂ϕ⊨τ₁τ₂ϕ C (τ₃ C ϕ))
                }

     P₀∈⟦C₁∙⟨C₂∙C₃⟩⟧ : P₀ ∈ ⟦ C₁ ∙ (C₂ ∙ C₃) ⟧
     P₀∈⟦C₁∙⟨C₂∙C₃⟩⟧ = sem-resp-≲τ (C₁ ∙ (C₂ ∙ C₃)) P₁₂₃≲P₀ P₁₂₃∈⟦C₁∙⟨C₂∙C₃⟩⟧
     
  -- QED
