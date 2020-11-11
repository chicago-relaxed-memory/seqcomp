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
                    ; P₂ = Pskip act₀
                    ; P₁∈𝒫₁ = P₀∈⟦C⟧
                    ; P₂∈𝒫₂ = Pskip∈⟦skip⟧ act₀
                    ; E₀⊆E₁∪E₂ = λ e e∈E₀ → left e∈E₀ (λ ())
                    ; E₁⊆E₀ = λ e e∈E₀ → e∈E₀
                    ; E₂⊆E₀ = λ e ()
                    ; ≤₁⊆≤₀ = λ d e d≤₀e → d≤₀e
                    ; ≤₂⊆≤₀ = λ { e .e refl → ≤₀-refl }
                    ; coherence = λ d e d∈E₀ ()
                    ; pre₀⊨pre₁ = λ e e∈E₀ _ → ⊨-refl
                    ; pre₀⊨pre′₂ = λ e e∉E₀ ()
                    ; pre₀⊨pre₁∨pre′₂ = λ e e∈E₀ () 
                    ; act₀=act₁ = λ e e∈E₀ → refl
                    ; act₀=act₂ = λ e ()
                    ; τ₀ϕ⊨τ₁τ₂ϕ = λ C ϕ → ⊨-refl
                    }

  ⟦C∙skip⟧⊆⟦C⟧ C P₀ P₀∈⟦C∙skip⟧ = P₀∈⟦C⟧ where

    open _●_ P₀∈⟦C∙skip⟧ using (P₁ ; P₂ ; E₀⊆E₁∪E₂ ; E₁⊆E₀ ; E₂⊆E₀ ; act₀=act₁ ; pre₀⊨pre₁ ; ≤₁⊆≤₀ ; τ₀ϕ⊨τ₁τ₂ϕ) renaming (P₁∈𝒫₁ to P₁∈⟦C⟧ ; P₂∈𝒫₂ to P₂∈⟦skip⟧)
    open SKIP P₂∈⟦skip⟧ using () renaming (E₀⊆∅ to E₂⊆∅ ; τ₀ϕ⊨ϕ to τ₂ϕ⊨ϕ)

    open Pomset P₀ using () renaming (E to E₀)
    open Pomset P₁ using () renaming (E to E₁ ; τ-resp-⊨ to τ₁-resp-⊨)
    open Pomset P₂ using () renaming (E to E₂)

    E₀⊆E₁ : (E₀ ⊆ E₁)
    E₀⊆E₁ e e∈E₀ with E₀⊆E₁∪E₂ e e∈E₀
    E₀⊆E₁ e e∈E₀ | left e∈E₁ _ = e∈E₁
    E₀⊆E₁ e e∈E₀ | right _ e∈E₂ = CONTRADICTION (E₂⊆∅ e e∈E₂)
    E₀⊆E₁ e e∈E₀ | both _  e∈E₂ =  CONTRADICTION (E₂⊆∅ e e∈E₂)

    P₁≲P₀ : P₁ ≲ P₀
    P₁≲P₀ = record
              { E′⊆E = E₀⊆E₁
              ; E⊆E′ = E₁⊆E₀
              ; act=act′ = λ e e∈E₁ → ≡-symm (act₀=act₁ e e∈E₁)
              ; pre′⊨pre = λ e e∈E₁ → pre₀⊨pre₁ e e∈E₁ (E₂⊆∅ e)
              ; ≤⊆≤′ = ≤₁⊆≤₀
              ; τ′⊨τ = λ C ϕ → ⊨-trans (τ₀ϕ⊨τ₁τ₂ϕ C ϕ) (τ₁-resp-⊨ C _ ϕ (τ₂ϕ⊨ϕ C ϕ))
              }
    
    P₀∈⟦C⟧ = sem-resp-≲ P₁≲P₀ P₁∈⟦C⟧

  -- PROOF that skip is a left unit

  ⟦C⟧⊆⟦skip∙C⟧ C P₀ P₀∈⟦C⟧ = P₀∈⟦skip∙C⟧ where

    open Pomset P₀ using () renaming (act to act₀ ; ≤-refl to ≤₀-refl)

    P₀∈⟦skip∙C⟧ : P₀ ∈ ⟦ skip ∙ C ⟧
    P₀∈⟦skip∙C⟧ = record
                    { P₁ = Pskip act₀
                    ; P₂ = P₀
                    ; P₁∈𝒫₁ = Pskip∈⟦skip⟧ act₀
                    ; P₂∈𝒫₂ = P₀∈⟦C⟧
                    ; E₀⊆E₁∪E₂ = λ e e∈E₀ → right (λ ()) e∈E₀
                    ; E₁⊆E₀ = λ e ()
                    ; E₂⊆E₀ = λ e e∈E₀ → e∈E₀
                    ; ≤₁⊆≤₀ = λ { e .e refl → ≤₀-refl }
                    ; ≤₂⊆≤₀ = λ d e d≤₀e → d≤₀e
                    ; coherence = λ d e ()
                    ; pre₀⊨pre₁ = λ e ()
                    ; pre₀⊨pre′₂ = λ e _ e∈E₀ → ⊨-refl
                    ; pre₀⊨pre₁∨pre′₂ = λ e ()
                    ; act₀=act₁ = λ e ()
                    ; act₀=act₂ = λ e e∈E₀ → refl
                    ; τ₀ϕ⊨τ₁τ₂ϕ = λ C ϕ → ⊨-refl
                    }
  
  ⟦skip∙C⟧⊆⟦C⟧ C P₀ P₀∈⟦skip∙C⟧ = P₀∈⟦C⟧ where
  
    open _●_ P₀∈⟦skip∙C⟧ using (P₁ ; P₂ ; E₀⊆E₁∪E₂ ; E₁⊆E₀ ; E₂⊆E₀ ; act₀=act₂ ; pre′₂ ; pre₀⊨pre′₂ ; ≤₂⊆≤₀ ; τ₀ϕ⊨τ₁τ₂ϕ) renaming (P₁∈𝒫₁ to P₁∈⟦skip⟧ ; P₂∈𝒫₂ to P₂∈⟦C⟧)
    open SKIP P₁∈⟦skip⟧ using () renaming (E₀⊆∅ to E₁⊆∅ ; τ₀ϕ⊨ϕ to τ₁ϕ⊨ϕ)

    open Pomset P₀ using () renaming (E to E₀ ; ↓RW to ↓RW₀)
    open Pomset P₁ using () renaming (E to E₁)
    open Pomset P₂ using () renaming (E to E₂ ; pre to pre₂ ; τ to τ₂ ; τ-resp-⊨ to τ₂-resp-⊨)

    E₀⊆E₂ : (E₀ ⊆ E₂)
    E₀⊆E₂ e e∈E₀ with E₀⊆E₁∪E₂ e e∈E₀
    E₀⊆E₂ e e∈E₀ | right _ e∈E₂ = e∈E₂
    E₀⊆E₂ e e∈E₀ | left e∈E₁ _ = CONTRADICTION (E₁⊆∅ e e∈E₁)
    E₀⊆E₂ e e∈E₀ | both e∈E₁ _ =  CONTRADICTION (E₁⊆∅ e e∈E₁)
    
    P₂≲P₀ : P₂ ≲ P₀
    P₂≲P₀ = record
              { E′⊆E = E₀⊆E₂
              ; E⊆E′ = E₂⊆E₀
              ; act=act′ = λ e e∈E₀ → ≡-symm (act₀=act₂ e e∈E₀)
              ; pre′⊨pre = λ e e∈E₂ → ⊨-trans (pre₀⊨pre′₂ e (E₁⊆∅ e) e∈E₂) (τ₁ϕ⊨ϕ (↓RW₀(e)) (pre₂(e)))
              ; ≤⊆≤′ =  ≤₂⊆≤₀
              ; τ′⊨τ = λ C ϕ → ⊨-trans (τ₀ϕ⊨τ₁τ₂ϕ C ϕ) (τ₁ϕ⊨ϕ C (τ₂ C ϕ))
              }
    
    P₀∈⟦C⟧ = sem-resp-≲ P₂≲P₀ P₂∈⟦C⟧
  
  -- PROOF of associativity

  ⟦C₁∙⟨C₂∙C₃⟩⟧⊆⟦⟨C₁∙C₂⟩∙C₃⟧ C₁ C₂ C₃ P₀ P₀∈⟦C₁∙⟨C₂∙C₃⟩⟧ =  P₀∈⟦⟨C₁∙C₂⟩∙C₃⟧ where

     open _●_ P₀∈⟦C₁∙⟨C₂∙C₃⟩⟧ using (P₁ ; ≤₁⊆≤₀ ; act₀=act₁ ; pre₀⊨pre₁) renaming (P₂ to P₂₃ ; P₁∈𝒫₁ to P₁∈⟦C₁⟧ ; P₂∈𝒫₂ to P₂₃∈⟦C₂∙C₃⟧ ; act₀=act₂ to act₀=act₂₃ ; pre′₂ to pre′₂₃ ; ≤₂⊆≤₀ to ≤₂₃⊆≤₀ ; coherence to coherence₀)
     open _●_ P₂₃∈⟦C₂∙C₃⟧ using () renaming (P₁ to P₂ ; P₂ to P₃ ; P₁∈𝒫₁ to P₂∈⟦C₂⟧ ; P₂∈𝒫₂ to P₃∈⟦C₃⟧ ; pre′₂ to pre′₃ ; E₁⊆E₀ to E₂⊆E₂₃ ; E₂⊆E₀ to E₃⊆E₂₃ ; ≤₁⊆≤₀ to ≤₂⊆≤₂₃ ; ≤₂⊆≤₀ to ≤₃⊆≤₂₃ ; act₀=act₁ to act₂₃=act₂ ; act₀=act₂ to act₂₃=act₃)
     
     open Pomset P₀ using () renaming (E to E₀ ; act to act₀ ; _≤_ to _≤₀_ ; ≤-refl to ≤₀-refl ; ≤-trans to ≤₀-trans ; ≤-asym to ≤₀-asym ; ↓RW to ↓RW₀m ; PO to PO₀)
     open Pomset P₁ using () renaming (E to E₁ ; dec-E to dec-E₁ ; ℓ to ℓ₁ ; act to act₁ ; pre to pre₁ ; τ to τ₁ ; τ-resp-⊆ to τ₁-resp-⊆ ; τ-resp-⊨ to τ₁-resp-⊨)
     open Pomset P₂ using () renaming (E to E₂ ; dec-E to dec-E₂ ; ℓ to ℓ₂ ; act to act₂ ; pre to pre₂ ; τ to τ₂ ; τ-resp-⊆ to τ₂-resp-⊆ ; τ-resp-⊨ to τ₂-resp-⊨)
     open Pomset P₃ using () renaming (E to E₃ ; act to act₃)

     P₁₂ : Pomset
     P₁₂ = Pcomp PO₀ P₁ P₂

     P₁₂₃ : Pomset
     P₁₂₃ = Pcomp PO₀ P₁₂ P₃

     open Pomset P₁₂ using () renaming (E to E₁₂ ; act to act₁₂)
     open Pomset P₁₂₃ using () renaming (E to E₁₂₃ ; act to act₁₂₃)
     
     act₀=act₁₂ : ∀ e → (e ∈ E₁₂) → (act₀(e) ≡ act₁₂(e))
     act₀=act₁₂ = {!!}

     act₀=act₁₂₃ : ∀ e → (e ∈ E₁₂₃) → (act₀(e) ≡ act₁₂₃(e))
     act₀=act₁₂₃ = {!!}

     coherence₁₂₃ : ∀ d e → (d ∈ E₁₂) → (e ∈ E₃) → (act₁₂ d , act₃ e) ∈ Conflicts → (d ≤₀ e)
     coherence₁₂₃ = {!!}
     
     PO₀∈CompP₁P₂ : PO₀ ∈ Compatible P₁ P₂
     PO₀∈CompP₁P₂ = record
                      { act₁=act₂ = λ{ e (e∈E₁ , e∈E₂) → ≡-trans (≡-symm (act₀=act₁ e e∈E₁)) (≡-trans (act₀=act₂₃ e (E₂⊆E₂₃ e e∈E₂)) (act₂₃=act₂ e e∈E₂)) }
                      ; ≤₁⊆≤₀ = ≤₁⊆≤₀
                      ; ≤₂⊆≤₀ = λ d e d≤₂e → ≤₂₃⊆≤₀ d e (≤₂⊆≤₂₃ d e d≤₂e)
                      ; coherence = λ d e d∈E₁ e∈E₂ a₁#a₂ → coherence₀ d e d∈E₁ (E₂⊆E₂₃ e e∈E₂) ((≡-subst (λ X → (act₁ d , X) ∈ Conflicts) (≡-symm (act₂₃=act₂ e e∈E₂)) a₁#a₂)) }
     
     PO₀∈CompP₁₂P₃ : PO₀ ∈ Compatible P₁₂ P₃
     PO₀∈CompP₁₂P₃ = record
                       { act₁=act₂ = λ{ e (e∈E₁₂ , e∈E₃) → ≡-trans (≡-symm (act₀=act₁₂ e e∈E₁₂)) (≡-trans (act₀=act₂₃ e (E₃⊆E₂₃ e e∈E₃)) (act₂₃=act₃ e e∈E₃)) }
                       ; ≤₁⊆≤₀ = λ d e d≤₀e → d≤₀e
                       ; ≤₂⊆≤₀ = λ d e d≤₃e → ≤₂₃⊆≤₀ d e (≤₃⊆≤₂₃ d e d≤₃e)
                       ; coherence = coherence₁₂₃ }
     
     P₁₂∈⟦C₁∙C₂⟧ : P₁₂ ∈ ⟦ C₁ ∙ C₂ ⟧
     P₁₂∈⟦C₁∙C₂⟧ = Pcomp∈⟦C₁∙C₂⟧ C₁ C₂ PO₀ P₁ P₂ P₁∈⟦C₁⟧ P₂∈⟦C₂⟧ PO₀∈CompP₁P₂

     P₁₂∈⟦⟨C₁∙C₂⟩∙C₃⟧ : P₁₂₃ ∈ ⟦ (C₁ ∙ C₂) ∙ C₃ ⟧
     P₁₂∈⟦⟨C₁∙C₂⟩∙C₃⟧ = Pcomp∈⟦C₁∙C₂⟧ (C₁ ∙ C₂) C₃ PO₀ P₁₂ P₃ P₁₂∈⟦C₁∙C₂⟧ P₃∈⟦C₃⟧ PO₀∈CompP₁₂P₃

     P₁₂₃≲P₀ : P₁₂₃ ≲ P₀
     P₁₂₃≲P₀ = record
                 { E′⊆E = λ e e∈E₀ → {!!}
                 ; E⊆E′ = λ e e∈E₁₂₃ → {!!}
                 ; act=act′ = λ e e∈E₁₂₃ → ≡-symm (act₀=act₁₂₃ e e∈E₁₂₃)
                 ; pre′⊨pre = {!!}
                 ; ≤⊆≤′ = λ d e d≤₀e → d≤₀e
                 ; τ′⊨τ = {!!}
                 }

     P₀∈⟦⟨C₁∙C₂⟩∙C₃⟧ : P₀ ∈ ⟦ (C₁ ∙ C₂) ∙ C₃ ⟧
     P₀∈⟦⟨C₁∙C₂⟩∙C₃⟧ = sem-resp-≲ P₁₂₃≲P₀ P₁₂∈⟦⟨C₁∙C₂⟩∙C₃⟧
     
  ⟦⟨C₁∙C₂⟩∙C₃⟧⊆⟦C₁∙⟨C₂∙C₃⟩⟧ = {!!}

  -- QED
