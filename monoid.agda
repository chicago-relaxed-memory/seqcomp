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

    open Pomset P₀ using () renaming (≤-refl to ≤₀-refl)

    P₀∈⟦C∙skip⟧ : P₀ ∈ ⟦ C ∙ skip ⟧
    P₀∈⟦C∙skip⟧ = record
                    { P₁ = P₀
                    ; P₂ = Pskip
                    ; P₁∈𝒫₁ = P₀∈⟦C⟧
                    ; P₂∈𝒫₂ = Pskip∈⟦skip⟧
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

    open Pomset P₀ using () renaming (≤-refl to ≤₀-refl)

    P₀∈⟦skip∙C⟧ : P₀ ∈ ⟦ skip ∙ C ⟧
    P₀∈⟦skip∙C⟧ = record
                    { P₁ = Pskip
                    ; P₂ = P₀
                    ; P₁∈𝒫₁ = Pskip∈⟦skip⟧
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

     -- open _●_ P₀∈⟦C₁∙⟨C₂∙C₃⟩⟧ using (P₁) renaming (P₂ to P₂₃ ; P₁∈𝒫₁ to P₁∈⟦C₁⟧ ; P₂∈𝒫₂ to P₂₃∈⟦C₂∙C₃⟧ ; just to just₂₃ ; pre′₂ to pre′₂₃)
     -- open _●_ P₂₃∈⟦C₂∙C₃⟧ using () renaming (P₁ to P₂ ; P₂ to P₃ ; P₁∈𝒫₁ to P₂∈⟦C₂⟧ ; P₂∈𝒫₂ to P₃∈⟦C₃⟧ ; pre′₂ to pre′₃)

     -- open Pomset P₀ using () renaming (E to E₀ ; _≤_ to _≤₀_ ; ≤-refl to ≤₀-refl ; ≤-trans to ≤₀-trans ; ≤-asym to ≤₀-asym ; I-max to I₀-max)
     -- open Pomset P₁ using () renaming (E to E₁ ; I to I₁ ; X to X₁ ; I⊆E to I₁⊆E₁ ; E⊆I⊎X to E₁⊆I₁⊎X₁ ; ℓ to ℓ₁ ; act to act₁ ; pre to pre₁ ; dec-E to dec-E₁ ; dec-X to dec-X₁ ; dec-I to dec-I₁)
     -- open Pomset P₂ using () renaming (E to E₂ ; I to I₂ ; X to X₂ ; I⊆E to I₂⊆E₂ ; ℓ to ℓ₂ ; act to act₂ ; post to post₂ ; dec-E to dec-E₂ ; dec-X to dec-X₂ ; dec-I to dec-I₂)

     -- pre′₂ = pre′₂₃
     
     -- prex₁₂ : Event → Formula
     -- prex₁₂ e with dec-X₁ e
     -- prex₁₂ e | yes _ = pre₁ e ∨ pre′₂ e
     -- prex₁₂ e | no  _ = pre′₂ e
     
     -- pre₁₂ : Event → Formula
     -- pre₁₂ e with dec-X₂ e
     -- pre₁₂ e | yes _ = prex₁₂ e
     -- pre₁₂ e | no  _ = pre₁ e

     -- act₁₂ : Event → Action
     -- act₁₂ e with dec-X₁ e
     -- act₁₂ e | yes _ = act₁ e
     -- act₁₂ e | no  _ = act₂ e
     
     -- ℓ₁₂ : Event → (Formula × Action)
     -- ℓ₁₂ e = (pre₁₂ e , act₁₂ e)
     
     -- E₁₂ = (I₁ ∩ I₂) ⊎ (X₁ ∪ X₂)
     -- I₁₂ = _

     -- data _≤₁₂_ : Event → Event → Set where
     --   ≤₁₂-refl : ∀ {e} → (e ≤₁₂ e)
     --   ≤₀-in-≤₁₂ : ∀ {d e} → (d ∉ I₁₂) → (d ≤₀ e) → (d ≤₁₂ e)

     -- ≤₁₂-trans : ∀ {c d e} → (c ≤₁₂ d) → (d ≤₁₂ e) → (c ≤₁₂ e)
     -- ≤₁₂-trans ≤₁₂-refl d≤e = d≤e
     -- ≤₁₂-trans c≤d ≤₁₂-refl = c≤d
     -- ≤₁₂-trans (≤₀-in-≤₁₂ c∉I c≤d) (≤₀-in-≤₁₂ _ d≤e) = ≤₀-in-≤₁₂ c∉I (≤₀-trans c≤d d≤e)
     
     -- ≤₁₂-asym : ∀ {d e} → (e ≤₁₂ d) → (d ≤₁₂ e) → (d ≡ e)
     -- ≤₁₂-asym ≤₁₂-refl d≤e = refl
     -- ≤₁₂-asym c≤d ≤₁₂-refl = refl
     -- ≤₁₂-asym (≤₀-in-≤₁₂ c∉I c≤d) (≤₀-in-≤₁₂ _ d≤e) = ≤₀-asym c≤d d≤e
     
     -- I₁₂-max : ∀ {d e} → (d ≤₁₂ e) → (d ∈ I₁₂) → (d ≡ e)
     -- I₁₂-max ≤₁₂-refl d∈I₁₂ = refl
     -- I₁₂-max (≤₀-in-≤₁₂ d∉I₁₂ d≤₀e) d∈I₁₂ = CONTRADICTION (d∉I₁₂ d∈I₁₂)

     -- P₁₂ : Pomset
     -- P₁₂ = record
     --         { E = E₁₂
     --         ; _≤_ = _≤₁₂_
     --         ; ℓ = ℓ₁₂
     --         ; dec-E = {!!}
     --         ; ≤-refl = ≤₁₂-refl 
     --         ; ≤-trans = ≤₁₂-trans
     --         ; ≤-asym = ≤₁₂-asym
     --         ; I-max = I₁₂-max
     --         }
          
     -- I₁₂⊆I₁∩I₂ : I₁₂ ⊆ (I₁ ∩ I₂)
     -- I₁₂⊆I₁∩I₂ e e∈I₁₂ with dec-X₁ e 
     -- I₁₂⊆I₁∩I₂ e (left e∈I₁∩I₂ _ , _) | _ = e∈I₁∩I₂
     -- I₁₂⊆I₁∩I₂ e (right _ e∈X₁∪X₂ , a∈I) | yes (_ , a∈X) = CONTRADICTION (a∈I a∈X)
     -- I₁₂⊆I₁∩I₂ e (right _ e∈X₁∪X₂ , _) | no e∉X₁ with E∪F∖E⊆F e (e∈X₁∪X₂ , e∉X₁)
     -- I₁₂⊆I₁∩I₂ e (right _ e∈X₁∪X₂ , a∈I) | no e∉X₁ | (_ , a∈X) = CONTRADICTION (a∈I a∈X)
     
     -- I₁₂⊆I₁ : I₁₂ ⊆ I₁
     -- I₁₂⊆I₁ e e∈I₁₂ = fst(I₁₂⊆I₁∩I₂ e e∈I₁₂)
     
     -- I₁₂⊆I₂ : I₁₂ ⊆ I₂
     -- I₁₂⊆I₂ e e∈I₁₂ = snd(I₁₂⊆I₁∩I₂ e e∈I₁₂)

     -- P₁₂∈⟦C₁∙C₂⟧ : P₁₂ ∈ ⟦ C₁ ∙ C₂ ⟧
     -- P₁₂∈⟦C₁∙C₂⟧ = record
     --                 { P₁ = P₁
     --                 ; P₂ = P₂
     --                 ; P₁∈𝒫₁ = P₁∈⟦C₁⟧
     --                 ; P₂∈𝒫₂ = P₂∈⟦C₂⟧
     --                 ; I₀⊆I₁ = I₁₂⊆I₁
     --                 ; I₀⊆I₂ = I₁₂⊆I₂
     --                 ; X₀⊆X₁∪X₂ = {!!}
     --                 ; X₁⊆X₀ = {!!}
     --                 ; X₂⊆X₀ = {!!}
     --                 ; int-pre₀⊨pre₁ = {!!}
     --                 ; int-post₁⊨pre₂ = {!!}
     --                 ; int-post₂⊨post₀ = {!!}
     --                 ; just = {!!}
     --                 ; just-I = {!!}
     --                 ; just-≤ = {!!}
     --                 ; ext-post′₁⊨pre₂ = {!!}
     --                 ; ext-pre₀⊨pre₁ = {!!}
     --                 ; ext-pre₀⊨pre′₂ = {!!}
     --                 ; ext-pre₀⊨pre₁∨pre′₂ = {!!}
     --                 ; ext-act₀=act₁ = {!!}
     --                 ; ext-act₀=act₂ = {!!}
     --                 ; ≤₁⊆≤₀ = {!!}
     --                 ; ≤₂⊆≤₀ = {!!}
     --                 ; coherence = {!!}
     --                 }
     
     P₀∈⟦⟨C₁∙C₂⟩∙C₃⟧ : P₀ ∈ ⟦ (C₁ ∙ C₂) ∙ C₃ ⟧
     P₀∈⟦⟨C₁∙C₂⟩∙C₃⟧ = {!!}
     -- P₀∈⟦⟨C₁∙C₂⟩∙C₃⟧ = record
     --                     { P₁ = P₁₂
     --                     ; P₂ = P₃
     --                     ; P₁∈𝒫₁ = P₁₂∈⟦C₁∙C₂⟧
     --                     ; P₂∈𝒫₂ = P₃∈⟦C₃⟧
     --                     ; I₀⊆I₁ = {!!}
     --                     ; I₀⊆I₂ = {!!}
     --                     ; X₀⊆X₁∪X₂ = {!!}
     --                     ; X₁⊆X₀ = {!!}
     --                     ; X₂⊆X₀ = {!!}
     --                     ; int-pre₀⊨pre₁ = {!!}
     --                     ; int-post₁⊨pre₂ = {!!}
     --                     ; int-post₂⊨post₀ = {!!}
     --                     ; just = {!!}
     --                     ; just-I = {!!}
     --                     ; just-≤ = {!!}
     --                     ; ext-post′₁⊨pre₂ = {!!}
     --                     ; ext-pre₀⊨pre₁ = {!!}
     --                     ; ext-pre₀⊨pre′₂ = {!!}
     --                     ; ext-pre₀⊨pre₁∨pre′₂ = {!!}
     --                     ; ext-act₀=act₁ = {!!}
     --                     ; ext-act₀=act₂ = {!!}
     --                     ; ≤₁⊆≤₀ = {!!}
     --                     ; ≤₂⊆≤₀ = {!!}
     --                     ; coherence = {!!}
     --                     }
     
  ⟦⟨C₁∙C₂⟩∙C₃⟧⊆⟦C₁∙⟨C₂∙C₃⟩⟧ = {!!}

  -- QED
