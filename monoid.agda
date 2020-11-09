
open import prelude
open import data-model using ( DataModel )
import command
import pomset
import semantics
import augmentation

module monoid (DM : DataModel) (Event : Set) where

  open DataModel DM
  open command(DM)
  open pomset(DM)(Event)
  open semantics(DM)(Event)
  open augmentation(DM)(Event)

  -- PROPOSITION: sequential composition forms a monoid
  
  ⟦C⟧⊆⟦C∙skip⟧ : ∀ C → ⟦ C ⟧ ⊆ ⟦ C ∙ skip ⟧
  ⟦C∙skip⟧⊆⟦C⟧ : ∀ C → ⟦ C ∙ skip ⟧ ⊆ ⟦ C ⟧

  ⟦C⟧⊆⟦skip∙C⟧ : ∀ C → ⟦ C ⟧ ⊆ ⟦ skip ∙ C ⟧
  ⟦skip∙C⟧⊆⟦C⟧ : ∀ C → ⟦ skip ∙ C ⟧ ⊆ ⟦ C ⟧

  ⟦C₁∙⟨C₂∙C₃⟩⟧⊆⟦⟨C₁∙C₂⟩∙C₃⟧ : ∀ C₁ C₂ C₃ → ⟦ C₁ ∙ (C₂ ∙ C₃) ⟧ ⊆ ⟦ (C₁ ∙ C₂) ∙ C₃ ⟧
  ⟦⟨C₁∙C₂⟩∙C₃⟧⊆⟦C₁∙⟨C₂∙C₃⟩⟧ : ∀ C₁ C₂ C₃ → ⟦ (C₁ ∙ C₂) ∙ C₃ ⟧ ⊆ ⟦ C₁ ∙ (C₂ ∙ C₃) ⟧

  -- PROOF that skip is a right unit
  
  ⟦C⟧⊆⟦C∙skip⟧ C P₀ P₀∈⟦C⟧ = P₀∈⟦C∙skip⟧ where

    -- open Pomset P₀ using () renaming (E to E₀ ; I to I₀ ; dec-I to dec-I₀ ; E⊆I⊎X to E₀⊆I₀⊎X₀ ; I∩X⊆∅ to I₀∩X₀⊆∅ ; post to post₀ ; ≤-refl to ≤₀-refl)

    -- P₁ = P₀
    -- P₂ = record
    --        { E = I₀
    --        ; _≤_ = _≡_
    --        ; ℓ = λ e → (post₀(e) , ✓(post₀(e)))
    --        ; dec-E = dec-I₀
    --        ; ≤-refl = refl
    --        ; ≤-trans = ≡-trans
    --        ; ≤-asym = λ _ d=e → d=e
    --        ; I-max = λ d=e _ → d=e
    --        }

    -- open Pomset P₁ using () renaming (E to E₁ ; I to I₁ ; X⊆E to X₁⊆E₁)
    -- open Pomset P₂ using () renaming (E to E₂ ; I to I₂ ; I⊆E to I₂⊆E₂)

    -- P₂∈⟦skip⟧ : P₂ ∈ ⟦ skip ⟧ 
    -- P₂∈⟦skip⟧ = record
    --               { E₀⊆I₀ = λ e e∈I₀ → (e∈I₀ , λ ())
    --               ; pre₀⊨post₀ = λ e e∈E₂ → ⊨-refl
    --               }

    -- E₀⊆E₁∪E₂ : E₀ ⊆ (E₁ ∪ E₂)
    -- E₀⊆E₁∪E₂ e e∈E₀ with E₀⊆I₀⊎X₀ e e∈E₀
    -- E₀⊆E₁∪E₂ e e∈E₀ | left e∈I₀ e∉X₀ = both e∈E₀ e∈I₀
    -- E₀⊆E₁∪E₂ e e∈E₀ | right e∉I₀ e∈X₀ = left e∈E₀ e∉I₀

    P₀∈⟦C∙skip⟧ : P₀ ∈ ⟦ C ∙ skip ⟧
    P₀∈⟦C∙skip⟧ = ?
    -- P₀∈⟦C∙skip⟧ = record
    --                 { P₁ = P₁
    --                 ; P₂ = P₂
    --                 ; P₁∈𝒫₁ = P₀∈⟦C⟧
    --                 ; P₂∈𝒫₂ = P₂∈⟦skip⟧
    --                 ; I₀⊆I₁ = λ e e∈I₀ → e∈I₀
    --                 ; I₀⊆I₂ = λ e e∈I₀ → (e∈I₀ , λ ())
    --                 ; X₀⊆X₁∪X₂ = λ e e∈X₀ → left e∈X₀ (λ ())
    --                 ; X₁⊆X₀ = λ e e∈X₁ → e∈X₁
    --                 ; X₂⊆X₀ = λ e ()
    --                 ; int-pre₀⊨pre₁ = λ e e∈I₀ → ⊨-refl
    --                 ; int-post₁⊨pre₂ = λ e e∈I₀ → ⊨-refl
    --                 ; int-post₂⊨post₀ = λ e e∈I₀ → ⊨-refl
    --                 ; just = λ e → e
    --                 ; just-I = λ e ()
    --                 ; just-≤ = λ d e d∈RE₁ ()
    --                 ; ext-post′₁⊨pre₂ = λ e ()
    --                 ; ext-pre₀⊨pre₁ = λ e e∈X₁ e∉X₂ → ⊨-refl
    --                 ; ext-pre₀⊨pre′₂ = λ e e∉E₁ ()
    --                 ; ext-pre₀⊨pre₁∨pre′₂ = λ e e∩X₁ ()
    --                 ; ext-act₀=act₁ = λ e e∈X₁ → refl
    --                 ; ext-act₀=act₂ = λ e ()
    --                 ; ≤₁⊆≤₀ = λ d e d∈E₁ e∈E₁ d≤₁e → d≤₁e
    --                 ; ≤₂⊆≤₀ = λ{ d .d d∈E₁ e∈E₁ refl → ≤₀-refl }
    --                 ; coherence =  λ d e d∈X₁ ()
    --                 }

  ⟦C∙skip⟧⊆⟦C⟧ C P₀ P₀∈⟦C∙skip⟧ = P₀∈⟦C⟧ where

    -- open _●_ P₀∈⟦C∙skip⟧ using (P₁ ; P₂ ; E₀⊆E₁∪E₂ ; I₀⊆I₁ ; I₀⊆I₂ ; X₁⊆X₀ ; X₂⊆X₀ ; X₀⊆X₁∪X₂ ; ext-act₀=act₁ ; int-pre₀⊨pre₁ ; int-post₁⊨pre₂ ; int-post₂⊨post₀ ; ext-pre₀⊨pre₁ ; ≤₁⊆≤₀) renaming (P₁∈𝒫₁ to P₁∈⟦C⟧ ; P₂∈𝒫₂ to P₂∈⟦skip⟧)
    -- open SKIP P₂∈⟦skip⟧ using () renaming (X₀⊆∅ to X₂⊆∅ ; pre₀⊨post₀ to pre₂⊨post₂)
    -- open Pomset P₀ using () renaming (E to E₀ ; X to X₀ ; E⊆I⊎X to E₀⊆I₀⊎X₀ ; I∩X⊆∅ to I₀∩X₀⊆∅ ; pre to pre₀)
    -- open Pomset P₁ using () renaming (E to E₁ ; X to X₁ ; I⊆E to I₁⊆E₁ ; X⊆E to X₁⊆E₁ ; pre to pre₁)
    -- open Pomset P₂ using () renaming (E to E₂ ; X to X₂ ; I⊆E to I₂⊆E₂)

    -- X₀⊆X₁ : (X₀ ⊆ X₁)
    -- X₀⊆X₁ e e∈X₀ with X₀⊆X₁∪X₂ e e∈X₀
    -- X₀⊆X₁ e e∈X₀ | left e∈X₁ _ = e∈X₁
    -- X₀⊆X₁ e e∈X₀ | right _ e∈X₂ = CONTRADICTION (X₂⊆∅ e e∈X₂)
    -- X₀⊆X₁ e e∈X₀ | both _ e∈X₂ = CONTRADICTION (X₂⊆∅ e e∈X₂)

    -- E₀⊆E₁ : (E₀ ⊆ E₁)
    -- E₀⊆E₁ e e∈E₀ with E₀⊆I₀⊎X₀ e e∈E₀
    -- E₀⊆E₁ e e∈E₀ | left e∈I₀  _ = I₁⊆E₁ e (I₀⊆I₁ e e∈I₀)
    -- E₀⊆E₁ e e∈E₀ | right _ e∈X₀ = X₁⊆E₁ e (X₀⊆X₁ e e∈X₀)

    -- pre₀⊨pre₁ : ∀ e → (e ∈ E₀) → (pre₀(e)  ⊨ pre₁(e))
    -- pre₀⊨pre₁ e e∈E₀ with E₀⊆I₀⊎X₀ e e∈E₀
    -- pre₀⊨pre₁ e e∈E₀ | left e∈I₀ _ = int-pre₀⊨pre₁ e e∈I₀
    -- pre₀⊨pre₁ e e∈E₀ | right _ e∈X₀ = ext-pre₀⊨pre₁ e (X₀⊆X₁ e e∈X₀) (X₂⊆∅ e)
    
    -- P₁≲P₀ : P₁ ≲ P₀
    -- P₁≲P₀ = record
    --           { E′⊆E = E₀⊆E₁
    --           ; X⊆X′ = λ e e∈X₁ → X₁⊆X₀ e e∈X₁
    --           ; act=act′ = λ e e∈X₀ → ≡-symm (ext-act₀=act₁ e (X₀⊆X₁ e e∈X₀))
    --           ; pre′⊨pre = pre₀⊨pre₁
    --           ; post⊨post′ = λ e e∈I₀ → ⊨-trans (int-post₁⊨pre₂ e e∈I₀) (⊨-trans (pre₂⊨post₂ e (I₂⊆E₂ e (I₀⊆I₂ e e∈I₀))) (int-post₂⊨post₀ e e∈I₀))
    --           ; ≤⊆≤′ = λ d e d∈E₀ e∈E₀ d≤₁e → ≤₁⊆≤₀ d e (d∈E₀ , (E₀⊆E₁ d d∈E₀)) (e∈E₀ , (E₀⊆E₁ e e∈E₀)) d≤₁e
    --           }
    
    P₀∈⟦C⟧ = sem-resp-≲ ? ?

  -- PROOF that skip is a left unit

  ⟦C⟧⊆⟦skip∙C⟧ C P₀ P₀∈⟦C⟧ = P₀∈⟦skip∙C⟧ where

    -- open Pomset P₀ using () renaming (E to E₀ ; I to I₀ ; dec-E to dec-E₀ ; I⊆E to I₀⊆E₀ ; E⊆I⊎X to E₀⊆I₀⊎X₀ ; I∩X⊆∅ to I₀∩X₀⊆∅ ; pre to pre₀ ; ≤-refl to ≤₀-refl)

    -- P₁ = record
    --        { E = E₀
    --        ; _≤_ = _≡_
    --        ; ℓ = λ e → (pre₀(e) , ✓(pre₀(e)))
    --        ; dec-E = dec-E₀
    --        ; ≤-refl = refl
    --        ; ≤-trans = ≡-trans
    --        ; ≤-asym = λ _ d=e → d=e
    --        ; I-max = λ d=e _ → d=e
    --        }
    -- P₂ = P₀

    -- open Pomset P₁ using () renaming (E to E₁ ; I to I₁ ; I⊆E to I₁⊆E₁)
    -- open Pomset P₂ using () renaming (E to E₂ ; I to I₂ ; I⊆E to I₂⊆E₂ ; X⊆E to X₂⊆E₂ ; pre to pre₂)

    -- P₁∈⟦skip⟧ : P₁ ∈ ⟦ skip ⟧ 
    -- P₁∈⟦skip⟧ = record
    --               { E₀⊆I₀ = λ e e∈I₀ → (e∈I₀ , λ ())
    --               ; pre₀⊨post₀ = λ e e∈E₂ → ⊨-refl
    --               }

    P₀∈⟦skip∙C⟧ : P₀ ∈ ⟦ skip ∙ C ⟧
    P₀∈⟦skip∙C⟧ = ?
    -- P₀∈⟦skip∙C⟧ = record
    --                 { P₁ = P₁
    --                 ; P₂ = P₂
    --                 ; P₁∈𝒫₁ = P₁∈⟦skip⟧
    --                 ; P₂∈𝒫₂ = P₀∈⟦C⟧
    --                 ; I₀⊆I₁ = λ e e∈I₀ → (I₀⊆E₀ e e∈I₀ , λ ())
    --                 ; I₀⊆I₂ = λ e e∈I₀ → e∈I₀
    --                 ; X₀⊆X₁∪X₂ = λ e e∈X₀ → right (λ ()) e∈X₀
    --                 ; X₁⊆X₀ = λ e ()
    --                 ; X₂⊆X₀ = λ e e∈X₂ → e∈X₂
    --                 ; int-pre₀⊨pre₁ = λ e e∈I₀ → ⊨-refl
    --                 ; int-post₁⊨pre₂ = λ e e∈I₀ → ⊨-refl
    --                 ; int-post₂⊨post₀ = λ e e∈I₀ → ⊨-refl
    --                 ; just = λ e → e
    --                 ; just-I = λ e e∈X₂ → (X₂⊆E₂ e e∈X₂ , λ ())
    --                 ; just-≤ = λ d e ()
    --                 ; ext-post′₁⊨pre₂ = λ e e∈X₂ → ⊨-refl
    --                 ; ext-pre₀⊨pre₁ = λ e ()
    --                 ; ext-pre₀⊨pre′₂ = λ e e∉E₁ e∈X₂ → ⊨-refl
    --                 ; ext-pre₀⊨pre₁∨pre′₂ = λ e ()
    --                 ; ext-act₀=act₁ = λ e ()
    --                 ; ext-act₀=act₂ = λ e e∈X₁ → refl
    --                 ; ≤₁⊆≤₀ = λ{ d .d d∈E₁ e∈E₁ refl → ≤₀-refl }
    --                 ; ≤₂⊆≤₀ =  λ d e d∈E₁ e∈E₁ d≤₁e → d≤₁e
    --                 ; coherence =  λ d e ()
    --                 }
  
  ⟦skip∙C⟧⊆⟦C⟧ C P₀ P₀∈⟦skip∙C⟧ = P₀∈⟦C⟧ where

    -- open _●_ P₀∈⟦skip∙C⟧ using (P₁ ; P₂ ; E₀⊆E₁∪E₂ ; I₀⊆I₁ ; I₀⊆I₂ ; X₁⊆X₀ ; X₂⊆X₀ ; X₀⊆X₁∪X₂ ; just ; just-I ; ext-act₀=act₂ ; int-pre₀⊨pre₁ ; int-post₁⊨pre₂ ; int-post₂⊨post₀ ; ext-post′₁⊨pre₂ ; ext-pre₀⊨pre′₂ ; ≤₂⊆≤₀) renaming (P₁∈𝒫₁ to P₁∈⟦skip⟧ ; P₂∈𝒫₂ to P₂∈⟦C⟧)
    -- open SKIP P₁∈⟦skip⟧ using () renaming (X₀⊆∅ to X₁⊆∅ ; pre₀⊨post₀ to pre₁⊨post₁)
    -- open Pomset P₀ using () renaming (E to E₀ ; X to X₀ ; E⊆I⊎X to E₀⊆I₀⊎X₀ ; I∩X⊆∅ to I₀∩X₀⊆∅ ; pre to pre₀)
    -- open Pomset P₁ using () renaming (E to E₁ ; X to X₁ ; I⊆E to I₁⊆E₁ ; X⊆E to X₁⊆E₁ ; pre to pre₁)
    -- open Pomset P₂ using () renaming (E to E₂ ; X to X₂ ; I⊆E to I₂⊆E₂ ; X⊆E to X₂⊆E₂ ; pre to pre₂)

    -- X₀⊆X₂ : (X₀ ⊆ X₂)
    -- X₀⊆X₂ e e∈X₀ with X₀⊆X₁∪X₂ e e∈X₀
    -- X₀⊆X₂ e e∈X₀ | left e∈X₁ _ = CONTRADICTION (X₁⊆∅ e e∈X₁)
    -- X₀⊆X₂ e e∈X₀ | right _ e∈X₂ = e∈X₂
    -- X₀⊆X₂ e e∈X₀ | both e∈X₁ _ = CONTRADICTION (X₁⊆∅ e e∈X₁)

    -- E₀⊆E₂ : (E₀ ⊆ E₂)
    -- E₀⊆E₂ e e∈E₀ with E₀⊆I₀⊎X₀ e e∈E₀
    -- E₀⊆E₂ e e∈E₀ | left e∈I₀  _ = I₂⊆E₂ e (I₀⊆I₂ e e∈I₀)
    -- E₀⊆E₂ e e∈E₀ | right _ e∈X₀ = X₂⊆E₂ e (X₀⊆X₂ e e∈X₀)

    -- pre₀⊨pre₂ : ∀ e → (e ∈ E₀) → (pre₀(e)  ⊨ pre₂(e))
    -- pre₀⊨pre₂ e e∈E₀ with E₀⊆I₀⊎X₀ e e∈E₀
    -- pre₀⊨pre₂ e e∈E₀ | left e∈I₀ _ = ⊨-trans (int-pre₀⊨pre₁ e e∈I₀) (⊨-trans (pre₁⊨post₁ e (I₁⊆E₁ e (I₀⊆I₁ e e∈I₀))) (int-post₁⊨pre₂ e e∈I₀))
    -- pre₀⊨pre₂ e e∈E₀ | right _ e∈X₀ = ⊨-trans (ext-pre₀⊨pre′₂ e (X₁⊆∅ e) (X₀⊆X₂ e e∈X₀)) (⊨-trans (pre₁⊨post₁ (just e) (I₁⊆E₁ (just e) (just-I e (X₀⊆X₂ e e∈X₀)))) (ext-post′₁⊨pre₂ e (X₀⊆X₂ e e∈X₀)))
    
    -- P₂≲P₀ : P₂ ≲ P₀
    -- P₂≲P₀ = record
    --           { E′⊆E = E₀⊆E₂
    --           ; X⊆X′ = λ e e∈X₂ → X₂⊆X₀ e e∈X₂
    --           ; act=act′ = λ e e∈X₀ → ≡-symm (ext-act₀=act₂ e (X₀⊆X₂ e e∈X₀))
    --           ; pre′⊨pre = pre₀⊨pre₂
    --           ; post⊨post′ = int-post₂⊨post₀
    --           ; ≤⊆≤′ = λ d e d∈E₀ e∈E₀ d≤₂e → ≤₂⊆≤₀ d e (d∈E₀ , E₀⊆E₂ d d∈E₀) (e∈E₀ , E₀⊆E₂ e e∈E₀) d≤₂e
    --           }
    
    P₀∈⟦C⟧ = sem-resp-≲ ? ?
  
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
     P₀∈⟦⟨C₁∙C₂⟩∙C₃⟧ = ?
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
