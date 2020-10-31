open import prelude
open import data-model using ( DataModel )
import command
import pomset
import semantics
import augmentation

module properties (DM : DataModel) (Event : Set) where

  open DataModel DM
  open command(DM)
  open pomset(DM)(Event)
  open semantics(DM)(Event)
  open augmentation(DM)(Event)

  right-unit-sub : ∀ C → ⟦ C ⟧ ⊆ ⟦ C ∙ skip ⟧
  right-unit-sub C P₀ P₀∈⟦C⟧ = P₀∈⟦C∙skip⟧ where

    open Pomset P₀ using () renaming (E to E₀ ; I to I₀ ; E⊆I∪X to E₀⊆I₀∪X₀ ; I∩X⊆∅ to I₀∩X₀⊆∅ ; post to post₀ ; ≤-refl to ≤₀-refl)

    P₁ = P₀
    P₂ = record
           { E = I₀
           ; _≤_ = _≡_
           ; ℓ = λ e → (post₀(e) , ✓(post₀(e)))
           ; ≤-refl = refl
           ; ≤-trans = ≡-trans
           ; ≤-asym = λ _ d=e → d=e
           ; ✓-max = λ{ (d=e , d≠e ) → CONTRADICTION (d≠e d=e) }
           }

    open Pomset P₁ using () renaming (E to E₁ ; I to I₁; X⊆E to X₁⊆E₁)
    open Pomset P₂ using () renaming (E to E₂ ; I to I₂)

    P₂∈⟦skip⟧ = record
                  { E₀⊆I₀ = λ e e∈I₀ → (e∈I₀ , λ ())
                  ; pre₀⊨post₀ = λ e e∈E₂ → ⊨-refl
                  }

    E₀⊆E₁∪E₂ : E₀ ⊆ (E₁ ∪ E₂)
    E₀⊆E₁∪E₂ e e∈E₀ with E₀⊆I₀∪X₀ e e∈E₀
    E₀⊆E₁∪E₂ e e∈E₀ | left e∈I₀ _ = both e∈E₀ e∈I₀
    E₀⊆E₁∪E₂ e e∈E₀ | right _ e∈X₀ = left e∈E₀ (λ e∈I₀ → I₀∩X₀⊆∅ e (e∈I₀ , e∈X₀))
    E₀⊆E₁∪E₂ e e∈E₀ | both e∈I₀ e∈X₀ = CONTRADICTION (I₀∩X₀⊆∅ e (e∈I₀ , e∈X₀))

    P₀∈⟦C∙skip⟧ = record
                    { P₁ = P₁
                    ; P₂ = P₂
                    ; P₁∈𝒫₁ = P₀∈⟦C⟧
                    ; P₂∈𝒫₂ = P₂∈⟦skip⟧
                    ; E₀⊆E₁∪E₂ = E₀⊆E₁∪E₂
                    ; I₀⊆I₁∩I₂ = λ e e∈I₀ → (e∈I₀ , (e∈I₀ , λ ()))
                    ; X₀⊆X₁∪X₂ = λ e e∈X₀ → left e∈X₀ (λ ())
                    ; X₁⊆X₀ = λ e e∈X₁ → e∈X₁
                    ; X₂⊆X₀ = λ e ()
                    ; int-pre₀⊨pre₁ = λ e e∈I₀ → ⊨-refl
                    ; int-post₁⊨pre₂ = λ e e∈I₀ → ⊨-refl
                    ; int-post₂⊨post₀ = λ e e∈I₀ → ⊨-refl
                    ; pre′₂ = post₀
                    ; pre′₂✓ = λ e ()
                    ; ext-pre₀⊨pre₁ = λ e e∈X₁ e∉E₂ → ⊨-refl
                    ; ext-pre₀⊨pre′₂ = λ e e∉E₁ ()
                    ; ext-pre₀⊨pre₁∨pre′₂ = λ e e∩X₁ ()
                    ; ext-act₀=act₁ = λ e e∈X₁ → refl
                    ; ext-act₀=act₂ = λ e ()
                    ; ≤₁⊆≤₀ = λ d e d∈E₁ e∈E₁ d≤₁e → d≤₁e
                    ; ≤₂⊆≤₀ = λ{ d .d d∈E₁ e∈E₁ refl → ≤₀-refl }
                    ; coherence =  λ d e d∈X₁ ()
                    }

  right-unit-sup : ∀ C → ⟦ C ∙ skip ⟧ ⊆ ⟦ C ⟧
  right-unit-sup C P₀ P₀∈⟦C∙skip⟧ = P₀∈⟦C⟧ where

    open _●_ P₀∈⟦C∙skip⟧ using (P₁ ; P₂ ; E₀⊆E₁∪E₂ ; I₀⊆I₁ ; I₀⊆I₂ ; X₁⊆X₀ ; X₂⊆X₀ ; X₀⊆X₁∪X₂ ; ext-act₀=act₁ ; int-pre₀⊨pre₁ ; int-post₁⊨pre₂ ; int-post₂⊨post₀ ; ext-pre₀⊨pre₁) renaming (P₁∈𝒫₁ to P₁∈⟦C⟧ ; P₂∈𝒫₂ to P₂∈⟦skip⟧)
    open SKIP P₂∈⟦skip⟧ using () renaming (X₀⊆∅ to X₂⊆∅ ; pre₀⊨post₀ to pre₂⊨post₂)
    open Pomset P₀ using () renaming (E to E₀ ; X to X₀ ; E⊆I∪X to E₀⊆I₀∪X₀ ; I∩X⊆∅ to I₀∩X₀⊆∅ ; pre to pre₀)
    open Pomset P₁ using () renaming (E to E₁ ; X to X₁ ; I⊆E to I₁⊆E₁ ; X⊆E to X₁⊆E₁ ; pre to pre₁)
    open Pomset P₂ using () renaming (E to E₂ ; X to X₂ ; I⊆E to I₂⊆E₂)

    X₀⊆X₁ : (X₀ ⊆ X₁)
    X₀⊆X₁ e e∈X₀ with X₀⊆X₁∪X₂ e e∈X₀
    X₀⊆X₁ e e∈X₀ | left e∈X₁ _ = e∈X₁
    X₀⊆X₁ e e∈X₀ | right _ e∈X₂ = CONTRADICTION (X₂⊆∅ e e∈X₂)
    X₀⊆X₁ e e∈X₀ | both _ e∈X₂ = CONTRADICTION (X₂⊆∅ e e∈X₂)

    E₀⊆E₁ : (E₀ ⊆ E₁)
    E₀⊆E₁ e e∈E₀ with E₀⊆I₀∪X₀ e e∈E₀
    E₀⊆E₁ e e∈E₀ | left e∈I₀  _ = I₁⊆E₁ e (I₀⊆I₁ e e∈I₀)
    E₀⊆E₁ e e∈E₀ | right _ e∈X₀ = X₁⊆E₁ e (X₀⊆X₁ e e∈X₀)
    E₀⊆E₁ e e∈E₀ | both e∈I₀ e∈X₀ = CONTRADICTION  (I₀∩X₀⊆∅ e (e∈I₀ , e∈X₀))

    pre₀⊨pre₁ : ∀ e → (e ∈ E₀) → (pre₀(e)  ⊨ pre₁(e))
    pre₀⊨pre₁ e e∈E₀ with E₀⊆I₀∪X₀ e e∈E₀
    pre₀⊨pre₁ e e∈E₀ | left e∈I₀ _ = int-pre₀⊨pre₁ e e∈I₀
    pre₀⊨pre₁ e e∈E₀ | right _ e∈X₀ = ext-pre₀⊨pre₁ e (X₀⊆X₁ e e∈X₀) {!!}
    pre₀⊨pre₁ e e∈E₀ | both e∈I₀ e∈X₀ = CONTRADICTION  (I₀∩X₀⊆∅ e (e∈I₀ , e∈X₀))
    
    P₁≲P₀ : P₁ ≲ P₀
    P₁≲P₀ = record
              { F⊆E = E₀⊆E₁
              ; X⊆Y = λ e e∈X₁ → X₁⊆X₀ e e∈X₁
              ; act=bct = λ e e∈X₀ → ≡-symm (ext-act₀=act₁ e (X₀⊆X₁ e e∈X₀))
              ; qre⊨pre = λ e e∈E₀ → {!!}
              ; post⊨qost = λ e e∈I₀ → ⊨-trans (int-post₁⊨pre₂ e e∈I₀) (⊨-trans (pre₂⊨post₂ e (I₂⊆E₂ e (I₀⊆I₂ e e∈I₀))) (int-post₂⊨post₀ e e∈I₀))
              ; ≤⊆≼ = {!!}
              }
    
    P₀∈⟦C⟧ = sem-resp-≲ P₁≲P₀ P₁∈⟦C⟧
    
    -- open Pomset P₀ using () renaming (E to E₀ ; X to X₀ ; I to I₀ ; act to act₀ ; pre to pre₀ ; post to post₀ ; _≤_ to _≤₀_)
    -- open Pomset P₁ using () renaming (E to E₁ ; X to X₁ ; I to I₁ ; act to act₁ ; pre to pre₁ ; post to post₁ ; _≤_ to _≤₁_ ; I⊆E to I₁⊆E₁ ; X⊆E to X₁⊆E₁)
    -- open Pomset P₂ using () renaming (X⊆E to X₂⊆E₂ ; I∩X⊆∅ to I₂∩X₂⊆∅)

    -- E₀⊆E₁ : (E₀ ⊆ E₁)
    -- E₀⊆E₁ e e∈E₀ with hyp-ℓ e e∈E₀
    -- E₀⊆E₁ e e∈E₀ | cut _ e∈I₁ _ _ _ _ = I₁⊆E₁ e e∈I₁
    -- E₀⊆E₁ e e∈E₀ | left _ e∈X₁ _ _ _ = X₁⊆E₁ e e∈X₁
    -- E₀⊆E₁ e e∈E₀ | right _ _ e∈X₂ _ _ _ = CONTRADICTION (I₂∩X₂⊆∅ e (E₂⊆I₂ e (X₂⊆E₂ e e∈X₂) , e∈X₂))
    -- E₀⊆E₁ e e∈E₀ | both _ e∈X₁ _ _ _ _ _ = X₁⊆E₁ e e∈X₁

    -- X₁⊆X₀ : (X₁ ⊆ X₀)
    -- X₁⊆X₀ e e∈X₁ = X₁∪X₂⊆X₀ e (inl e∈X₁)

    -- act₁=act₀ : ∀ e → (e ∈ X₀) → (act₁ e ≡ act₀ e)
    -- act₁=act₀ = {!!}

    -- pre₀⊨pre₁ : ∀ e → (e ∈ E₀) → (pre₀ e ⊨ pre₁ e)
    -- pre₀⊨pre₁ = {!!}
    
    -- post₁⊨post₀ : ∀ e → (e ∈ I₀) → (post₁ e ⊨ post₀ e)
    -- post₁⊨post₀  = {!!}

    -- ≤₁⊆≤₀ : ∀ d e → (d ≤₁ e) → (d ≤₀ e)
    -- ≤₁⊆≤₀ = {!!}
    
    -- P₁≲P₀ : P₁ ≲ P₀
    -- P₁≲P₀ = record
    --           { F⊆E = E₀⊆E₁
    --           ; X⊆Y = X₁⊆X₀ 
    --           ; act=bct = act₁=act₀
    --           ; qre⊨pre = pre₀⊨pre₁
    --           ; post⊨qost = post₁⊨post₀
    --           ; ≤⊆≼ = ≤₁⊆≤₀ 
    --           }
    
