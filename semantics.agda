open import prelude
open import data-model using ( DataModel )
import command
import pomset

module semantics (DM : DataModel) (Event : Set) where

  open DataModel DM
  open command(DM)
  open pomset(DM)(Event)

  record SKIP (P₀ : Pomset) : Set₁ where
  
   open Pomset P₀ using () renaming (E to E₀ ; I to I₀ ; X to X₀ ; pre to pre₀ ; post to post₀ ; X⊆E to X₀⊆E₀ ; I∩X⊆∅ to I₀∩X₀⊆∅)
   field E₀⊆I₀ :  (E₀ ⊆ I₀)
   field pre₀⊨post₀ : (∀ e → (e ∈ E₀) → (pre₀(e) ⊨ post₀(e)))

   X₀⊆∅ : X₀ ⊆ ∅
   X₀⊆∅ e e∈X₀ = I₀∩X₀⊆∅ e ((E₀⊆I₀ e (X₀⊆E₀ e e∈X₀)) , e∈X₀)

  record _●_ (𝒫₁ 𝒫₂ : Pomset → Set₁) (P₀ : Pomset) : Set₁ where

   field P₁ : Pomset
   field P₂ : Pomset

   field P₁∈𝒫₁ : P₁ ∈ 𝒫₁
   field P₂∈𝒫₂ : P₂ ∈ 𝒫₂
   
   open Pomset P₀ using () renaming (E to E₀ ; I to I₀ ; X to X₀ ; X⊆E to X₀⊆E₀ ; E⊆I⊎X to E₀⊆I₀⊎X₀ ; I∩X⊆∅ to I₀∩X₀⊆∅ ; act to act₀ ; pre to pre₀ ; post to post₀ ; _≤_ to _≤₀_ ; ↓ to ↓₀)
   open Pomset P₁ using () renaming (E to E₁ ; I to I₁ ; X to X₁ ; RE to RE₁ ; X⊆E to X₁⊆E₁ ; E⊆I⊎X to E₁⊆I₁⊎X₁ ; I⊆E to I₁⊆E₁ ; I∩X⊆∅ to I₁∩X₁⊆∅ ; dec-E to dec-E₁ ; act to act₁ ; pre to pre₁ ; post to post₁ ; _≤_ to _≤₁_)
   open Pomset P₂ using () renaming (E to E₂ ; I to I₂ ; X to X₂ ; WE to WE₂ ; X⊆E to X₂⊆E₂ ; E⊆I⊎X to E₂⊆I₂⊎X₂ ; I⊆E to I₂⊆E₂ ; I∩X⊆∅ to I₂∩X₂⊆∅ ; dec-E to dec-E₂ ; act to act₂ ; pre to pre₂ ; post to post₂ ; _≤_ to _≤₂_)

   field I₀⊆I₁ : I₀ ⊆ I₁
   field I₀⊆I₂ : I₀ ⊆ I₂

   field X₀⊆X₁∪X₂ : (X₀ ⊆ (X₁ ∪ X₂))
   field X₁⊆X₀ : (X₁ ⊆ X₀)
   field X₂⊆X₀ : (X₂ ⊆ X₀)

   field int-pre₀⊨pre₁ : ∀ e → (e ∈ I₀) → (pre₀(e) ⊨ pre₁(e))
   field int-post₁⊨pre₂ : ∀ e → (e ∈ I₀) → (post₁(e) ⊨ pre₂(e))
   field int-post₂⊨post₀ : ∀ e → (e ∈ I₀) → (post₂(e) ⊨ post₀(e))

   field just : Event → Event
   field just-I : ∀ e → (e ∈ X₂) → (just(e) ∈ I₁)
   field just-≤ : ∀ d e → (d ∈ RE₁) → (e ∈ WE₂) → (d ≤₁ just(e)) → (d ≤₀ e)
   
   pre′₂ = λ e → pre₁(just(e))
   post′₁ = λ e → post₁(just(e))
   
   field ext-post′₁⊨pre₂ : ∀ e → (e ∈ X₂) → (post′₁(e) ⊨ pre₂(e))
   field ext-pre₀⊨pre₁ : ∀ e → (e ∈ X₁) → (e ∉ X₂) → (pre₀(e) ⊨ pre₁(e))
   field ext-pre₀⊨pre′₂ : ∀ e → (e ∉ X₁) → (e ∈ X₂) → (pre₀(e) ⊨ pre′₂(e))
   field ext-pre₀⊨pre₁∨pre′₂ : ∀ e → (e ∈ X₁) → (e ∈ X₂) → (pre₀(e) ⊨ (pre₁(e) ∨ pre′₂(e)))
   
   field ext-act₀=act₁ : ∀ e → (e ∈ X₁) → (act₀(e) ≡ act₁(e))
   field ext-act₀=act₂ : ∀ e → (e ∈ X₂) → (act₀(e) ≡ act₂(e))

   field ≤₁⊆≤₀ : ∀ d e → (d ∈ (E₀ ∩ E₁)) → (e ∈ (E₀ ∩ E₁)) → (d ≤₁ e) → (d ≤₀ e)
   field ≤₂⊆≤₀ : ∀ d e → (d ∈ (E₀ ∩ E₂)) → (e ∈ (E₀ ∩ E₂)) → (d ≤₂ e) → (d ≤₀ e)
   field coherence :  ∀ d e → (d ∈ X₁) → (e ∈ X₂) → ((act₁(e) , act₂(e)) ∈ Conflicts) → (d ≤₀ e)

   E₁⊆E₁∪E₂ : E₁ ⊆ (E₁ ∪ E₂)
   E₁⊆E₁∪E₂ e e∈E₁ with dec-E₂ e
   E₁⊆E₁∪E₂ e e∈E₁ | yes e∈E₂ = both e∈E₁ e∈E₂
   E₁⊆E₁∪E₂ e e∈E₁ | no e∉E₂ = left e∈E₁ e∉E₂

   E₂⊆E₁∪E₂ : E₂ ⊆ (E₁ ∪ E₂)
   E₂⊆E₁∪E₂ e e∈E₂ with dec-E₁ e
   E₂⊆E₁∪E₂ e e∈E₂ | yes e∈E₁ = both e∈E₁ e∈E₂
   E₂⊆E₁∪E₂ e e∈E₂ | no e∉E₁ = right e∉E₁ e∈E₂
   
   X₁∪X₂⊆E₁∪E₂ : (X₁ ∪ X₂) ⊆ (E₁ ∪ E₂)
   X₁∪X₂⊆E₁∪E₂ e (left e∈X₁ _) = E₁⊆E₁∪E₂ e (X₁⊆E₁ e e∈X₁)
   X₁∪X₂⊆E₁∪E₂ e (right _ e∈X₂) = E₂⊆E₁∪E₂ e (X₂⊆E₂ e e∈X₂)
   X₁∪X₂⊆E₁∪E₂ e (both e∈X₁ e∈X₂) = both (X₁⊆E₁ e e∈X₁) (X₂⊆E₂ e e∈X₂)
   
   E₀⊆E₁∪E₂ : (E₀ ⊆ (E₁ ∪ E₂))
   E₀⊆E₁∪E₂ e e∈E₀ with E₀⊆I₀⊎X₀ e e∈E₀ 
   E₀⊆E₁∪E₂ e e∈E₀ | left e∈I₀ _ = both (I₁⊆E₁ e (I₀⊆I₁ e e∈I₀)) (I₂⊆E₂ e (I₀⊆I₂ e e∈I₀))
   E₀⊆E₁∪E₂ e e∈E₀ | right _ e∈X₀ = X₁∪X₂⊆E₁∪E₂ e (X₀⊆X₁∪X₂ e e∈X₀)
   
   I₀∩X₁⊆∅ : (I₀ ∩ X₁) ⊆ ∅
   I₀∩X₁⊆∅ e (e∈I₀ , e∈X₁) = I₀∩X₀⊆∅ e (e∈I₀ , (X₁⊆X₀ e e∈X₁))
   
   I₀∩X₂⊆∅ : (I₀ ∩ X₂) ⊆ ∅
   I₀∩X₂⊆∅ e (e∈I₀ , e∈X₂) = I₀∩X₀⊆∅ e (e∈I₀ , (X₂⊆X₀ e e∈X₂))

  record _◁_ (ϕ : Formula) (𝒫₁ : Pomset → Set₁) (P : Pomset) : Set₁ where
    -- TODO
    
  record LOAD (r : Register) (a : Address)  (P : Pomset) : Set₁ where
    -- TODO

  record STORE (a : Address) (M : Expression) (P : Pomset) : Set₁ where
    -- TODO
  
  record LET (r : Register) (M : Expression) (P : Pomset) : Set₁ where
    -- TODO
  
  ⟦_⟧ : Command → Pomset → Set₁
  ⟦ skip ⟧ = SKIP
  ⟦ C₁ ∙ C₂ ⟧ = ⟦ C₁ ⟧ ● ⟦ C₂ ⟧
  ⟦ if ϕ then C ⟧ = ϕ ◁ ⟦ C ⟧
  ⟦ r :=[ a ] ⟧ = LOAD r a
  ⟦ [ a ]:= M ⟧ = STORE a M
  ⟦ r := M ⟧ = LET r M
