open import prelude
open import data-model using ( DataModel )
import command
import pomset

module semantics (DM : DataModel) (Event : Set) where

  open DataModel DM
  open command(DM)
  open pomset(DM)(Event)

  record SKIP (P₀ : Pomset) : Set₁ where
  
   open Pomset P₀ using () renaming (E to E₀ ; I to I₀ ; X to X₀ ; pre to pre₀ ; post to post₀)
   field E₀⊆I₀ :  (E₀ ⊆ I₀)
   field pre₀⊨post₀ : (∀ e → (e ∈ E₀) → (pre₀(e) ⊨ post₀(e)))

  record _●_ (𝒫₁ 𝒫₂ : Pomset → Set₁) (P₀ : Pomset) : Set₁ where

   field P₁ : Pomset
   field P₂ : Pomset

   field P₁∈𝒫₁ : P₁ ∈ 𝒫₁
   field P₂∈𝒫₂ : P₂ ∈ 𝒫₂
   
   open Pomset P₀ using () renaming (E to E₀ ; I to I₀ ; X to X₀ ; act to act₀ ; pre to pre₀ ; post to post₀ ; _≤_ to _≤₀_ ; ↓ to ↓₀)
   open Pomset P₁ using () renaming (E to E₁ ; I to I₁ ; X to X₁ ; act to act₁ ; pre to pre₁ ; post to post₁ ; _≤_ to _≤₁_ ; _▷_ to _▷₁_)
   open Pomset P₂ using () renaming (E to E₂ ; I to I₂ ; X to X₂ ; act to act₂ ; pre to pre₂ ; post to post₂ ; _≤_ to _≤₂_)

   field E₀⊆E₁∪E₂ : E₀ ⊆ (E₁ ∪ E₂)
   field X₁∪X₂⊆X₀ : ((X₁ ∪ X₂) ⊆ X₀)

   field int-pre₀⊨pre₁ : ∀ e → (e ∈ I₀) → (pre₀(e) ⊨ pre₁(e))
   field int-post₁⊨pre₂ : ∀ e → (e ∈ I₀) → (post₁(e) ⊨ pre₂(e))
   field int-post₂⊨post₀ : ∀ e → (e ∈ I₀) → (post₂(e) ⊨ post₀(e))

   field pre′₂ : Event → Formula
   field pre′₂✓ : ∀ e → (e ∈ X₂) → (↓₀(e) ▷₁ (pre′₂(e) , pre₂(e)))

   field ext-pre₀⊨pre₁ : ∀ e → (e ∈ X₁) → (e ∉ E₂) → (pre₀(e) ⊨ pre₁(e))
   field ext-pre₀⊨pre′₂ : ∀ e → (e ∉ E₁) → (e ∈ X₂) → (pre₀(e) ⊨ pre′₂(e))
   field ext-pre₀⊨pre₁∨pre′₂ : ∀ e → (e ∈ X₁) → (e ∈ X₂) → (pre₀(e) ⊨ (pre₁(e) ∨ pre′₂(e)))
   
   field ext-act₀=act₁ : ∀ e → (e ∈ X₁) → (act₀(e) ≡ act₁(e))
   field ext-act₀=act₂ : ∀ e → (e ∈ X₂) → (act₀(e) ≡ act₂(e))

   field ≤₁⊆≤₀ : ∀ d e → (d ∈ E₀) → (e ∈ E₀) → (d ≤₁ e) → (d ≤₀ e)
   field ≤₂⊆≤₀ : ∀ d e → (d ∈ E₀) → (e ∈ E₀) → (d ≤₂ e) → (d ≤₀ e)
   field coherence :  ∀ d e → (d ∈ E₁) → (e ∈ E₂) → ((act₁(e) , act₂(e)) ∈ Conflicts) → (d ≤₀ e)
   
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
