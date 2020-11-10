open import prelude
open import data-model using ( DataModel )
import command
import pomset
import semantics

module augmentation (DM : DataModel) (Event : Set) where

  open DataModel DM
  open command(DM)
  open pomset(DM)(Event)
  open semantics(DM)(Event)

  record _≲_ (P P′ : Pomset) : Set₁ where

    open Pomset P using (E ; act ; pre ; _≤_ ; τ ; RE ; WE ; ↓RW ; WE⊆↓RW ; RE⊆↓RW ; ≤⊆↓RW)
    open Pomset P′ using () renaming (E to E′ ; act to act′ ; pre to pre′ ; _≤_ to _≤′_; ≤-refl to ≤′-refl ; τ to τ′ ; RE to RE′ ; WE to WE′ ; ↓RW to ↓RW′ ; WE⊆↓RW to WE′⊆↓RW′ ; RE⊆↓RW to RE′⊆↓RW′ ; ≤⊆↓RW to ≤′⊆↓RW′)

    field E′⊆E : (E′ ⊆ E)
    field E⊆E′ : (E ⊆ E′)
    field act=act′ : ∀ e → (e ∈ E) → (act(e) ≡ act′(e))
    field pre′⊨pre : ∀ e → (e ∈ E) → (pre′(e) ⊨ pre(e))
    field ≤⊆≤′ : ∀ d e → (d ≤ e) → (d ≤′ e)
    field τ′⊨τ : ∀ C ϕ → (τ′(C)(ϕ) ⊨ τ(C)(ϕ))
    
    RE⊆RE′ : (RE ⊆ RE′)
    RE⊆RE′ e (e∈E , ae∈R) = (E⊆E′ e e∈E , ≡-subst Reads (act=act′ e e∈E) ae∈R)

    WE⊆WE′ : (WE ⊆ WE′)
    WE⊆WE′ e (e∈E , ae∈W) = (E⊆E′ e e∈E , ≡-subst Writes (act=act′ e e∈E) ae∈W)

    ↓RW⊆↓RW' : ∀ e → (e ∈ E) → (↓RW(e) ⊆ ↓RW′(e))
    ↓RW⊆↓RW' e e∈E d (WE⊆↓RW d∈WE) = WE′⊆↓RW′ (WE⊆WE′ d d∈WE)
    ↓RW⊆↓RW' e e∈E d (RE⊆↓RW e∈RE) = RE′⊆↓RW′ (RE⊆RE′ e e∈RE)
    ↓RW⊆↓RW' e e∈E d (≤⊆↓RW d≤e) = ≤′⊆↓RW′ (≤⊆≤′ d e d≤e)
    
  sem-resp-≲ : ∀ {P P′ C} → (P ≲ P′) → (P ∈ ⟦ C ⟧) → (P′ ∈ ⟦ C ⟧)

  sem-resp-≲ {P₀} {P′₀} {skip} P₀≲P′₀ P₀∈SKIP = P′₀∈SKIP  where

    open SKIP P₀∈SKIP using (E₀⊆∅ ; τ₀ϕ⊨ϕ)
    open _≲_ P₀≲P′₀ using () renaming (E′⊆E to E′₀⊆E₀ ; τ′⊨τ to τ′₀⊨τ₀)
      
    P′₀∈SKIP : P′₀ ∈ SKIP
    P′₀∈SKIP = record
                { E₀⊆∅ = λ e e∈E′₀ → E₀⊆∅ e (E′₀⊆E₀ e e∈E′₀)
                ; τ₀ϕ⊨ϕ = λ C ϕ → ⊨-trans (τ′₀⊨τ₀ C ϕ) (τ₀ϕ⊨ϕ C ϕ) }

  sem-resp-≲ {P₀} {P′₀} {C₁ ∙ C₂} P₀≲P′₀ P₀∈⟦C₁⟧●⟦C₂⟧ = P′₀∈⟦C₁⟧●⟦C₂⟧ where

    open _●_ P₀∈⟦C₁⟧●⟦C₂⟧
    open Pomset P₁ using () renaming (τ to τ₁ ; τ-resp-⊆ to τ₁-resp-⊆)
    open Pomset P₂ using () renaming (E to E₂ ; pre to pre₂)
    open Pomset P₀ using () renaming (↓RW to ↓RW₀)
    open Pomset P′₀ using () renaming (↓RW to ↓RW′₀)
    open _≲_ P₀≲P′₀ using () renaming (E′⊆E to E′₀⊆E₀ ; E⊆E′ to E₀⊆E′₀ ; act=act′ to act₀=act′₀ ; pre′⊨pre to pre′₀⊨pre₀ ; ≤⊆≤′ to ≤₀⊆≤′₀ ; τ′⊨τ to τ′₀⊨τ₀ ; ↓RW⊆↓RW' to ↓RW₀⊆↓RW'₀) 

    pre″₂ : Event → Formula
    pre″₂(e) = τ₁(↓RW′₀(e))(pre₂(e))
   
    pre′₂⊨pre″₂ : ∀ e → (e ∈ E₂) → (pre′₂(e) ⊨ pre″₂(e))
    pre′₂⊨pre″₂ e e∈E₂ = τ₁-resp-⊆ (↓RW₀(e)) (↓RW′₀(e)) (pre₂(e)) (↓RW₀⊆↓RW'₀ e (E₂⊆E₀ e e∈E₂))
    
    P′₀∈⟦C₁⟧●⟦C₂⟧ : P′₀ ∈ (⟦ C₁ ⟧ ● ⟦ C₂ ⟧)
    P′₀∈⟦C₁⟧●⟦C₂⟧ = record
                      { P₁ = P₁
                      ; P₂ = P₂
                      ; P₁∈𝒫₁ = P₁∈𝒫₁
                      ; P₂∈𝒫₂ = P₂∈𝒫₂
                      ; E₀⊆E₁∪E₂ = λ e e∈E′₀ → E₀⊆E₁∪E₂ e (E′₀⊆E₀ e e∈E′₀)
                      ; E₁⊆E₀ = λ e e∈E₁ → E₀⊆E′₀ e (E₁⊆E₀ e e∈E₁)
                      ; E₂⊆E₀ = λ e e∈E₂ → E₀⊆E′₀ e (E₂⊆E₀ e e∈E₂)
                      ; ≤₁⊆≤₀ = λ d e d≤₁e → ≤₀⊆≤′₀ d e (≤₁⊆≤₀ d e d≤₁e)
                      ; ≤₂⊆≤₀ = λ d e d≤₂e → ≤₀⊆≤′₀ d e (≤₂⊆≤₀ d e d≤₂e)
                      ; coherence = λ d e d∈E₁ e∈E₂ d#e → ≤₀⊆≤′₀ d e (coherence d e d∈E₁ e∈E₂ d#e)
                      ; pre₀⊨pre₁ = λ e e∈E₁ e∉E₂ → ⊨-trans (pre′₀⊨pre₀ e (E₁⊆E₀ e e∈E₁)) (pre₀⊨pre₁ e e∈E₁ e∉E₂)
                      ; pre₀⊨pre′₂ = λ e e∉E₁ e∈E₂ → ⊨-trans (pre′₀⊨pre₀ e (E₂⊆E₀ e e∈E₂)) (⊨-trans (pre₀⊨pre′₂ e e∉E₁ e∈E₂) (pre′₂⊨pre″₂ e  e∈E₂))
                      ; pre₀⊨pre₁∨pre′₂ = λ e e∈E₁ e∈E₂ → ⊨-trans (pre′₀⊨pre₀ e (E₂⊆E₀ e e∈E₂)) (⊨-trans (pre₀⊨pre₁∨pre′₂ e e∈E₁ e∈E₂) (⊨-resp-∨ ⊨-refl (pre′₂⊨pre″₂ e  e∈E₂)))
                      ; act₀=act₁ = λ e e∈E₁ → ≡-trans (≡-symm (act₀=act′₀ e (E₁⊆E₀ e e∈E₁))) (act₀=act₁ e e∈E₁)
                      ; act₀=act₂ =  λ e e∈E₂ → ≡-trans (≡-symm (act₀=act′₀ e (E₂⊆E₀ e e∈E₂))) (act₀=act₂ e e∈E₂)
                      ; τ₀ϕ⊨τ₁τ₂ϕ = λ C ϕ → ⊨-trans (τ′₀⊨τ₀ C ϕ) (τ₀ϕ⊨τ₁τ₂ϕ C ϕ)
                      }
    
  -- TODO
  sem-resp-≲ {P} {P′} {if ϕ then C} P≲P′ P∈ϕ▷⟦C⟧ = record {}
  sem-resp-≲ {P} {P′} {r :=[ a ]} P≲P′ P∈LOAD = record {}
  sem-resp-≲ {P} {P′} {[ x ]:= x₁} P≲P′ P∈STORE = record {}
  sem-resp-≲ {P} {P′} {r := M} P≲P′ P∈LET = record {}
