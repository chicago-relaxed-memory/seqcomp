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

    open Pomset P using (E ; act ; pre ; _≤_ ; τ ; RE ; WE ; ↓RW)
    open Pomset P′ using () renaming (E to E′ ; act to act′ ; pre to pre′ ; _≤_ to _≤′_; ≤-refl to ≤′-refl ; τ to τ′ ; RE to RE′ ; WE to WE′ ; ↓RW to ↓RW′)

    field E′⊆E : (E′ ⊆ E)
    field E⊆E′ : (E ⊆ E′)
    field act=act′ : ∀ e → (e ∈ E) → (act(e) ≡ act′(e))
    field pre′⊨pre : ∀ e → (e ∈ E) → (pre′(e) ⊨ pre(e))
    field ≤⊆≤′ : ∀ d e → (d ≤ e) → (d ≤′ e)
    field τ′⊨τ : ∀ C ϕ → (τ′(C)(ϕ) ⊨ τ(C)(ϕ))
    
    RE⊆RE′ : (RE ⊆ RE′)
    RE⊆RE′ e (e∈E , ae∈R) = (E⊆E′ e e∈E , ≡-subst Reads (act=act′ e e∈E) ae∈R)
    
    RE′⊆RE : (RE′ ⊆ RE)
    RE′⊆RE e (e∈E′ , ae∈R) = (E′⊆E e e∈E′ , ≡-subst Reads (≡-symm (act=act′ e (E′⊆E e e∈E′))) ae∈R)

    WE⊆WE′ : (WE ⊆ WE′)
    WE⊆WE′ e (e∈E , ae∈W) = (E⊆E′ e e∈E , ≡-subst Writes (act=act′ e e∈E) ae∈W)
    
    WE′⊆WE : (WE′ ⊆ WE)
    WE′⊆WE e (e∈E′ , ae∈W) = (E′⊆E e e∈E′ , ≡-subst Writes (≡-symm (act=act′ e (E′⊆E e e∈E′))) ae∈W)

    ↓RW⊆↓RW' : ∀ e → (e ∈ E) → (↓RW(e) ⊆ ↓RW′(e))
    ↓RW⊆↓RW' e e∈E d (d∈E , d∈↓RWe) = (E⊆E′ d d∈E , λ d∈RE′ e∈WE′ → ≤⊆≤′ d e (d∈↓RWe (RE′⊆RE d d∈RE′) (WE′⊆WE e e∈WE′)))
    
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

    rhs′₀ : Event → Formula
    rhs′₀(e) = τ₁(↓RW′₀(e))(pre₂(e))
   
    rhs₀⊨rhs′₀ : ∀ e → (e ∈ E₂) → (rhs₀(e) ⊨ rhs′₀(e))
    rhs₀⊨rhs′₀ e e∈E₂ = τ₁-resp-⊆ (↓RW₀⊆↓RW'₀ e (E₂⊆E₀ e e∈E₂))
    
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
                      ; pre₀⊨lhs₀ = λ e e∈E₁ e∉E₂ → ⊨-trans (pre′₀⊨pre₀ e (E₁⊆E₀ e e∈E₁)) (pre₀⊨lhs₀ e e∈E₁ e∉E₂)
                      ; pre₀⊨rhs₀ = λ e e∉E₁ e∈E₂ → ⊨-trans (pre′₀⊨pre₀ e (E₂⊆E₀ e e∈E₂)) (⊨-trans (pre₀⊨rhs₀ e e∉E₁ e∈E₂) (rhs₀⊨rhs′₀ e  e∈E₂))
                      ; pre₀⊨lhs₀∨rhs₀ = λ e e∈E₁ e∈E₂ → ⊨-trans (pre′₀⊨pre₀ e (E₂⊆E₀ e e∈E₂)) (⊨-trans (pre₀⊨lhs₀∨rhs₀ e e∈E₁ e∈E₂) (⊨-resp-∨ ⊨-refl (rhs₀⊨rhs′₀ e  e∈E₂)))
                      ; act₀=act₁ = λ e e∈E₁ → ≡-trans (≡-symm (act₀=act′₀ e (E₁⊆E₀ e e∈E₁))) (act₀=act₁ e e∈E₁)
                      ; act₀=act₂ =  λ e e∈E₂ → ≡-trans (≡-symm (act₀=act′₀ e (E₂⊆E₀ e e∈E₂))) (act₀=act₂ e e∈E₂)
                      ; τ₀ϕ⊨τ₁τ₂ϕ = λ C ϕ → ⊨-trans (τ′₀⊨τ₀ C ϕ) (τ₀ϕ⊨τ₁τ₂ϕ C ϕ)
                      }
    
  -- TODO
  sem-resp-≲ {P} {P′} {if ϕ then C} P≲P′ P∈ϕ▷⟦C⟧ = record {}
  sem-resp-≲ {P} {P′} {r :=[ a ]} P≲P′ P∈LOAD = record {}
  sem-resp-≲ {P} {P′} {[ x ]:= x₁} P≲P′ P∈STORE = record {}
  sem-resp-≲ {P} {P′} {r := M} P≲P′ P∈LET = record {}
