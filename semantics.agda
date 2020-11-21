open import prelude
open import data-model using ( DataModel )
import command
import pomset

module semantics (DM : DataModel) (Event : Set) where

  open DataModel DM
  open command(DM)
  open pomset(DM)(Event)

  record SKIP (P₀ : Pomset) : Set₁ where
  
   open Pomset P₀ using () renaming (E to E₀ ; τ to τ₀)
   field E₀⊆∅ :  (E₀ ⊆ ∅)
   field τ₀ϕ⊨ϕ : ∀ C ϕ → τ₀(C)(ϕ) ⊨ ϕ

  record _●_ (𝒫₁ 𝒫₂ : Pomset → Set₁) (P₀ : Pomset) : Set₁ where

   field P₁ : Pomset
   field P₂ : Pomset

   field P₁∈𝒫₁ : P₁ ∈ 𝒫₁
   field P₂∈𝒫₂ : P₂ ∈ 𝒫₂
   
   open Pomset P₀ using () renaming (E to E₀ ; act to act₀ ; pre to pre₀ ; _≤_ to _≤₀_ ; ↓RW to ↓RW₀ ; RE to RE₀ ; WE to WE₀ ; RE⊆E to RE₀⊆E₀ ; τ to τ₀)
   open Pomset P₁ using () renaming (E to E₁ ; act to act₁ ; pre to pre₁ ; _≤_ to _≤₁_ ; ↓RW to ↓RW₁ ; RE to RE₁ ; WE to WE₁ ; τ to τ₁)
   open Pomset P₂ using () renaming (E to E₂ ; act to act₂ ; pre to pre₂ ; _≤_ to _≤₂_ ; ↓RW to ↓RW₂ ; RE to RE₂ ; WE to WE₂ ; τ to τ₂)

   field E₀⊆E₁∪E₂ : (E₀ ⊆ (E₁ ∪ E₂))
   field E₁⊆E₀ : (E₁ ⊆ E₀)
   field E₂⊆E₀ : (E₂ ⊆ E₀)

   E₁∪E₂⊆E₀ : ((E₁ ∪ E₂) ⊆ E₀)
   E₁∪E₂⊆E₀ = ⊆-elim-∪ E₁⊆E₀ E₂⊆E₀
   
   field ≤₁⊆≤₀ : ∀ d e → (d ≤₁ e) → (d ≤₀ e)
   field ≤₂⊆≤₀ : ∀ d e → (d ≤₂ e) → (d ≤₀ e)
   field coherence :  ∀ d e → (d ∈ E₁) → (e ∈ E₂) → (Conflicts (act₁(d)) (act₂(e))) → (d ≤₀ e)

   lhs₀ : Event → Formula
   lhs₀ = pre₁

   rhs₀ : Event → Formula
   rhs₀(e) = τ₁(↓RW₀(e))(pre₂(e))
   
   field pre₀⊨lhs₀ : ∀ e → (e ∈ E₁) → (e ∉ E₂) → (pre₀(e) ⊨ lhs₀(e))
   field pre₀⊨rhs₀ : ∀ e → (e ∉ E₁) → (e ∈ E₂) → (pre₀(e) ⊨ rhs₀(e))
   field pre₀⊨lhs₀∨rhs₀ : ∀ e → (e ∈ E₁) → (e ∈ E₂) → (pre₀(e) ⊨ (lhs₀(e) ∨ rhs₀(e)))
   
   field act₀=act₁ : ∀ e → (e ∈ E₁) → (act₀(e) ≡ act₁(e))
   field act₀=act₂ : ∀ e → (e ∈ E₂) → (act₀(e) ≡ act₂(e))
   
   field τ₀ϕ⊨τ₁τ₂ϕ : ∀ C ϕ → τ₀(C)(ϕ) ⊨ τ₁(C)(τ₂(C)(ϕ))

   RE₀∩E₁⊆RE₁ : (RE₀ ∩ E₁) ⊆ RE₁
   RE₀∩E₁⊆RE₁ = ⊆-refl-∩⁻¹ act₀=act₁ E₁⊆E₀ Reads

   RE₀∩E₂⊆RE₂ : (RE₀ ∩ E₂) ⊆ RE₂
   RE₀∩E₂⊆RE₂ = ⊆-refl-∩⁻¹ act₀=act₂ E₂⊆E₀ Reads

   RE₁⊆RE₀ : RE₁ ⊆ RE₀
   RE₁⊆RE₀ = ⊆-resp-∩⁻¹ act₀=act₁ E₁⊆E₀ Reads

   RE₂⊆RE₀ : RE₂ ⊆ RE₀
   RE₂⊆RE₀ = ⊆-resp-∩⁻¹ act₀=act₂ E₂⊆E₀ Reads

   WE₀∩E₁⊆WE₁ : (WE₀ ∩ E₁) ⊆ WE₁
   WE₀∩E₁⊆WE₁ = ⊆-refl-∩⁻¹ act₀=act₁ E₁⊆E₀ Writes

   WE₀∩E₂⊆WE₂ : (WE₀ ∩ E₂) ⊆ WE₂
   WE₀∩E₂⊆WE₂ = ⊆-refl-∩⁻¹ act₀=act₂ E₂⊆E₀ Writes

   WE₁⊆WE₀ : WE₁ ⊆ WE₀
   WE₁⊆WE₀ = ⊆-resp-∩⁻¹ act₀=act₁ E₁⊆E₀ Writes

   WE₂⊆WE₀ : WE₂ ⊆ WE₀
   WE₂⊆WE₀ = ⊆-resp-∩⁻¹ act₀=act₂ E₂⊆E₀ Writes

  record IF (ψ : Formula) (𝒫₁ 𝒫₂ : Pomset → Set₁) (P₀ : Pomset) : Set₁ where

   field P₁ : Pomset
   field P₂ : Pomset
   field P₁∈𝒫₁ : P₁ ∈ 𝒫₁
   field P₂∈𝒫₂ : P₂ ∈ 𝒫₂
   
   open Pomset P₀ using () renaming (E to E₀ ; act to act₀ ; pre to pre₀ ; _≤_ to _≤₀_ ; τ to τ₀)
   open Pomset P₁ using () renaming (E to E₁ ; act to act₁ ; pre to pre₁ ; _≤_ to _≤₁_ ; τ to τ₁)
   open Pomset P₂ using () renaming (E to E₂ ; act to act₂ ; pre to pre₂ ; _≤_ to _≤₂_ ; τ to τ₂)

   field E₀⊆E₁∪E₂ : (E₀ ⊆ (E₁ ∪ E₂))
   field E₁⊆E₀ : (E₁ ⊆ E₀)
   field E₂⊆E₀ : (E₂ ⊆ E₀)

   field ≤₁⊆≤₀ : ∀ d e → (d ≤₁ e) → (d ≤₀ e)
   field ≤₂⊆≤₀ : ∀ d e → (d ≤₂ e) → (d ≤₀ e)

   lhs₀ = λ e → (ψ ∧ pre₁(e))
   rhs₀ = λ e → ((¬ ψ) ∧ pre₂(e))
   
   field pre₀⊨lhs₀ : ∀ e → (e ∈ E₁) → (e ∉ E₂) → (pre₀(e) ⊨ lhs₀(e))
   field pre₀⊨rhs₀ : ∀ e → (e ∉ E₁) → (e ∈ E₂) → (pre₀(e) ⊨ rhs₀(e))
   field pre₀⊨lhs₀∨rhs₀ : ∀ e → (e ∈ E₁) → (e ∈ E₂) → (pre₀(e) ⊨ (lhs₀(e) ∨ rhs₀(e)))
   
   field act₀=act₁ : ∀ e → (e ∈ E₁) → (act₀(e) ≡ act₁(e))
   field act₀=act₂ : ∀ e → (e ∈ E₂) → (act₀(e) ≡ act₂(e))
   
   field τ₀ϕ⊨τ₁ϕ : ∀ C ϕ → (ψ ∧ τ₀(C)(ϕ)) ⊨ τ₁(C)(ϕ)
   field τ₀ϕ⊨τ₂ϕ : ∀ C ϕ → ((¬ ψ) ∧ τ₀(C)(ϕ)) ⊨ τ₂(C)(ϕ)
   
  record LOAD (r : Register) (a : Address)  (P : Pomset) : Set₁ where

    open Pomset P

    field e : Event
    field v : Value

    field e∈E : e ∈ E
    field d=e : ∀ d → (d ∈ E) → (d ≡ e)
    field act=Rav : act(e) ≡ (R a v)
    field τϕ⊨ϕ[v/r] : ∀ ϕ C → (τ(C)(ϕ) ⊨ (ϕ [ v / r ]))
    field τϕ⊨ϕ[[a]/r] : ∀ ϕ C → (e ∉ C) → (τ(C)(ϕ) ⊨ (ϕ [[ a ]/ r ]))
    
  record STORE (a : Address) (M : Expression) (P : Pomset) : Set₁ where

    open Pomset P

    field e : Event
    field v : Value

    field e∈E : e ∈ E
    field d=e : ∀ d → (d ∈ E) → (d ≡ e)
    field act=Wav : act(e) ≡ (W a v)
    field pre⊨M=v : pre(e) ⊨ (M == value v)
    field τϕ⊨ϕ[v/[a]] : ∀ ϕ C → (τ(C)(ϕ) ⊨ (ϕ [ v /[ a ]]))
  
  record LET (r : Register) (M : Expression) (P : Pomset) : Set₁ where
    -- TODO

  record THREAD (𝒫 : Pomset → Set₁) (P₀ : Pomset) : Set₁ where

   field P₁ : Pomset
   field P₁∈𝒫 : P₁ ∈ 𝒫
   
   open Pomset P₀ using () renaming (E to E₀ ; act to act₀ ; pre to pre₀ ; _≤_ to _≤₀_ ; τ to τ₀)
   open Pomset P₁ using () renaming (E to E₁ ; act to act₁ ; pre to pre₁ ; _≤_ to _≤₁_ ; τ to τ₁)

   field E₁⊆E₀ : (E₁ ⊆ E₀)
   field E₀⊆E₁ : (E₀ ⊆ E₁)
   
   field ≤₁⊆≤₀ : ∀ d e → (d ≤₁ e) → (d ≤₀ e)
   
   field pre₀⊨pre₁ : ∀ e → (e ∈ E₁) → (pre₀(e) ⊨ pre₁(e))
   field act₀=act₁ : ∀ e → (e ∈ E₁) → (act₀(e) ≡ act₁(e))
   
   field τ₀ϕ⊨ϕ : ∀ C ϕ → (τ₀(C)(ϕ) ⊨ ϕ) 
   field τ₀ϕ⊨ff : ∀ C ϕ e → (e ∈ E₀) → (e ∉ C) → (τ₀(C)(ϕ) ⊨ ff) 

  record _|||_ (𝒫₁ 𝒫₂ : Pomset → Set₁) (P₀ : Pomset) : Set₁ where

   field P₁ : Pomset
   field P₂ : Pomset

   field P₁∈𝒫₁ : P₁ ∈ 𝒫₁
   field P₂∈𝒫₂ : P₂ ∈ 𝒫₂
   
   open Pomset P₀ using () renaming (E to E₀ ; act to act₀ ; pre to pre₀ ; _≤_ to _≤₀_ ; τ to τ₀)
   open Pomset P₁ using () renaming (E to E₁ ; act to act₁ ; pre to pre₁ ; _≤_ to _≤₁_ ; τ to τ₁)
   open Pomset P₂ using () renaming (E to E₂ ; act to act₂ ; pre to pre₂ ; _≤_ to _≤₂_ ; τ to τ₂)

   field E₀⊆E₁⊎E₂ : (E₀ ⊆ (E₁ ⊎ E₂))
   field E₁⊆E₀ : (E₁ ⊆ E₀)
   field E₂⊆E₀ : (E₂ ⊆ E₀)
   field E₁∩E₂⊆∅ : (E₁ ∩ E₂) ⊆ ∅ 
   
   field ≤₁⊆≤₀ : ∀ d e → (d ≤₁ e) → (d ≤₀ e)
   field ≤₂⊆≤₀ : ∀ d e → (d ≤₂ e) → (d ≤₀ e)
   
   field pre₀⊨pre₁ : ∀ e → (e ∈ E₁) → (pre₀(e) ⊨ pre₁(e))
   field pre₀⊨pre₂ : ∀ e → (e ∈ E₂) → (pre₀(e) ⊨ pre₂(e))
   
   field act₀=act₁ : ∀ e → (e ∈ E₁) → (act₀(e) ≡ act₁(e))
   field act₀=act₂ : ∀ e → (e ∈ E₂) → (act₀(e) ≡ act₂(e))
   
   field τ₀ϕ⊨τ₁ϕ : ∀ C ϕ → τ₀(C)(ϕ) ⊨ τ₁(C)(ϕ)
   field τ₀ϕ⊨τ₂ϕ : ∀ C ϕ → τ₀(C)(ϕ) ⊨ τ₂(C)(ϕ)

  ⟦_⟧ : Command → Pomset → Set₁
  ⟪_⟫ : ThreadGroup → Pomset → Set₁
  
  ⟦ skip ⟧ = SKIP
  ⟦ C₁ ∙ C₂ ⟧ = ⟦ C₁ ⟧ ● ⟦ C₂ ⟧
  ⟦ if ϕ then C₁ else C₂ ⟧ = IF ϕ ⟦ C₁ ⟧ ⟦ C₂ ⟧
  ⟦ r :=[ a ] ⟧ = LOAD r a
  ⟦ [ a ]:= M ⟧ = STORE a M
  ⟦ r := M ⟧ = LET r M
  ⟦ fork G join ⟧ = ⟪ G ⟫

  ⟪ nil ⟫ = SKIP
  ⟪ thread C ⟫ = THREAD ⟦ C ⟧
  ⟪ G₁ ∥ G₂ ⟫ = ⟪ G₁ ⟫ ||| ⟪ G₂ ⟫
  
