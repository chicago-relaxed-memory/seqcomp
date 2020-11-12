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
   
   open Pomset P₀ using () renaming (E to E₀ ; act to act₀ ; pre to pre₀ ; _≤_ to _≤₀_ ; ↓RW to ↓RW₀ ; RE to RE₀ ; WE to WE₀ ; τ to τ₀)
   open Pomset P₁ using () renaming (E to E₁ ; act to act₁ ; pre to pre₁ ; _≤_ to _≤₁_ ; ↓RW to ↓RW₁ ; RE to RE₁ ; WE to WE₁ ; τ to τ₁)
   open Pomset P₂ using () renaming (E to E₂ ; act to act₂ ; pre to pre₂ ; _≤_ to _≤₂_ ; ↓RW to ↓RW₂ ; RE to RE₂ ; WE to WE₂ ; τ to τ₂)

   field E₀⊆E₁∪E₂ : (E₀ ⊆ (E₁ ∪ E₂))
   field E₁⊆E₀ : (E₁ ⊆ E₀)
   field E₂⊆E₀ : (E₂ ⊆ E₀)

   E₁∪E₂⊆E₀ : ((E₁ ∪ E₂) ⊆ E₀)
   E₁∪E₂⊆E₀ = cond E₁⊆E₀ E₂⊆E₀
   
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

   E₀∖E₂⊆E₁ : (E₀ ∖ E₂) ⊆ E₁
   E₀∖E₂⊆E₁ e (e∈E₀ , e∉E₂) = E∪F∖F⊆E e (E₀⊆E₁∪E₂ e e∈E₀ , e∉E₂)

   E₀∖E₁⊆E₂ : (E₀ ∖ E₁) ⊆ E₂
   E₀∖E₁⊆E₂ e (e∈E₀ , e∉E₁) = E∪F∖E⊆F e (E₀⊆E₁∪E₂ e e∈E₀ , e∉E₁)

   RE₀∩E₁⊆RE₁ : (RE₀ ∩ E₁) ⊆ RE₁
   RE₀∩E₁⊆RE₁ e ((e∈E₀ , a∈R) , e∈E₁) = (e∈E₁ , ≡-subst Reads (act₀=act₁ e e∈E₁) a∈R)

   RE₀∩E₂⊆RE₂ : (RE₀ ∩ E₂) ⊆ RE₂
   RE₀∩E₂⊆RE₂ e ((e∈E₀ , a∈R) , e∈E₂) = (e∈E₂ , ≡-subst Reads (act₀=act₂ e e∈E₂) a∈R)

   RE₁⊆RE₀ : RE₁ ⊆ RE₀
   RE₁⊆RE₀ e (e∈E₁ , a∈R) = (E₁⊆E₀ e e∈E₁ , ≡-subst Reads (≡-symm (act₀=act₁ e e∈E₁)) a∈R)

   RE₂⊆RE₀ : RE₂ ⊆ RE₀
   RE₂⊆RE₀ e (e∈E₂ , a∈R) = (E₂⊆E₀ e e∈E₂ , ≡-subst Reads (≡-symm (act₀=act₂ e e∈E₂)) a∈R)

   WE₁⊆WE₀ : WE₁ ⊆ WE₀
   WE₁⊆WE₀ e (e∈E₁ , a∈W) = (E₁⊆E₀ e e∈E₁ , ≡-subst Writes (≡-symm (act₀=act₁ e e∈E₁)) a∈W)

   WE₂⊆WE₀ : WE₂ ⊆ WE₀
   WE₂⊆WE₀ e (e∈E₂ , a∈W) = (E₂⊆E₀ e e∈E₂ , ≡-subst Writes (≡-symm (act₀=act₂ e e∈E₂)) a∈W)

   WE₀∩E₁⊆WE₁ : (WE₀ ∩ E₁) ⊆ WE₁
   WE₀∩E₁⊆WE₁ e ((e∈E₀ , a∈W) , e∈E₁) = (e∈E₁ , ≡-subst Writes (act₀=act₁ e e∈E₁) a∈W)

   WE₀∩E₂⊆WE₂ : (WE₀ ∩ E₂) ⊆ WE₂
   WE₀∩E₂⊆WE₂ e ((e∈E₀ , a∈W) , e∈E₂) = (e∈E₂ , ≡-subst Writes (act₀=act₂ e e∈E₂) a∈W)

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
