module data-model where

  record DataModel : Set₁ where
  
    field Value : Set
    field Register : Set
    field Expression : Set
    field Formula : Set
    field Address : Set

    field value : Value → Expression
    field register : Value → Expression
    
    field _⊨_ : Formula → Formula → Set

    field tt : Formula
    field _∨_ : Formula → Formula → Formula
    field _==_ : Expression → Expression → Formula

    field ⊨-refl : ∀ {ϕ} → (ϕ ⊨ ϕ)
    field ⊨-trans : ∀ {ϕ ψ χ} → (ϕ ⊨ ψ) → (ψ ⊨ χ) → (ϕ ⊨ χ)
    

