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
    field ff : Formula
    field _∨_ : Formula → Formula → Formula
    field _==_ : Expression → Expression → Formula

    field ⊨-refl : ∀ {ϕ} → (ϕ ⊨ ϕ)
    field ⊨-trans : ∀ {ϕ ψ χ} → (ϕ ⊨ ψ) → (ψ ⊨ χ) → (ϕ ⊨ χ)
    field ⊨-resp-∨ : ∀ {ϕ ψ ξ ζ} → (ϕ ⊨ ψ) → (ξ ⊨ ζ) → ((ϕ ∨ ξ) ⊨ (ψ ∨ ζ))
    field ⊨-left-∨ : ∀ {ϕ ψ} → (ϕ ⊨ (ϕ ∨ ψ))
    field ⊨-right-∨ : ∀ {ϕ ψ} → (ψ ⊨ (ϕ ∨ ψ))
    field ⊨-elim-∨ : ∀ {ϕ ψ χ} → (ϕ ⊨ χ) → (ψ ⊨ χ) → ((ϕ ∨ ψ) ⊨ χ)
    
    ⊨-assocl-∨ : ∀ {ϕ ψ χ} → ((ϕ ∨ (ψ ∨ χ)) ⊨ ((ϕ ∨ ψ) ∨ χ))
    ⊨-assocl-∨ = ⊨-elim-∨ (⊨-trans ⊨-left-∨ ⊨-left-∨) (⊨-elim-∨ (⊨-trans ⊨-right-∨ ⊨-left-∨) ⊨-right-∨)

    ⊨-assocr-∨ : ∀ {ϕ ψ χ} → (((ϕ ∨ ψ) ∨ χ) ⊨ (ϕ ∨ (ψ ∨ χ)))
    ⊨-assocr-∨ = ⊨-elim-∨ (⊨-elim-∨ ⊨-left-∨ (⊨-trans ⊨-left-∨ ⊨-right-∨)) (⊨-trans ⊨-right-∨ ⊨-right-∨)
