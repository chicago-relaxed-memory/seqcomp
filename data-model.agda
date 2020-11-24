open import prelude

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

    field ff : Formula
    field _∨_ : Formula → Formula → Formula
    field ¬ : Formula → Formula
    field _==_ : Expression → Expression → Formula
    
    field _[_/_] : Formula → Expression → Register → Formula
    field _[[_]/_] : Formula → Address → Register → Formula
    field _[_/[_]] : Formula → Expression → Address → Formula

    field ⊨-refl : ∀ {ϕ} → (ϕ ⊨ ϕ)
    field ⊨-trans : ∀ {ϕ ψ χ} → (ϕ ⊨ ψ) → (ψ ⊨ χ) → (ϕ ⊨ χ)
    field ⊨-resp-∨ : ∀ {ϕ ψ ξ ζ} → (ϕ ⊨ ψ) → (ξ ⊨ ζ) → ((ϕ ∨ ξ) ⊨ (ψ ∨ ζ))
    field ⊨-left-∨ : ∀ {ϕ ψ} → (ϕ ⊨ (ϕ ∨ ψ))
    field ⊨-right-∨ : ∀ {ϕ ψ} → (ψ ⊨ (ϕ ∨ ψ))
    field ⊨-elim-∨ : ∀ {ϕ ψ χ} → (ϕ ⊨ χ) → (ψ ⊨ χ) → ((ϕ ∨ ψ) ⊨ χ) 
    field ⊨-resp-¬ : ∀ {ϕ ψ} → (ϕ ⊨ ψ) → ((¬ ψ) ⊨ (¬ ϕ))
    field ⊨-elim-¬¬ : ∀ {ϕ} → (¬(¬ ϕ) ⊨ ϕ)
    field ⊨-intro-¬¬ : ∀ {ϕ} → (ϕ ⊨ ¬(¬ ϕ)) 
    field ⊨-elim-ff : ∀ {ϕ} → (ff ⊨ ϕ)
    
    tt = ¬ ff
    _∧_ = λ ϕ ψ → ¬((¬ ϕ) ∨ (¬ ψ))

    _⊭_ = λ ϕ ψ → (ϕ ⊨ ψ) → FALSE
    Satisfiable = λ ϕ → (ϕ ⊭ ff)
    Tautology = λ ϕ → (tt ⊨ ϕ)
    
    ⊨-resp-∧ : ∀ {ϕ ψ ξ ζ} → (ϕ ⊨ ψ) → (ξ ⊨ ζ) → ((ϕ ∧ ξ) ⊨ (ψ ∧ ζ))
    ⊨-resp-∧ ϕ⊨ψ ξ⊨ζ = ⊨-resp-¬ (⊨-resp-∨ (⊨-resp-¬ ϕ⊨ψ) (⊨-resp-¬ ξ⊨ζ))

    ⊨-left-∧ : ∀ {ϕ ψ} → ((ϕ ∧ ψ) ⊨ ϕ)
    ⊨-left-∧ = ⊨-trans (⊨-resp-¬ ⊨-left-∨) ⊨-elim-¬¬

    ⊨-right-∧ : ∀ {ϕ ψ} → ((ϕ ∧ ψ) ⊨ ψ)
    ⊨-right-∧ = ⊨-trans (⊨-resp-¬ ⊨-right-∨) ⊨-elim-¬¬

    ⊨-intro-∧ : ∀ {ϕ ψ χ} → (ϕ ⊨ ψ) → (ϕ ⊨ χ) → (ϕ ⊨ (ψ ∧ χ)) 
    ⊨-intro-∧ ϕ⊨ψ ϕ⊨χ = ⊨-trans ⊨-intro-¬¬ (⊨-resp-¬ (⊨-elim-∨ (⊨-resp-¬ ϕ⊨ψ) (⊨-resp-¬ ϕ⊨χ)))

    ⊨-intro-tt : ∀ {ϕ} → (ϕ ⊨ tt)
    ⊨-intro-tt = ⊨-trans ⊨-intro-¬¬ (⊨-resp-¬ ⊨-elim-ff)
    
    ⊨-assocl-∨ : ∀ {ϕ ψ χ} → ((ϕ ∨ (ψ ∨ χ)) ⊨ ((ϕ ∨ ψ) ∨ χ))
    ⊨-assocl-∨ = ⊨-elim-∨ (⊨-trans ⊨-left-∨ ⊨-left-∨) (⊨-elim-∨ (⊨-trans ⊨-right-∨ ⊨-left-∨) ⊨-right-∨)

    ⊨-assocr-∨ : ∀ {ϕ ψ χ} → (((ϕ ∨ ψ) ∨ χ) ⊨ (ϕ ∨ (ψ ∨ χ)))
    ⊨-assocr-∨ = ⊨-elim-∨ (⊨-elim-∨ ⊨-left-∨ (⊨-trans ⊨-left-∨ ⊨-right-∨)) (⊨-trans ⊨-right-∨ ⊨-right-∨)
