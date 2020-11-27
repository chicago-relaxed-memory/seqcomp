open import prelude
open import data-model using ( DataModel )

module pomset (DM : DataModel) (Event : Set) where

  open DataModel DM

  record PartialOrder : Set₁ where

    field _≤_ : Event → Event → Set
    field ≤-refl : ∀ {e} → (e ≤ e)
    field ≤-trans : ∀ {c d e} → (c ≤ d) → (d ≤ e) → (c ≤ e)
    field ≤-asym : ∀ {d e} → (e ≤ d) → (d ≤ e) → (d ≡ e)
    
    _<_ : Event → Event → Set
    (d < e) = (d ≤ e) × (d ≢ e)

  ≡PO : PartialOrder
  ≡PO = record
          { _≤_ = λ d e → (d ≡ e)
          ; ≤-refl = refl
          ; ≤-trans = ≡-trans
          ; ≤-asym = λ d=e e=d → e=d
          }
          
  record PomsetWithPreconditions : Set₁ where

    field E : Event → Set
    field PO : PartialOrder
    field ℓ : Event → (Formula × Action)
    
    open PartialOrder PO public

    pre : Event → Formula
    pre(e) = fst(ℓ(e))
    
    act : Event → Action
    act(e) = snd(ℓ(e))

    RE : Event → Set
    RE = E ∩ (act ⁻¹[ Reads ])

    WE : Event → Set
    WE = E ∩ (act ⁻¹[ Writes ])

    ↓RW : Event → Event → Set
    ↓RW(e) = E ∩ (λ d → (d ∈ RE) → (e ∈ WE) → (d ≤ e))
    
    RE⊆E : (RE ⊆ E)
    RE⊆E = ⊆-left-∩

    WE⊆E : (WE ⊆ E)
    WE⊆E = ⊆-left-∩

    ↓RW⊆E : ∀ e → (↓RW(e) ⊆ E)
    ↓RW⊆E e = ⊆-left-∩
    
    dec-E : ∀ e → Dec(e ∈ E)
    dec-E e = EXCLUDED_MIDDLE(e ∈ E)
    
  record PomsetWithPredicateTransformers : Set₁ where

    field PwP : PomsetWithPreconditions
    open PomsetWithPreconditions PwP public

    field τ : (Event → Set) → Formula → Formula

    field τ-resp-∩⊆ : ∀ {C D ϕ} → ((C ∩ E) ⊆ D) → (τ(C)(ϕ) ⊨ τ(D)(ϕ))
    field τ-resp-⊨ : ∀ {C ϕ ψ} → (ϕ ⊨ ψ) → (τ(C)(ϕ) ⊨ τ(C)(ψ))
    field τ-resp-∨ : ∀ {C ϕ ψ} → (τ(C)(ϕ ∨ ψ) ⊨ (τ(C)(ϕ) ∨ τ(C)(ψ)))
    field τ-refl-∨ : ∀ {C ϕ ψ} → ((τ(C)(ϕ) ∨ τ(C)(ψ)) ⊨ τ(C)(ϕ ∨ ψ))
    field τ-refl-∧ : ∀ {C ϕ ψ} → ((τ(C)(ϕ) ∧ τ(C)(ψ)) ⊨ τ(C)(ϕ ∧ ψ))

    τ-resp-⊆ : ∀ {C D ϕ} → (C ⊆ D) → (τ(C)(ϕ) ⊨ τ(D)(ϕ))
    τ-resp-⊆ C⊆D = τ-resp-∩⊆ (λ{ e (e∈C , _) → C⊆D e e∈C})
    
