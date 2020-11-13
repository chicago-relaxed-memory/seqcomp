open import prelude
open import data-model using ( DataModel )

module pomset (DM : DataModel) (Event : Set) where

  open DataModel DM

  data Action : Set where
     R : Address → Value → Action
     W : Address → Value → Action
     
  data Reads : Action → Set where
    R : ∀ {a v} → ((R a v) ∈ Reads)

  data Writes : Action → Set where
    W : ∀ {a v} → ((W a v) ∈ Writes)

  data Conflicts : Action → Action → Set where
    RW : ∀ {x v w} → Conflicts (R x v) (W x w)
    WR : ∀ {x v w} → Conflicts (W x v) (R x w)
    WW : ∀ {x v w} → Conflicts (W x v) (W x w)

  record PartialOrder : Set₁ where

    field _≤_ : Event → Event → Set
    field ≤-refl : ∀ {e} → (e ≤ e)
    field ≤-trans : ∀ {c d e} → (c ≤ d) → (d ≤ e) → (c ≤ e)
    field ≤-asym : ∀ {d e} → (e ≤ d) → (d ≤ e) → (d ≡ e)
  
  record Pomset : Set₁ where

    field E : Event → Set
    field _≤_ : Event → Event → Set
    field ℓ : Event → (Formula × Action)
    field τ : (Event → Set) → Formula → Formula

    pre : Event → Formula
    pre(e) = fst(ℓ(e))
    
    act : Event → Action
    act(e) = snd(ℓ(e))
    
    _<_ : Event → Event → Set
    (d < e) = (d ≤ e) × (d ≢ e)

    RE : Event → Set
    RE = E ∩ (act ⁻¹[ Reads ])

    WE : Event → Set
    WE = E ∩ (act ⁻¹[ Writes ])

    field ≤-refl : ∀ {e} → (e ≤ e)
    field ≤-trans : ∀ {c d e} → (c ≤ d) → (d ≤ e) → (c ≤ e)
    field ≤-asym : ∀ {d e} → (e ≤ d) → (d ≤ e) → (d ≡ e)

    field τ-resp-∩⊆ : ∀ {C D ϕ} → ((C ∩ E) ⊆ D) → (τ(C)(ϕ) ⊨ τ(D)(ϕ))
    field τ-resp-⊨ : ∀ {C ϕ ψ} → (ϕ ⊨ ψ) → (τ(C)(ϕ) ⊨ τ(C)(ψ))
    field τ-resp-∨ : ∀ {C ϕ ψ} → (τ(C)(ϕ ∨ ψ) ⊨ (τ(C)(ϕ) ∨ τ(C)(ψ)))

    τ-resp-⊆ : ∀ {C D ϕ} → (C ⊆ D) → (τ(C)(ϕ) ⊨ τ(D)(ϕ))
    τ-resp-⊆ C⊆D = τ-resp-∩⊆ (λ{ e (e∈C , _) → C⊆D e e∈C})
    
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
      
    PO : PartialOrder
    PO = record { _≤_ = _≤_ ; ≤-refl = ≤-refl ; ≤-trans = ≤-trans ; ≤-asym = ≤-asym }
    
