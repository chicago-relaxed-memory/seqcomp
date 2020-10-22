open import prelude
open import data-model using ( DataModel )

module pomset (DM : DataModel) (Event : Set) where

  open DataModel DM

  data Action : Set where
     R : Address → Value → Action
     W : Address → Value → Action
     ✓ : Formula → Action

  data ReadWrites : Action → Set where
    R : ∀ {a v} → ((R a v) ∈ ReadWrites)
    W : ∀ {a v} → ((W a v) ∈ ReadWrites)
    
  data Reads : Action → Set where
    R : ∀ {a v} → ((R a v) ∈ Reads)
    
  data Writes : Action → Set where
    W : ∀ {a v} → ((W a v) ∈ Writes)
    
  data Ticks : Action → Set where
    ✓ : ∀ {ϕ} → ((✓ ϕ) ∈ Ticks)
     
  record Pomset : Set₁ where

    field E : Event → Set
    field _≤_ : Event → Event → Set
    field ℓ : Event → (Formula × Action)

    pre : Event → Formula
    pre(e) = fst(ℓ(e))
    
    act : Event → Action
    act(e) = snd(ℓ(e))

    _<_ : Event → Event → Set
    (d < e) = (d ≤ e) × (d ≢ e)

    ↓ : Event → Event → Set
    ↓(e) = λ d → (d ≤ e)
    
    field ✓-max : ∀ d e → (d < e) → (act(d) ∉ Ticks)

    data _⊨_⇝_ (D : Event → Set) (ϕ : Formula) (ψ : Formula) : Set where
      ⇝-defn : ∀ {e ϕ′ ψ′} → 
        (ℓ(e) ≡ (ϕ′ , ✓ ψ′)) →
        (ϕ ⊨ ϕ′) →
        (ψ′ ⊨ ψ) →
        (∀ d → (d < e) → (d ∈ D)) →
        ---------------------------
        D ⊨ ϕ ⇝ ψ
