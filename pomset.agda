open import prelude
open import data-model using ( DataModel )

module pomset (DM : DataModel) (Event : Set) where

  open DataModel DM

  data Action : Set where
     R : Address → Value → Action
     W : Address → Value → Action
     ✓ : Formula → Action

  data Visibles : Action → Set where
    R : ∀ {a v} → ((R a v) ∈ Visibles)
    W : ∀ {a v} → ((W a v) ∈ Visibles)
    
  data Reads : Action → Set where
    R : ∀ {a v} → ((R a v) ∈ Reads)
    
  data Writes : Action → Set where
    W : ∀ {a v} → ((W a v) ∈ Writes)
    
  data Conflicts : (Action × Action) → Set where
    RW : ∀ {x v w} → ((R x v , W x w) ∈ Conflicts)
    WR : ∀ {x v w} → ((W x v , R x w) ∈ Conflicts)
    WW : ∀ {x v w} → ((W x v , W x w) ∈ Conflicts)
    
  dec-vis : ∀ a → Dec(a ∈ Visibles)
  dec-vis (R x v) = yes R
  dec-vis (W x v) = yes W
  dec-vis (✓ ϕ) = no (λ ())
  
  postcondition : Action → Formula
  postcondition (R x v) = tt
  postcondition (W x v) = tt
  postcondition (✓ ϕ) = ϕ
  
  record Pomset : Set₁ where

    field E : Event → Set
    field _≤_ : Event → Event → Set
    field ℓ : Event → (Formula × Action)

    pre : Event → Formula
    pre(e) = fst(ℓ(e))
    
    post : Event → Formula
    post(e) = postcondition(snd(ℓ(e)))
    
    act : Event → Action
    act(e) = snd(ℓ(e))

    _<_ : Event → Event → Set
    (d < e) = (d ≤ e) × (d ≢ e)

    ↓ : Event → Event → Set
    ↓(e) = λ d → (d ≤ e)

    field ≤-refl : ∀ {e} → (e ≤ e)
    field ≤-trans : ∀ {c d e} → (c ≤ d) → (d ≤ e) → (c ≤ e)
    field ≤-asym : ∀ {d e} → (e ≤ d) → (d ≤ e) → (d ≡ e)
    field ✓-max : ∀ {d e} → (d < e) → (act(d) ∈ Visibles)

    data _⊨_⇝_ (D : Event → Set) (ϕ : Formula) (ψ : Formula) : Set where
      ⇝-defn : ∀ {e ϕ′ ψ′} → 
        (ℓ(e) ≡ (ϕ′ , ✓ ψ′)) →
        (ϕ ⊨ ϕ′) →
        (ψ′ ⊨ ψ) →
        (∀ d → (d < e) → (d ∈ D)) →
        ---------------------------
        D ⊨ ϕ ⇝ ψ
