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

  data Conflicts : (Action × Action) → Set where
    RW : ∀ {x v w} → ((R x v , W x w) ∈ Conflicts)
    WR : ∀ {x v w} → ((W x v , R x w) ∈ Conflicts)
    WW : ∀ {x v w} → ((W x v , W x w) ∈ Conflicts)

  record Events : Set₁ where

    field Carrier : Event → Set
    field dec-Carrier : ∀ e → Dec(e ∈ Carrier)

  open Events public
  
  record Pomset : Set₁ where

    field ES : Events
    field ↓ : Event → Events
    field ℓ : Event → (Formula × Action)
    field τ : Events → Formula → Formula

    E : Event → Set
    E = Carrier ES

    _≤_ : Event → Event → Set
    d ≤ e = d ∈ Carrier(↓(e))
 
    pre : Event → Formula
    pre(e) = fst(ℓ(e))
    
    act : Event → Action
    act(e) = snd(ℓ(e))
    
    _<_ : Event → Event → Set
    (d < e) = (d ≤ e) × (d ≢ e)

    RE : Event → Set
    RE(e) = (e ∈ E) × (act(e) ∈ Reads)

    WE : Event → Set
    WE(e) = (e ∈ E) × (act(e) ∈ Writes)

    field ≤-refl : ∀ {e} → (e ≤ e)
    field ≤-trans : ∀ {c d e} → (c ≤ d) → (d ≤ e) → (c ≤ e)
    field ≤-asym : ∀ {d e} → (e ≤ d) → (d ≤ e) → (d ≡ e)

    field τ-resp-⊆ : ∀ C D ϕ → (Carrier C ⊆ Carrier D) → (τ(C)(ϕ) ⊨ τ(D)(ϕ))

    ↓W : Event → Events
    ↓W(e) with act(e)
    ↓W e | R x v = ES
    ↓W e | W x v = ↓(e)
    
    RE⊆E : (RE ⊆ E)
    RE⊆E e (e∈E , _) = e∈E

    WE⊆E : (WE ⊆ E)
    WE⊆E e (e∈E , _) = e∈E

