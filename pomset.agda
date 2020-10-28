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

  Invisibles = λ e → (Visibles e → FALSE)
  
  data Reads : Action → Set where
    R : ∀ {a v} → ((R a v) ∈ Reads)
    
  data Writes : Action → Set where
    W : ∀ {a v} → ((W a v) ∈ Writes)
    
  data Conflicts : (Action × Action) → Set where
    RW : ∀ {x v w} → ((R x v , W x w) ∈ Conflicts)
    WR : ∀ {x v w} → ((W x v , R x w) ∈ Conflicts)
    WW : ∀ {x v w} → ((W x v , W x w) ∈ Conflicts)
    
  dec-Visibles : ∀ a → Dec(a ∈ Visibles)
  dec-Visibles (R x v) = yes R
  dec-Visibles (W x v) = yes W
  dec-Visibles (✓ ϕ) = no (λ ())
  
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

    V : Event → Set
    V(e) = (e ∈ E) × (act(e) ∈ Visibles)

    I : Event → Set
    I(e) = (e ∈ E) × (act(e) ∈ Invisibles)

    field ≤-refl : ∀ {e} → (e ≤ e)
    field ≤-trans : ∀ {c d e} → (c ≤ d) → (d ≤ e) → (c ≤ e)
    field ≤-asym : ∀ {d e} → (e ≤ d) → (d ≤ e) → (d ≡ e)
    field ✓-max : ∀ {d e} → (d < e) → (d ∈ V)

    V⊆E : (V ⊆ E)
    V⊆E e (e∈E , _) = e∈E

    I⊆E : (I ⊆ E)
    I⊆E e (e∈E , _) = e∈E

    I∩V⊆∅ : ((I ∩ V) ⊆ ∅)
    I∩V⊆∅ e ((_ , ae∉Vis) , (_ , ae∈Vis)) = ae∉Vis ae∈Vis
    
    E⊆I∪V : (E ⊆ (I ∪ V))
    E⊆I∪V e e∈E with dec-Visibles (act(e))
    E⊆I∪V e e∈E | yes ae∈Vis = inr (e∈E , ae∈Vis)
    E⊆I∪V e e∈E | no  ae∉Vis = inl (e∈E , ae∉Vis)
    
    dec-V : ∀ e → (e ∈ E) → Dec(e ∈ V)
    dec-V e e∈E with dec-Visibles(act(e))
    dec-V e e∈E | yes a∈V = yes (e∈E , a∈V)
    dec-V e e∈E | no  a∉V = no (λ e∈V → a∉V (snd e∈V))
    
    data _⊨_⇝_ (D : Event → Set) (ϕ : Formula) (ψ : Formula) : Set where
      ⇝-defn : ∀ e →
        (e ∈ I) →
        (ϕ ⊨ pre(e)) →
        (post(e) ⊨ ψ) →
        (∀ d → (d < e) → (d ∈ D)) →
        ---------------------------
        D ⊨ ϕ ⇝ ψ

    ⇝-resp-⊆ : ∀ {C D ϕ ψ} → (C ⊆ D) → (C ⊨ ϕ ⇝ ψ) → (D ⊨ ϕ ⇝ ψ)
    ⇝-resp-⊆ C⊆D (⇝-defn e e∈I ϕ⊨pre post⊨ψ d<e⇒d∈C) = ⇝-defn e e∈I ϕ⊨pre post⊨ψ (λ d d<e → C⊆D d (d<e⇒d∈C d d<e))
    
