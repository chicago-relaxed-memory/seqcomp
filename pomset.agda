open import prelude
open import data-model using ( DataModel )

module pomset (DM : DataModel) (Event : Set) where

  open DataModel DM

  data Action : Set where
     R : Address → Value → Action
     W : Address → Value → Action
     ✓ : Formula → Action

  data Externals : Action → Set where
    R : ∀ {a v} → ((R a v) ∈ Externals)
    W : ∀ {a v} → ((W a v) ∈ Externals)

  Internals = λ e → (Externals e → FALSE)
  
  data Reads : Action → Set where
    R : ∀ {a v} → ((R a v) ∈ Reads)
    
  data Writes : Action → Set where
    W : ∀ {a v} → ((W a v) ∈ Writes)
    
  data Conflicts : (Action × Action) → Set where
    RW : ∀ {x v w} → ((R x v , W x w) ∈ Conflicts)
    WR : ∀ {x v w} → ((W x v , R x w) ∈ Conflicts)
    WW : ∀ {x v w} → ((W x v , W x w) ∈ Conflicts)
    
  dec-Externals : ∀ a → Dec(a ∈ Externals)
  dec-Externals (R x v) = yes R
  dec-Externals (W x v) = yes W
  dec-Externals (✓ ϕ) = no (λ ())
  
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
    ↓(e) = λ d → (d ∈ E) × (d ≤ e)

    X : Event → Set
    X(e) = (e ∈ E) × (act(e) ∈ Externals)

    I : Event → Set
    I(e) = (e ∈ E) × (act(e) ∈ Internals)

    field ≤-refl : ∀ {e} → (e ≤ e)
    field ≤-trans : ∀ {c d e} → (c ≤ d) → (d ≤ e) → (c ≤ e)
    field ≤-asym : ∀ {d e} → (e ≤ d) → (d ≤ e) → (d ≡ e)
    field I-max : ∀ {d e} → (d ≤ e) → (d ∈ I) → (d ≡ e)

    X⊆E : (X ⊆ E)
    X⊆E e (e∈E , _) = e∈E

    I⊆E : (I ⊆ E)
    I⊆E e (e∈E , _) = e∈E

    I∩X⊆∅ : ((I ∩ X) ⊆ ∅)
    I∩X⊆∅ e ((_ , ae∉X) , (_ , ae∈X)) = ae∉X ae∈X
    
    E⊆I⊎X : (E ⊆ (I ⊎ X))
    E⊆I⊎X e e∈E with dec-Externals (act(e))
    E⊆I⊎X e e∈E | yes ae∈X = right (λ{ (_ , ae∉X) → ae∉X ae∈X }) (e∈E , ae∈X)
    E⊆I⊎X e e∈E | no  ae∉X = left (e∈E , ae∉X) λ{ (_ , ae∈X) → ae∉X ae∈X }
    
    dec-X : ∀ e → (e ∈ E) → Dec(e ∈ X)
    dec-X e e∈E with dec-Externals(act(e))
    dec-X e e∈E | yes a∈X = yes (e∈E , a∈X)
    dec-X e e∈E | no  a∉X = no (λ e∈X → a∉X (snd e∈X))
    
    data _▷_ (D : Event → Set) (ϕψ : (Formula × Formula)) : Set where
      ▷-defn : ∀ e →
        (e ∈ I) →
        (fst(ϕψ) ⊨ pre(e)) →
        (post(e) ⊨ snd(ϕψ)) →
        (∀ d → (d < e) → (d ∈ D)) →
        ---------------------------
        D ▷ ϕψ

    ▷-resp-⊆ : ∀ {C D ϕ ψ} → (C ⊆ D) → (C ▷ (ϕ , ψ)) → (D ▷ (ϕ , ψ))
    ▷-resp-⊆ C⊆D (▷-defn e e∈I ϕ⊨pre post⊨ψ d<e⇒d∈C) = ▷-defn e e∈I ϕ⊨pre post⊨ψ (λ d d<e → C⊆D d (d<e⇒d∈C d d<e))
    
