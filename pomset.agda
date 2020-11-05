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

  Reads⊆Externals : Reads ⊆ Externals
  Reads⊆Externals _ R = R
  
  data Writes : Action → Set where
    W : ∀ {a v} → ((W a v) ∈ Writes)

  Writes⊆Externals : Writes ⊆ Externals
  Writes⊆Externals _ W = W
  
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

    RE : Event → Set
    RE(e) = (e ∈ E) × (act(e) ∈ Reads)

    WE : Event → Set
    WE(e) = (e ∈ E) × (act(e) ∈ Writes)

    field dec-E : ∀ e → Dec(e ∈ E)
    field ≤-refl : ∀ {e} → (e ≤ e)
    field ≤-trans : ∀ {c d e} → (c ≤ d) → (d ≤ e) → (c ≤ e)
    field ≤-asym : ∀ {d e} → (e ≤ d) → (d ≤ e) → (d ≡ e)
    field I-max : ∀ {d e} → (d ≤ e) → (d ∈ I) → (d ≡ e)

    X⊆E : (X ⊆ E)
    X⊆E e (e∈E , _) = e∈E

    I⊆E : (I ⊆ E)
    I⊆E e (e∈E , _) = e∈E

    RE⊆E : (RE ⊆ E)
    RE⊆E e (e∈E , _) = e∈E

    RE⊆X : (RE ⊆ X)
    RE⊆X e (e∈E , a∈R) = (e∈E , Reads⊆Externals _ a∈R)

    WE⊆E : (WE ⊆ E)
    WE⊆E e (e∈E , _) = e∈E

    WE⊆X : (WE ⊆ X)
    WE⊆X e (e∈E , a∈W) = (e∈E , Writes⊆Externals _ a∈W)

    I∩X⊆∅ : ((I ∩ X) ⊆ ∅)
    I∩X⊆∅ e ((_ , ae∉X) , (_ , ae∈X)) = ae∉X ae∈X
    
    E⊆I⊎X : (E ⊆ (I ⊎ X))
    E⊆I⊎X e e∈E with dec-Externals (act(e))
    E⊆I⊎X e e∈E | yes ae∈X = right (λ{ (_ , ae∉X) → ae∉X ae∈X }) (e∈E , ae∈X)
    E⊆I⊎X e e∈E | no  ae∉X = left (e∈E , ae∉X) λ{ (_ , ae∈X) → ae∉X ae∈X }
    
    dec-I : ∀ e → Dec(e ∈ I)
    dec-I e with dec-E(e) | dec-Externals(act(e))
    dec-I e | yes e∈E | yes a∈X = no (λ e∈I → snd e∈I a∈X)
    dec-I e | yes e∈E | no  a∉X = yes (e∈E , a∉X)
    dec-I e | no e∉E  | _ = no (λ e∈I → e∉E (I⊆E e e∈I))
    
    dec-X : ∀ e → Dec(e ∈ X)
    dec-X e with dec-E(e) | dec-Externals(act(e))
    dec-X e | yes e∈E | yes a∈X = yes (e∈E , a∈X)
    dec-X e | yes e∈E | no  a∉X = no (λ e∈X → a∉X (snd e∈X))
    dec-X e | no e∉E  | _ = no (λ e∈X → e∉E (X⊆E e e∈X))
