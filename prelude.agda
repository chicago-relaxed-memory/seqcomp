module prelude where

  data FALSE : Set where

  CONTRADICTION : ∀ {α} {X : Set α} → FALSE → X
  CONTRADICTION ()

  data _≡_ {X : Set} (x : X) : X → Set where
    refl : (x ≡ x)

  ≡-symm : ∀ {X} {x y : X} → (x ≡ y) → (y ≡ x)
  ≡-symm refl = refl

  ≡-trans : ∀ {X} {x y z : X} → (x ≡ y) → (y ≡ z) → (x ≡ z)
  ≡-trans refl refl = refl

  ≡-cong : ∀ {X Y} (f : X → Y) {x y} → (x ≡ y) → (f x ≡ f y)
  ≡-cong f refl = refl

  ≡-cong₂ : ∀ {X Y Z} (f : X → Y → Z) {x₁ x₂ y₁ y₂} → (x₁ ≡ x₂) → (y₁ ≡ y₂) → (f x₁ y₁ ≡ f x₂ y₂)
  ≡-cong₂ f refl refl = refl

  ≡-subst : ∀ {X} (P : X → Set) {x y} → (x ≡ y) → (P x) → (P y)
  ≡-subst f refl Px = Px

  ≡-subst₂ : ∀ {X Y} (P : X → Y → Set) {x₁ x₂ y₁ y₂} → (x₁ ≡ x₂) → (y₁ ≡ y₂) → (P x₁ y₁) → (P x₂ y₂)
  ≡-subst₂ f refl refl Pxy = Pxy

  _≢_ : ∀ {X : Set} → X → X → Set
  x ≢ y = (x ≡ y) → FALSE

  data Singleton {A : Set} (x : A) : Set where
    _with≡_ : (y : A) → (x ≡ y) → Singleton x

  inspect : ∀ {A} (x : A) → Singleton x
  inspect x = x with≡ refl

  data Dec (X : Set) : Set where
    yes : X → Dec X
    no : (X → FALSE) → Dec X

  record _×_ (X Y : Set) : Set where
    constructor _,_
    field fst : X
    field snd : Y

  data _⊎_ (X Y : Set) : Set where
    inl : X → (X ⊎ Y)
    inr : Y → (X ⊎ Y)

  open _×_ public

  data Maybe (X : Set) : Set where
    none : Maybe X
    some : X → Maybe X

  _∈_ : ∀ {α} {X : Set α} → X → (X → Set α) → Set α
  e ∈ E = E e

  _∉_ : ∀ {X : Set} → X → (X → Set) → Set
  e ∉ E = E e → FALSE

  _⊆_ : ∀ {α} {X : Set α} → (X → Set α) → (X → Set α) → (Set α)
  (E ⊆ F) = ∀ e → (e ∈ E) → (e ∈ F)

  ∅ : ∀ {X : Set} → (X → Set)
  ∅ = λ e → FALSE
  
  _∩_ :  ∀ {X : Set} → (X → Set) → (X → Set) → (X → Set)
  (E ∩ F) = λ e → (e ∈ E) × (e ∈ F)
  
  _∪_ :  ∀ {X : Set} → (X → Set) → (X → Set) → (X → Set)
  (E ∪ F) = λ e → (e ∈ E) ⊎ (e ∈ F)
  
