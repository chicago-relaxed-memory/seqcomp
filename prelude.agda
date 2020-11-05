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
  open _×_ public

  _∈_ : ∀ {α} {X : Set α} → X → (X → Set α) → Set α
  e ∈ E = E e

  _∉_ : ∀ {X : Set} → X → (X → Set) → Set
  e ∉ E = E e → FALSE

  _⊆_ : ∀ {α} {X : Set α} → (X → Set α) → (X → Set α) → (Set α)
  (E ⊆ F) = ∀ e → (e ∈ E) → (e ∈ F)

  ∅ : ∀ {α} {X : Set α} → (X → Set)
  ∅ = λ e → FALSE
  
  _∩_ :  ∀ {X : Set} → (X → Set) → (X → Set) → (X → Set)
  (E ∩ F) = λ e → (e ∈ E) × (e ∈ F)
  
  data _∪_ {X : Set} (E F : X → Set) (e : X) : Set where
    left : (e ∈ E) → (e ∉ F) → (e ∈ (E ∪ F))
    right : (e ∉ E) → (e ∈ F) → (e ∈ (E ∪ F))
    both : (e ∈ E) → (e ∈ F) → (e ∈ (E ∪ F))

  neither : ∀ {X E F} {e : X} → (e ∉ E) → (e ∉ F) → (e ∉ (E ∪ F))
  neither e∉E e∉F (left e∈E _) = e∉E e∈E
  neither e∉E e∉F (right _ e∈F) = e∉F e∈F
  neither e∉E e∉F (both e∈E _) = e∉E e∈E
  
  dec-∪ : ∀ {X E F} {e : X} → Dec(e ∈ E) → Dec(e ∈ F) → Dec(e ∈ (E ∪ F))
  dec-∪ (yes e∈E) (yes e∈F) = yes (both e∈E e∈F)
  dec-∪ (yes e∈E) (no e∉F) = yes (left e∈E e∉F)
  dec-∪ (no e∉E) (yes e∈F) = yes (right e∉E e∈F)
  dec-∪ (no e∉E) (no e∉F)  = no (neither e∉E e∉F)

  data _⊎_ {X : Set} (E F : X → Set) (e : X) : Set where
    left : (e ∈ E) → (e ∉ F) → (e ∈ (E ⊎ F))
    right : (e ∉ E) → (e ∈ F) → (e ∈ (E ⊎ F))

  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ
  {-# BUILTIN NATURAL ℕ #-}
