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

  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ
  {-# BUILTIN NATURAL ℕ #-}

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
  
  postulate EXCLUDED_MIDDLE : ∀ X → Dec(X)

  _⁻¹[_] : ∀ {X Y : Set} → (X → Y) → (Y → Set) → (X → Set)
  f ⁻¹[ E ] = λ e → (f e) ∈ E
  
  ⊆-left-∪ : ∀ {X} {E F :  X → Set} → E ⊆ (E ∪ F)
  ⊆-left-∪ {F = F} e e∈E with EXCLUDED_MIDDLE(e ∈ F)
  ⊆-left-∪ e e∈E | yes e∈F = both e∈E e∈F
  ⊆-left-∪ e e∈E | no e∉F = left e∈E e∉F
  
  ⊆-right-∪ : ∀ {X} {E F :  X → Set} → F ⊆ (E ∪ F)
  ⊆-right-∪ {E = E} e e∈E with EXCLUDED_MIDDLE(e ∈ E)
  ⊆-right-∪ e e∈F | yes e∈E = both e∈E e∈F
  ⊆-right-∪ e e∈F | no e∉E = right e∉E e∈F
  
  ⊆-refl : ∀ {X : Set} {E : X → Set} → (E ⊆ E)
  ⊆-refl e e∈E = e∈E

  ⊆-trans : ∀ {X : Set} {D E F : X → Set} → (D ⊆ E) → (E ⊆ F) → (D ⊆ F)
  ⊆-trans D⊆E E⊆F e e∈D = E⊆F e (D⊆E e e∈D)

  ⊆-resp-∪ : ∀ {X : Set} {C D E F : X → Set} → (C ⊆ D) → (E ⊆ F) → ((C ∪ E) ⊆ (D ∪ F))
  ⊆-resp-∪ C⊆D E⊆F e (left e∈C _) = ⊆-left-∪ e (C⊆D e e∈C)
  ⊆-resp-∪ C⊆D E⊆F e (right _ e∈E) = ⊆-right-∪ e (E⊆F e e∈E)
  ⊆-resp-∪ C⊆D E⊆F e (both e∈C e∈E) = both (C⊆D e e∈C) (E⊆F e e∈E)
  
  ⊆-elim-∪ : ∀ {X : Set} {D E F : X → Set} → (D ⊆ F) → (E ⊆ F) → ((D ∪ E) ⊆ F)
  ⊆-elim-∪ D⊆F E⊆F e (left e∈D _) = D⊆F e e∈D
  ⊆-elim-∪ D⊆F E⊆F e (right _ e∈E) = E⊆F e e∈E
  ⊆-elim-∪ D⊆F E⊆F e (both e∈D _) = D⊆F e e∈D
  
  ⊆-assocl-∪ : ∀ {X} {D E F : X → Set} → (D ∪ (E ∪ F)) ⊆ ((D ∪ E) ∪ F)
  ⊆-assocl-∪ =  ⊆-elim-∪ (⊆-trans ⊆-left-∪ ⊆-left-∪) (⊆-elim-∪ (⊆-trans ⊆-right-∪ ⊆-left-∪) ⊆-right-∪)
  
  ⊆-assocr-∪ : ∀ {X} {D E F : X → Set} → ((D ∪ E) ∪ F) ⊆ (D ∪ (E ∪ F))
  ⊆-assocr-∪ =  ⊆-elim-∪ (⊆-elim-∪ ⊆-left-∪ (⊆-trans ⊆-left-∪ ⊆-right-∪)) (⊆-trans ⊆-right-∪ ⊆-right-∪)

  ⊆-resp-∩ : ∀ {X} {C D E F :  X → Set} → (C ⊆ D) → (E ⊆ F) → ((C ∩ E) ⊆ (D ∩ F))
  ⊆-resp-∩ C⊆D E⊆F e (e∈C , e∈E) = (C⊆D e e∈C , E⊆F e e∈E)

  ⊆-left-∩ : ∀ {X} {E F :  X → Set} → (E ∩ F) ⊆ E
  ⊆-left-∩ e (e∈E , e∈F) = e∈E

  ⊆-right-∩ : ∀ {X} {E F :  X → Set} → (E ∩ F) ⊆ F
  ⊆-right-∩ e (e∈E , e∈F) = e∈F

  ⊆-resp-∩⁻¹ : ∀ {X Y : Set} {E F : X → Set} {f g : X → Y} → (∀ e → (e ∈ E) → (f(e) ≡ g(e))) → (E ⊆ F) → (G : Y → Set) → ((E ∩ (g ⁻¹[ G ])) ⊆ (F ∩ (f ⁻¹[ G ])))
  ⊆-resp-∩⁻¹ f=g E⊆F G e (e∈E , e∈f⁻¹[G]) = (E⊆F e e∈E , ≡-subst G (≡-symm(f=g e e∈E)) e∈f⁻¹[G])
    
  ⊆-refl-∩⁻¹ : ∀ {X Y : Set} {E F : X → Set} {f g : X → Y} → (∀ e → (e ∈ F) → (f(e) ≡ g(e))) → (F ⊆ E) → (G : Y → Set) → (((E ∩ (f ⁻¹[ G ])) ∩ F) ⊆ (F ∩ (g ⁻¹[ G ])))
  ⊆-refl-∩⁻¹ f=g E⊆F G e ((e∈E , e∈f⁻¹[G]) , e∈F) = (e∈F , ≡-subst G (f=g e e∈F) e∈f⁻¹[G])
    
  ⊆-intro-∩ : ∀ {X : Set} {D E F : X → Set} → (D ⊆ E) → (D ⊆ F) → (D ⊆ (E ∩ F))
  ⊆-intro-∩ D⊆E D⊆F e e∈D = (D⊆E e e∈D , D⊆F e e∈D)

  ⊆-elim-∅ : ∀ {X : Set} {E : X → Set} → (∅ ⊆ E)
  ⊆-elim-∅ e ()
