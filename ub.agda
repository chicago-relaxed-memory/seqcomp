module ub where

----------------------

  postulate Event : Set
  postulate Value : Set
  postulate Address : Set
  postulate Register : Set
  postulate Precondition : Set

----------------------

  record Substitution {α} (X : Set α) : Set α where
    field subst : X → Register → Value → X

  _[_:=_] : ∀ {α} {X : Set α} → {{S : Substitution X}} → X → Register → Value → X
  _[_:=_] {X} {{S}} = subst where open Substitution S

----------------------

  instance
  
    postulate φsubst : Substitution Precondition
  
----------------------

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
  
  _≢_ : ∀ {X : Set} → X → X → Set
  x ≢ y = (x ≡ y) → FALSE

  _is-independent-of_ : {X : Set} → {{S : Substitution X}} → X → Register → Set
  x is-independent-of r = ∀ {v} → x ≡ (x [ r := v ])
  
  data Singleton {A : Set} (x : A) : Set where
    _with≡_ : (y : A) → (x ≡ y) → Singleton x

  inspect : ∀ {A} (x : A) → Singleton x
  inspect x = x with≡ refl

  data Dec (X : Set) : Set where
    yes : X → Dec X
    no : (X → FALSE) → Dec X

  postulate dec-≡ : (v w : Value) → Dec(v ≡ w)
  
  record _×_ (X Y : Set) : Set where
    constructor _,_
    field fst : X
    field snd : Y

  open _×_
  
  data Maybe (X : Set) : Set where
    none : Maybe X
    some : X → Maybe X
    
  _∈_ : ∀ {α} {X : Set α} → X → (X → Set α) → Set α
  e ∈ E = E e

  _∉_ : ∀ {X : Set} → X → (X → Set) → Set
  e ∉ E = E e → FALSE

  _⊆_ : ∀ {α} {X : Set α} → (X → Set α) → (X → Set α) → (Set α)
  (E ⊆ F) = ∀ {e} → (e ∈ E) → (e ∈ F)
  
----------------------

  data Cmd : Set where
    exit : Cmd
    load_:=_∙_ : Register → Address → Cmd → Cmd

  instance

    Csubst : Substitution Cmd
    Csubst = record { subst = subst } where

      subst : Cmd → Register → Value → Cmd
      subst exit r v = exit
      subst (load s := x ∙ C) r v = load s := x ∙ subst C r v
    
----------------------

  data Action : Set where
    R : Address → Value → Action
    W : Address → Value → Action
    
  record Pomset : Set₁ where

    field E : Event → Set
    field _≤_ : Event → Event → Set
    field ℓ : Event → (Precondition × Action)

    _<_ : Event → Event → Set
    d < e = (d ≤ e) × (d ≢ e)

  pre_ = fst
  act_ = snd
  
  instance

    PSubst : Substitution Pomset
    PSubst = record { subst = subst } where

      subst : Pomset → Register → Value → Pomset
      subst P r v = record { E = E ; _≤_ = _≤_ ; ℓ = λ e → ((pre ℓ(e)) [ r := v ] , act ℓ(e)) } where open Pomset P

  data load-cases (r : Register) (x : Address) (v : Value) (P P′ : Pomset) (e : Event) : Set where

    old-dependent : let open Pomset P in let open Pomset P′ renaming (E to E′; _<_ to _<′_ ; ℓ to ℓ′) in
      ∀ {d} →
      d ∈ E →
      e ∈ E′ →
      d < e →
      act ℓ(d) ≡ (R x v) →
      pre ℓ′(e) ≡ (pre ℓ(e)) [ r := v ] →
      ----------------------
      e ∈ load-cases r x v P P′

    old-independent : let open Pomset P in let open Pomset P′ renaming (E to E′; ℓ to ℓ′) in
      e ∈ E′ →
      pre ℓ′(e) ≡ pre ℓ(e) →
      (pre ℓ′(e) is-independent-of r) →
      ----------------------
      e ∈ load-cases r x v P P′

    new-load : let open Pomset P in let open Pomset P′ renaming (E to E′ ; ℓ to ℓ′) in
      ∀ {w} →
      e ∉ E′ →
      act ℓ(e) ≡ (R x w) →
      ----------------------
      e ∈ load-cases r x v P P′

    new-ub : let open Pomset P in let open Pomset P′ renaming (E to E′ ; ℓ to ℓ′ ; _<_ to _<′_) in
      ∀ {w c d} →
      c ∈ E →
      d ∈ E →
      e ∉ E′ →
      v ≢ w →
      act ℓ(c) ≡ (R x v) →
      act ℓ(d) ≡ (R x w) →
      c < e →
      d < e →
      ----------------------
      e ∈ load-cases r x v P P′

  data ⟦_⟧ : Cmd → Pomset → Set₁ where

    exit : ∀ {P} → let open Pomset P in
      (∀ {e} → (e ∉ E)) →
      ----------------------
      P ∈ ⟦ exit ⟧

    load : ∀ {P P′ r x v C} → let open Pomset P in let open Pomset P′ renaming (E to E′; _≤_ to _≤′_ ; ℓ to ℓ′) in
      P′ ∈ ⟦ C ⟧ →
      (E′ ⊆ E) →
      (∀ {d e} → (d ∈ E′) → (e ∈ E′) → (d ≤′ e) → (d ≤ e)) →
      (∀ {d e} → (d ∈ E′) → (e ∈ E′) → (d ≤′ e) → (d ≤ e)) →
      (∀ {e} → (e ∈ E′) → (act ℓ(e) ≡ act ℓ′(e))) →
      (∀ {e} → (e ∈ E) → (e ∈ load-cases r x v P P′)) →
      ----------------------
      P ∈ ⟦ load r := x ∙ C ⟧
      
----------------------
     
  data Access : Set where
    ro : Access
    rw : Access

  Store = Address → (Access × Maybe Value)

  acc_ = fst
  val_ = snd
  
  data Configuration : Set where
     _,_ : Store → Cmd → Configuration

  data _↦_ : Configuration → Configuration → Set where

    load-ok :
      ∀ {σ r x C v} →
      val σ(x) ≡ (some v) →
      ------------------------------------------
      (σ , load r := x ∙ C) ↦ (σ , C [ r := v ])

    load-segv :
      ∀ {σ σ′ r x C C′} →
      val σ(x) ≡ none →
      -----------------------------------
      (σ , load r := x ∙ C) ↦ (σ′ , C′)

  data _↦*_ : Configuration → Configuration → Set where
  
      done :
        ∀ {σ σ′ C} →
        (∀ {x} → (σ(x) ≡ σ′(x))) → 
        --------------------
        ((σ , C) ↦* (σ′ , C))

      step :
        ∀ {σ σ′ σ″ C C′ C″} →
        ((σ , C) ↦ (σ′ , C′)) →
        ((σ′ , C′) ↦* (σ″ , C″)) →
        -------------------------------
        ((σ , C) ↦* (σ″ , C″))

  ⟨_⟩_⟨_⟩ : Store → Cmd → Store → Set
  ⟨ σ ⟩ C ⟨ σ′ ⟩ = (σ , C) ↦* (σ′ , exit)
  
  _≲_ : Cmd → Cmd → Set
  (C ≲ D) = ∀ {σ σ′} → (⟨ σ ⟩ D ⟨ σ′ ⟩) → (⟨ σ ⟩ C ⟨ σ′ ⟩)

----------------------

  data ⟪_⟫_⟪_⟫ (σ : Store) (P : Pomset) (σ′ : Store) : Set where

    ok : let open Pomset P in
        (∀ {e x v α} → (e ∈ E) → (act ℓ(e) ≡ (R x v)) → (σ(x) ≡ (α , some v))) → 
        (∀ {e x v} → (e ∈ E) → (act ℓ(e) ≡ (W x v)) → (σ′(x) ≡ (rw , some v))) →
        (∀ {x α β v w} → (σ(x) ≡ (α , v)) → (σ′(x) ≡ (β , w)) → (α ≡ β)) → 
        (∀ {x} → (∀ {e v} → (e ∈ E) → (act ℓ(e) ≢ (W x v))) → (σ(x) ≡ σ′(x))) →
        ----------------------------
        ⟪ σ ⟫ P ⟪ σ′ ⟫
    
    segv-load : let open Pomset P in
        ∀ {e x v} →
        e ∈ E →
        val σ(x) ≡ none →
        act ℓ(e) ≡ (R x v) →
        (∀ {d y w} → (d ∈ E) → (d < e) → (act ℓ(d) ≡ (R y w)) → (val σ(y) ≡ (some w))) →
        ----------------------------
        ⟪ σ ⟫ P ⟪ σ′ ⟫

    segv-store : let open Pomset P in
        ∀ {x e v} →
        e ∈ E →
        acc σ(x) ≡ ro →
        act ℓ(e) ≡ (W x v) →
        ----------------------------
        ⟪ σ ⟫ P ⟪ σ′ ⟫

----------------------

  postulate sem-resp-subst : ∀ {P C} r v → (P ∈ ⟦ C ⟧) → ((P [ r := v ]) ∈ ⟦ C [ r := v ] ⟧)
  postulate sem-ignores-subst : ∀ {P σ σ′} r v → (⟪ σ ⟫ P ⟪ σ′ ⟫) → (⟪ σ ⟫ (P [ r := v ]) ⟪ σ′ ⟫) 

----------------------

  {-# NON_TERMINATING #-}
  this : ∀ {P C σ σ′} → (P ∈ ⟦ C ⟧) → (⟪ σ ⟫ P ⟪ σ′ ⟫) → (⟨ σ ⟩ C ⟨ σ′ ⟩)

  this {P} {exit} {σ} {σ′} (exit E=∅) (ok _ _ _ H) = done σ=σ' where
  
     σ=σ' : ∀ {x} → (σ(x) ≡ σ′(x))
     σ=σ' = H (λ e∈E → CONTRADICTION (E=∅ e∈E))
     
  this {P} {exit} (exit E=∅) (segv-load e∈E _ _ _) = CONTRADICTION (E=∅ e∈E)

  this {P} {exit} (exit E=∅) (segv-store e∈E _ _) = CONTRADICTION (E=∅ e∈E)

  this {P} {load r := x ∙ C} {σ} {σ′} (load P′∈⟦C⟧ E′⊆E ≤′⊆≤ ≤⊆≤′ a′⊆a P✓) σPσ′ with inspect(val σ(x))
  this {P} {load r := x ∙ C} {σ} {σ′} (load P′∈⟦C⟧ E′⊆E ≤′⊆≤ ≤⊆≤′ a′⊆a P✓) σPσ′ | none with≡ vσx=none = step (load-segv vσx=none) (done refl)

  this {P} {load r := x ∙ C} {σ} {σ′} (load P′∈⟦C⟧ E′⊆E ≤′⊆≤ ≤⊆≤′ a′⊆a P✓) (segv-load e∈E vσy=none ae=Ryu <✓) | some w with≡ vσx=somew with P✓ e∈E
    
  this {P} {load r := x ∙ C} {σ} {σ′} (load {P′ = P′} P′∈⟦C⟧ E′⊆E ≤′⊆≤ ≤⊆≤′ a′⊆a P✓) (segv-load {e = e} e∈E vσy=none ae=Ryu <✓) | some w with≡ vσx=somew | old-dependent _ e∈E′ _ _ _ = step (load-ok vσx=somew) σC[r:=w]σ′ where
  
    open Pomset P′ renaming (_<_ to _<′_ ; ℓ to ℓ′ ; E to E′)
    
    <′✓ : ∀ {d y w} → (d ∈ E′) → (d <′ e) → (act ℓ′(d) ≡ (R y w)) → (val σ(y) ≡ some w)
    <′✓ d∈E′ (d≤′e , d≠e) a′d=Ryw = <✓ (E′⊆E d∈E′) (≤′⊆≤ d∈E′ e∈E′ d≤′e , d≠e) (≡-trans (a′⊆a d∈E′) a′d=Ryw)

    σP′σ′ : ⟪ σ ⟫ P′ ⟪ σ′ ⟫
    σP′σ′ = segv-load e∈E′ vσy=none (≡-trans (≡-symm (a′⊆a e∈E′)) ae=Ryu) <′✓

    σC[r:=w]σ′ : ⟨ σ ⟩ (C [ r := w ]) ⟨ σ′ ⟩
    σC[r:=w]σ′ = this (sem-resp-subst r w P′∈⟦C⟧) (sem-ignores-subst r w σP′σ′)
    
  this {P} {load r := x ∙ C} {σ} {σ′} (load {P′ = P′} P′∈⟦C⟧ E′⊆E ≤′⊆≤ ≤⊆≤′ a′⊆a P✓) (segv-load {e = e} e∈E vσy=none ae=Ryu <✓) | some w with≡ vσx=somew | old-independent e∈E′ _ _ = step (load-ok vσx=somew) σC[r:=w]σ′ where
  
    open Pomset P′ renaming (_<_ to _<′_ ; ℓ to ℓ′ ; E to E′)
    
    <′✓ : ∀ {d y w} → (d ∈ E′) → (d <′ e) → (act ℓ′(d) ≡ (R y w)) → (val σ(y) ≡ some w)
    <′✓ d∈E′ (d≤′e , d≠e) a′d=Ryw = <✓ (E′⊆E d∈E′) (≤′⊆≤ d∈E′ e∈E′ d≤′e , d≠e) (≡-trans (a′⊆a d∈E′) a′d=Ryw)

    σP′σ′ : ⟪ σ ⟫ P′ ⟪ σ′ ⟫
    σP′σ′ = segv-load e∈E′ vσy=none (≡-trans (≡-symm (a′⊆a e∈E′)) ae=Ryu) <′✓

    σC[r:=w]σ′ : ⟨ σ ⟩ (C [ r := w ]) ⟨ σ′ ⟩
    σC[r:=w]σ′ = this (sem-resp-subst r w P′∈⟦C⟧) (sem-ignores-subst r w σP′σ′)
    
  this {P} {load r := x ∙ C} (load P′∈⟦C⟧ E′⊆E ≤′⊆≤ ≤⊆≤′ a′⊆a P✓) (segv-load e∈E vσy=none ae=Ryu <✓) | some w with≡ vσx=somew | new-load _ ae=Rxv with ≡-trans (≡-symm ae=Ryu) ae=Rxv
  this {P} {load r := x ∙ C} (load P′∈⟦C⟧ E′⊆E ≤′⊆≤ ≤⊆≤′ a′⊆a P✓) (segv-load e∈E vσx=none ae=Ryu <✓) | some w with≡ vσx=somew | new-load _ ae=Rxv | refl with ≡-trans (≡-symm vσx=none) vσx=somew
  this {P} {load r := x ∙ C} (load P′∈⟦C⟧ E′⊆E ≤′⊆≤ ≤⊆≤′ a′⊆a P✓) (segv-load e∈E vσx=none ae=Ryu <✓) | some w₁ with≡ vσx=somew | new-load _ ae=Rxv | refl | ()

  this {P} {load r := x ∙ C} (load P′∈⟦C⟧ E′⊆E ≤′⊆≤ ≤⊆≤′ a′⊆a P✓) (segv-load e∈E vσy=none ae=Ryu <✓) | some w with≡ vσx=somew | new-ub c∈E d∈E _ v≠t ac=Rxv ad=Rxt c<e d<e with ≡-trans (≡-symm (<✓ c∈E c<e ac=Rxv)) (<✓ d∈E d<e ad=Rxt)
  this {P} {load r := x ∙ C} (load P′∈⟦C⟧ E′⊆E ≤′⊆≤ ≤⊆≤′ a′⊆a P✓) (segv-load e∈E vσy=none ae=Ryu <✓) | some w with≡ vσx=somew | new-ub c∈E d∈E _ v≠t ac=Rxv ad=Rxt c<e d<e | refl = CONTRADICTION (v≠t refl)

  this {P} {load r := x ∙ C} (load P′∈⟦C⟧ E′⊆E ≤′⊆≤ ≤⊆≤′ a′⊆a P✓) (segv-store x₂ x₃ x₄) | some w with≡ vσx=somew = {!!} where

  this {P} {load r := x ∙ C} {σ} {σ′} (load P′∈⟦C⟧ E′⊆E ≤′⊆≤ ≤⊆≤′ a′⊆a P✓) (ok x₁ x₂ x₃ x₄) | some w with≡ vσx=somew = {!!}
  
----------------------

  that : ∀ {P C} → (∀ {σ σ′} → (⟪ σ ⟫ P ⟪ σ′ ⟫) → (⟨ σ ⟩ C ⟨ σ′ ⟩)) → (P ∈ ⟦ C ⟧) 

  that {P} {C = exit} σPσ′⇒σCσ′ = exit E=∅ where

     open Pomset P

     σ : Store
     σ x = (ro , none)

     σ′ : Store
     σ′ x = (rw , none)

     ¬σCσ′ : (⟨ σ ⟩ exit ⟨ σ′ ⟩) → ∀ x → FALSE
     ¬σCσ′ (done σ≡σ′) x with σ≡σ′ {x}
     ¬σCσ′ (done σ≡σ′) x | ()
     ¬σCσ′ (step () _)
     
     E=∅ : ∀ {e} → (e ∉ E)
     E=∅ {e} e∈E with inspect (act ℓ(e))
     E=∅ {e} e∈E | (R x v) with≡ ae=Rxv = ¬σCσ′ (σPσ′⇒σCσ′ (segv-load e∈E refl ae=Rxv {!!})) x
     E=∅ {e} e∈E | (W x v) with≡ ae=Wxv = ¬σCσ′ (σPσ′⇒σCσ′ (segv-store e∈E refl ae=Wxv)) x     

  that {P} {C = (load r := x ∙ C)} σPσ′⇒σCσ′ = {!!}
    
----------------------

  theorem : ∀ {C D} → (C ≲ D) → (⟦ D ⟧ ⊆ ⟦ C ⟧)
  theorem C≲D P∈⟦D⟧ = that (λ H → C≲D (this P∈⟦D⟧ H))
  
----------------------
