open import prelude
open import data-model using (MemoryModel)
import command
import pomset
import seqcomp
import parcomp

module semantics (Event : Set) (MM : MemoryModel(Event)) where

  open MemoryModel MM
  open data-model(Event)
  open command(Event)(MM)
  open pomset(Event)(DM)
  open seqcomp(Event)(DM)
  open parcomp(Event)(DM)

  -- initial model

  -- κLOAD : Register → Address → Formula
  -- κLOAD r a = Qw[ a ]

  -- τLOAD : Register → Address → Value → Formula → Formula
  -- τLOAD r a v ϕ = (value v == register r) ⇒ ϕ[r/x]

  -- τLOAD∅ : Register → Address → AccessMode → Value → Formula → Formula
  -- τLOAD∅ r a rlx v ϕ =  ¬ Q[ a ]  ∧ (((value v == register r) ∨ ([ a ]== register r)) ⇒ ϕ[r/x])
  -- τLOAD∅ r a ra  v ϕ  = false


  -- κSTORE : Address → Expression → AccessMode → Value → Formula
  -- κSTORE a M rlx v = Q[ a ] ∧ (M == value v)
  -- κSTORE a M ra v =  Q ∧ (M == value v)

  -- τSTORE : Address → Expression → AccessMode → Formula → Formula
  -- τSTORE a M μ ϕ = ϕ [ M /[ a ]]

  -- τSTORE∅ : Address → Expression → AccessMode → Formula → Formula
  -- τSTORE∅ a M μ ϕ = ¬ Qw[ a ] ∧ (ϕ [ M /[ a ]] )

  κLOAD : Expression → Address → Value → Formula
  κLOAD L a v = (L == address a) ∧ RO ∧ Qw[ a ]

  τLOADD : Register → Event → Value → Formula → Formula
  τLOADD r e v ϕ = (value v == register r[ e ]) ⇒ (ϕ [ register r[ e ] / r ])

  τLOADI : Register → Expression → Event → Address → AccessMode → Formula → Formula
  τLOADI r L e a rlx ϕ =          ¬ Q[ a ] ∧ (RW ⇒ (L == address a) ⇒ ([ a ]== register r[ e ]) ⇒ (ϕ [ register r[ e ] / r ]))
  τLOADI r L e a ra  ϕ = ↓[ a ] ∧ ¬ Q[ a ] ∧ (RW ⇒ (L == address a) ⇒ ([ a ]== register r[ e ]) ⇒ (ϕ [ register r[ e ] / r ]))

  record LOAD (r : Register) (L : Expression) (μ : AccessMode) (P : PomsetWithPredicateTransformers) : Set₁ where

    open PomsetWithPredicateTransformers P

    field a : Event → Address
    field v : Event → Value
    field ψ : Event → Formula

    field d=e : ∀ d e → (d ∈ E) → (e ∈ E) → ((ψ(d) ∧ ψ(e)) ∈ Satisfiable) → (d ≡ e)
    field ℓ=Rav : ∀ e → (e ∈ E) → ℓ(e) ≡ (R (a(e)) (v(e)))
    field κ⊨κLOAD :  ∀ e → (e ∈ E) → κ(e) ⊨ (ψ(e) ∧ κLOAD L (a(e)) (v(e)))
    field τC⊨τLOADD : ∀ C ϕ e → (e ∈ E) → (e ∈ C) → (τ(C)(ϕ) ⊨ (ψ(e) ⇒ τLOADD r e (v(e)) ϕ))
    field τC⊨τLOADI : ∀ C ϕ a e → (e ∈ E) → (e ∉ C) → (τ(C)(ϕ) ⊨ (ψ(e) ⇒ τLOADI r L e a μ ϕ))
    -- TODO field τ∅⊨τLOADI : ∀ ϕ a v → (τ(∅)(ϕ) ⊨ τLOADI r L a rlx v ϕ)

  κSTORE : Expression → AccessMode → Expression → Address → Value → Formula
  κSTORE L rlx M a v = (L == address a) ∧ (M == value v) ∧ RW ∧ Q[ a ]
  κSTORE L ra  M a v = (L == address a) ∧ (M == value v) ∧ RW ∧ Q

  τSTORED : Expression → AccessMode → Expression → Address → Formula → Formula
  τSTORED L rlx M a ϕ = (L == address a) ⇒ (ϕ [ M /[ a ]] [ tt /↓[ a ]])
  τSTORED L ra  M a ϕ = (L == address a) ⇒ (ϕ [ M /[ a ]] [ ff /↓[*]])

  τSTOREI : Expression → AccessMode → Expression → Address → Formula → Formula
  τSTOREI L rlx M a ϕ = (L == address a) ⇒ ((ϕ [ M /[ a ]] [ tt /↓[ a ]]) ∧ ¬ Qw[ a ])
  τSTOREI L ra  M a ϕ = (L == address a) ⇒ ((ϕ [ M /[ a ]] [ ff /↓[*]]) ∧ ¬ Qw[ a ])

  record STORE (L : Expression) (μ : AccessMode) (M : Expression) (P : PomsetWithPredicateTransformers) : Set₁ where

    open PomsetWithPredicateTransformers P

    field a : Event → Address
    field v : Event → Value
    field ψ : Event → Formula

    field d=e : ∀ d e → (d ∈ E) → (e ∈ E) → ((ψ(d) ∧ ψ(e)) ∈ Satisfiable) → (d ≡ e)
    field ℓ=Wav : ∀ e → (e ∈ E) → ℓ(e) ≡ (W (a(e)) (v(e)))
    field κ⊨κSTORE :  ∀ e → (e ∈ E) → (κ(e) ⊨ (ψ(e) ∧ κSTORE L μ M (a(e)) (v(e))))
    field τC⊨τSTORED : ∀ C ϕ a e → (e ∈ E) → (e ∈ C) → (τ(C)(ϕ) ⊨ (ψ(e) ⇒ τSTORED L μ M a ϕ))
    field τC⊨τSTOREI : ∀ C ϕ a e → (e ∈ E) → (e ∉ C) → (τ(C)(ϕ) ⊨ (ψ(e) ⇒ τSTOREI L μ M a ϕ))
    field τ∅⊨τSTOREI : ∀ ϕ a → (τ(∅)(ϕ) ⊨ τSTOREI L μ M a ϕ)

  record LET (r : Register) (M : Expression) (P : PomsetWithPredicateTransformers) : Set₁ where

    open PomsetWithPredicateTransformers P

    field E⊆∅ :  (E ⊆ ∅)
    field τϕ⊨ϕ[M/r] : ∀ C ϕ → τ(C)(ϕ) ⊨ (ϕ [ M / r ])

  ⟦_⟧ : Command → PomsetWithPredicateTransformers → Set₁
  ⟪_⟫ : ThreadGroup → PomsetWithPreconditions → Set₁

  ⟦ skip ⟧ = SKIP
  ⟦ C₁ ∙ C₂ ⟧ = ⟦ C₁ ⟧ ● ⟦ C₂ ⟧
  ⟦ if ϕ then C₁ else C₂ ⟧ = IF ϕ ⟦ C₁ ⟧ ⟦ C₂ ⟧
  ⟦ r :=[ L ]^ μ ⟧ = LOAD r L μ
  ⟦ [ L ]^ μ := M ⟧ = STORE L μ M
  ⟦ r := M ⟧ = LET r M
  ⟦ fork G ⟧ = FORK ⟪ G ⟫

  ⟪ nil ⟫ = NIL
  ⟪ thread C ⟫ = THREAD ⟦ C ⟧
  ⟪ G₁ ∥ G₂ ⟫ = ⟪ G₁ ⟫ ||| ⟪ G₂ ⟫
  
