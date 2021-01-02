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

  κLOAD : Address → Value → Formula
  κLOAD a v = RO ∧ Qw[ a ]

  τLOADD : Register → Register → Value → Formula → Formula
  τLOADD r s v ϕ = (value v == register s) ⇒ (ϕ [ register s / r ])

  τLOADI : Register → Register → Address → AccessMode → Formula → Formula
  τLOADI r s a rlx ϕ =          ¬ Q[ a ] ∧ (RW ⇒ ([ a ]== register s) ⇒ (ϕ [ register s / r ]))
  τLOADI r s a ra  ϕ = ↓[ a ] ∧ ¬ Q[ a ] ∧ (RW ⇒ ([ a ]== register s) ⇒ (ϕ [ register s / r ]))

  τLOAD∅ : Register → Register → Address → AccessMode → Formula → Formula
  τLOAD∅ r s a rlx ϕ =          ¬ Q[ a ] ∧ (ϕ [ register s / r ])
  τLOAD∅ r s a ra  ϕ = ↓[ a ] ∧ ¬ Q[ a ] ∧  (ϕ [ register s / r ])

  record LOAD (r : Register) (L : Expression) (μ : AccessMode) (P : PomsetWithPredicateTransformers) : Set₁ where

    open PomsetWithPredicateTransformers P

    field a : Event → Address
    field v : Event → Value
    field ψ : Event → Formula

    field d=e : ∀ d e → (d ∈ E) → (e ∈ E) → ((ψ(d) ∧ ψ(e)) ∈ Satisfiable) → (d ≡ e)
    field ℓ=Rav : ∀ e → (e ∈ E) → ℓ(e) ≡ (R (a(e)) (v(e)))
    field κ⊨κLOAD :  ∀ e → (e ∈ E) → κ(e) ⊨ (ψ(e) ∧ (L == address (a(e))) ∧ κLOAD (a(e)) (v(e)))
    field τC⊨τLOADD : ∀ C ϕ e → (e ∈ E) → (e ∈ C) → (τ(C)(ϕ) ⊨ (ψ(e) ⇒ τLOADD r (r[ e ]) (v(e)) ϕ))
    field τC⊨τLOADI : ∀ C ϕ a e → (e ∈ E) → (e ∉ C) → (τ(C)(ϕ) ⊨ (ψ(e) ⇒ (L == address a) ⇒ τLOADI r (r[ e ]) a μ ϕ))
    field τC⊨τLOAD∅ : ∀ C ϕ a s χ → (∀ e → (e ∈ E) → (e ∈ C) → (χ ⊨ ¬(ψ(e)))) → (τ(C)(ϕ) ⊨ (χ ⇒ (L == address a) ⇒ τLOAD∅ r s a μ ϕ))

  κSTORE : AccessMode → Expression → Address → Value → Formula
  κSTORE rlx M a v = (M == value v) ∧ RW ∧ Q[ a ]
  κSTORE ra  M a v = (M == value v) ∧ RW ∧ Q

  τSTORED : AccessMode → Expression → Address → Value → Formula → Formula
  τSTORED rlx M a v ϕ = (Qw[ a ] ⇒ (M == value v)) ∧ (ϕ [ M /[ a ]] [ tt /↓[ a ]])
  τSTORED ra  M a v ϕ = (Qw[ a ] ⇒ (M == value v)) ∧ (ϕ [ M /[ a ]] [ ff /↓[*]])

  τSTOREI : AccessMode → Expression → Address → Formula → Formula
  τSTOREI rlx M a ϕ = (¬ Qw[ a ]) ∧ (ϕ [ M /[ a ]] [ tt /↓[ a ]])
  τSTOREI ra  M a ϕ = (¬ Qw[ a ]) ∧ (ϕ [ M /[ a ]] [ ff /↓[*]])

  record STORE (L : Expression) (μ : AccessMode) (M : Expression) (P : PomsetWithPredicateTransformers) : Set₁ where

    open PomsetWithPredicateTransformers P

    field a : Event → Address
    field v : Event → Value
    field ψ : Event → Formula

    field d=e : ∀ d e → (d ∈ E) → (e ∈ E) → ((ψ(d) ∧ ψ(e)) ∈ Satisfiable) → (d ≡ e)
    field ℓ=Wav : ∀ e → (e ∈ E) → ℓ(e) ≡ (W (a(e)) (v(e)))
    field κ⊨κSTORE :  ∀ e → (e ∈ E) → (κ(e) ⊨ (ψ(e) ∧ (L == address (a(e))) ∧ κSTORE μ M (a(e)) (v(e))))
    field τC⊨τSTORED : ∀ C ϕ a e → (e ∈ E) → (e ∈ C) → (τ(C)(ϕ) ⊨ (ψ(e) ⇒ (L == address a) ⇒ τSTORED μ M a (v(e)) ϕ))
    field τC⊨τSTOREI : ∀ C ϕ a χ → (∀ e → (e ∈ E) → (e ∈ C) → (χ ⊨ ¬(ψ(e)))) → (τ(C)(ϕ) ⊨ (χ ⇒ (L == address a) ⇒ τSTOREI μ M a ϕ))

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
  
