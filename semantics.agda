open import prelude
open import data-model
import command
import pomset
import seqcomp
import parcomp

module semantics (MM : MemoryModel) (Event : Set) where

  open MemoryModel MM
  open command(MM)
  open pomset(DM)(Event)
  open seqcomp(DM)(Event)
  open parcomp(DM)(Event)

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








  κLOAD : Expression → Cached → Address → Value → Formula
  κLOAD L hit  a v = (L == address a) ∧ RO ∧ Qw[ a ] ∧ ([ a ]== value v)
  κLOAD L miss a v = (L == address a) ∧ RO ∧ Qw[ a ]
  -- ARM only does this if the value can be read from, so we could very reasonably require that the matching write have the same value as the relaxed read

  τLOADD : Register → Expression → Cached → Address → Value → Formula → Formula
  τLOADD r L hit  a v ϕ = (L == address a) ⇒ RW ⇒ (([ a ]== register r) ∧ (value v == register r)) ⇒ (ϕ [ register r /[ a ]])
  τLOADD r L miss a v ϕ = (L == address a) ⇒ RW ⇒                         (value v == register r)  ⇒ (ϕ [ register r /[ a ]])

  τLOADI : Register → Expression → Cached → Address → AccessMode → Value → Formula → Formula
  τLOADI r L hit  a rlx v ϕ =            ¬ Q[ a ] ∧ ((L == address a) ⇒ RW ⇒ (([ a ]== register r)                          ) ⇒ (ϕ [ register r /[ a ]]))
  τLOADI r L miss a rlx v ϕ =            ¬ Q[ a ] ∧ ((L == address a) ⇒ RW ⇒ (([ a ]== register r) ∨ (value v == register r)) ⇒ (ϕ [ register r /[ a ]]))
  τLOADI r L hit  a ra  v ϕ = (↓[ a ]) ∧ ¬ Q[ a ] ∧ ((L == address a) ⇒ RW ⇒ (([ a ]== register r)                          ) ⇒ (ϕ [ register r /[ a ]]))
  τLOADI r L miss a ra  v ϕ = ff 

  -- Note: this semantics assumes registers are fresh, otherwise we need to alpha-convert them.
  record LOAD (r : Register) (L : Expression) (μ : AccessMode) (P : PomsetWithPredicateTransformers) : Set₁ where

    open PomsetWithPredicateTransformers P

    field a : Event → Address
    field c : Event → Cached
    field v : Event → Value
    field ψ : Event → Formula

    field d=e : ∀ d e → (d ∈ E) → (e ∈ E) → ((ψ(d) ∧ ψ(e)) ∈ Satisfiable) → (d ≡ e)
    field ℓ=Rav : ∀ e → (e ∈ E) → ℓ(e) ≡ (R (c(e)) (a(e)) (v(e)))
    field κ⊨κLOAD :  ∀ e → (e ∈ E) → κ(e) ⊨ (ψ(e) ∧ κLOAD L (c(e)) (a(e)) (v(e)))
    field τC⊨τLOADD : ∀ C ϕ a e → (e ∈ E) → (e ∈ C) → (τ(C)(ϕ) ⊨ (ψ(e) ⇒ τLOADD r L (c(e)) a (v(e)) ϕ))
    field τC⊨τLOADI : ∀ C ϕ a e → (e ∈ E) → (e ∉ C) → (τ(C)(ϕ) ⊨ (ψ(e) ⇒ τLOADI r L (c(e)) a μ (v(e)) ϕ))
    field τ∅⊨τLOADI : ∀ ϕ a v → (τ(∅)(ϕ) ⊨ τLOADI r L hit a rlx v ϕ)

  κSTORE : Expression → AccessMode → Expression → Address → Value → Formula
  κSTORE L rlx M a v = (L == address a) ∧ (M == value v) ∧ RW ∧ Q[ a ]
  κSTORE L ra  M a v = (L == address a) ∧ (M == value v) ∧ RW ∧ Q

  τSTORED : Expression → AccessMode → Expression → Address → Formula → Formula
  τSTORED L rlx M a ϕ = (L == address a) ⇒ (ϕ [ M /[ a ]] [ tt /↓[ a ]])
  τSTORED L ra  M a ϕ = (L == address a) ⇒ (ϕ [ M /[ a ]] [ ff /↓[ a ]])

  τSTOREI : Expression → AccessMode → Expression → Address → Formula → Formula
  τSTOREI L rlx M a ϕ = (L == address a) ⇒ ((ϕ [ M /[ a ]] [ tt /↓[ a ]]) ∧ ¬ Qw[ a ])
  τSTOREI L ra  M a ϕ = (L == address a) ⇒ ((ϕ [ M /[ a ]] [ ff /↓[ a ]]) ∧ ¬ Qw[ a ])

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
  
