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








  κLOAD : Register → Address → Formula
  κLOAD r a = RO ∧ Qw[ a ]
  -- ARM only does this if the value can be read from, so we could very reasonably require that the matching write have the same value as the relaxed read

  τLOAD : Register → Address → Value → Formula → Formula
  τLOAD r a v ϕ = (value v == register r) ⇒ (RW ⇒ (ϕ [ register r /[ a ]]))
  
  τLOAD∅ : Register → Address → AccessMode → Value → Formula → Formula
  τLOAD∅ r a rlx v ϕ  =            (¬ Q[ a ]) ∧ (((value v == register r) ∨ ([ a ]== register r)) ⇒ (RW ⇒ (ϕ [ register r /[ a ]])))
  τLOAD∅ r a ra  v ϕ  = (↓[ a ]) ∧ (¬ Q[ a ]) ∧ (((value v == register r) ∨ ([ a ]== register r)) ⇒ (RW ⇒ (ϕ [ register r /[ a ]])))
  
  -- Note: this semantics assumes registers are fresh, otherwise we need to alpha-convert them.
  record LOAD (r : Register) (a : Address) (μ : AccessMode) (P : PomsetWithPredicateTransformers) : Set₁ where

    open PomsetWithPredicateTransformers P

    field v : Value
  
    field d=e : ∀ d e → (d ∈ E) → (e ∈ E) → (d ≡ e)
    field ℓ=Rav : ∀ e → (e ∈ E) → ℓ(e) ≡ (R a v)
    field κ⊨κLOAD :  ∀ e → (e ∈ E) → κ(e) ⊨ κLOAD r a
    field τ⊨τLOAD : ∀ C ϕ → (τ(C)(ϕ) ⊨ τLOAD r a v ϕ)
    field τ⊨τLOAD∅ : ∀ ϕ → (τ(∅)(ϕ) ⊨ τLOAD∅ r a μ v ϕ)

  κSTORE : Address → Expression → AccessMode → Value → Formula
  κSTORE a M rlx v = (RW ∧ Q[ a ]) ∧ (M == value v)
  κSTORE a M ra v = (RW ∧ Q) ∧ (M == value v)

  τSTORE : Address → Expression → AccessMode → Formula → Formula
  τSTORE a M rlx ϕ = ϕ [ M /[ a ]] [ tt /↓[ a ]] 
  τSTORE a M ra  ϕ = ϕ [ M /[ a ]] [ ff /↓[ a ]] 

  τSTORE∅ : Address → Expression → AccessMode → Formula → Formula
  τSTORE∅ a M rlx ϕ = ¬ Qw[ a ] ∧ (ϕ [ M /[ a ]] [ tt /↓[ a ]])
  τSTORE∅ a M ra  ϕ = ¬ Qw[ a ] ∧ (ϕ [ M /[ a ]] [ ff /↓[ a ]])
  
  record STORE (a : Address) (μ : AccessMode) (M : Expression) (P : PomsetWithPredicateTransformers) : Set₁ where

    open PomsetWithPredicateTransformers P

    field v : Value

    field d=e : ∀ d e → (d ∈ E) → (e ∈ E) → (d ≡ e)
    field ℓ=Wav :  ∀ e → (e ∈ E) → ℓ(e) ≡ (W a v)
    field κ⊨κSTORE :  ∀ e → (e ∈ E) → κ(e) ⊨ κSTORE a M μ v
    field τ⊨τSTORE :  ∀ C ϕ → (τ(C)(ϕ) ⊨ τSTORE a M μ ϕ)
    field τ⊨τSTORE∅ : ∀ ϕ → (τ(∅)(ϕ) ⊨ τSTORE∅ a M μ ϕ)
 
  record LET (r : Register) (M : Expression) (P : PomsetWithPredicateTransformers) : Set₁ where
  
    open PomsetWithPredicateTransformers P

    field E⊆∅ :  (E ⊆ ∅)
    field τϕ⊨ϕ[M/r] : ∀ C ϕ → τ(C)(ϕ) ⊨ (ϕ [ M / r ])

  ⟦_⟧ : Command → PomsetWithPredicateTransformers → Set₁
  ⟪_⟫ : ThreadGroup → PomsetWithPreconditions → Set₁
  
  ⟦ skip ⟧ = SKIP
  ⟦ C₁ ∙ C₂ ⟧ = ⟦ C₁ ⟧ ● ⟦ C₂ ⟧
  ⟦ if ϕ then C₁ else C₂ ⟧ = IF ϕ ⟦ C₁ ⟧ ⟦ C₂ ⟧
  ⟦ r :=[ a ]^ μ ⟧ = LOAD r a μ
  ⟦ [ a ]^ μ := M ⟧ = STORE a μ M
  ⟦ r := M ⟧ = LET r M
  ⟦ fork G ⟧ = FORK ⟪ G ⟫

  ⟪ nil ⟫ = NIL
  ⟪ thread C ⟫ = THREAD ⟦ C ⟧
  ⟪ G₁ ∥ G₂ ⟫ = ⟪ G₁ ⟫ ||| ⟪ G₂ ⟫
  
