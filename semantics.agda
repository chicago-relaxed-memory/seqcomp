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
   
  record LOAD (r : Register) (a : Address)  (P : PomsetWithPredicateTransformers) : Set₁ where

    open PomsetWithPredicateTransformers P

    field v : Value

    field d=e : ∀ d e → (d ∈ E) → (e ∈ E) → (d ≡ e)
    field act=Rav : ∀ e → (e ∈ E) → act(e) ≡ (R a v)
    field τϕ⊨ϕ[v/r] : ∀ ϕ C → (τ(C)(ϕ) ⊨ (ϕ [ value v / r ]))
    field τϕ⊨ϕ[[a]/r] : ∀ ϕ C → ((C ∩ E) ⊆ ∅) → (τ(C)(ϕ) ⊨ (ϕ [[ a ]/ r ]))
    
  record STORE (a : Address) (M : Expression) (P : PomsetWithPredicateTransformers) : Set₁ where

    open PomsetWithPredicateTransformers P

    field v : Value

    field d=e : ∀ d e → (d ∈ E) → (e ∈ E) → (d ≡ e)
    field act=Wav :  ∀ e → (e ∈ E) → act(e) ≡ (W a v)
    field pre⊨M=v :  ∀ e → (e ∈ E) → pre(e) ⊨ (M == value v)
    field τϕ⊨ϕ[v/[a]] : ∀ C ϕ → (τ(C)(ϕ) ⊨ (ϕ [ M /[ a ]])) 
 
  record LET (r : Register) (M : Expression) (P : PomsetWithPredicateTransformers) : Set₁ where
  
    open PomsetWithPredicateTransformers P

    field E⊆∅ :  (E ⊆ ∅)
    field τϕ⊨ϕ[M/r] : ∀ C ϕ → τ(C)(ϕ) ⊨ (ϕ [ M / r ])
   
  ⟦_⟧ : Command → PomsetWithPredicateTransformers → Set₁
  ⟪_⟫ : ThreadGroup → PomsetWithPreconditions → Set₁
  
  ⟦ skip ⟧ = SKIP
  ⟦ C₁ ∙ C₂ ⟧ = ⟦ C₁ ⟧ ● ⟦ C₂ ⟧
  ⟦ if ϕ then C₁ else C₂ ⟧ = IF ϕ ⟦ C₁ ⟧ ⟦ C₂ ⟧
  ⟦ r :=[ a ] ⟧ = LOAD r a
  ⟦ [ a ]:= M ⟧ = STORE a M
  ⟦ r := M ⟧ = LET r M
  ⟦ fork G ⟧ = FORK ⟪ G ⟫

  ⟪ nil ⟫ = NIL
  ⟪ thread C ⟫ = THREAD ⟦ C ⟧
  ⟪ G₁ ∥ G₂ ⟫ = ⟪ G₁ ⟫ ||| ⟪ G₂ ⟫
  
