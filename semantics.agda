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
   
  record LOAD (r : Register) (a : Address) (μ : AccessMode) (P : PomsetWithPredicateTransformers) : Set₁ where

    open PomsetWithPredicateTransformers P

    field v : Value

    field d=e : ∀ d e → (d ∈ E) → (e ∈ E) → (d ≡ e)
    field act=Rav : ∀ e → (e ∈ E) → act(e) ≡ (R a v)
    field pre⊨RO :  ∀ e → (e ∈ E) → pre(e) ⊨ RO
    field pre⊨Q[a] : ∀ e → (e ∈ E) → (pre(e) ⊨ Q[ a ])
    field τϕ⊨ϕ[v/r] : ∀ C ϕ → (τ(C)(ϕ) ⊨ (ϕ [ value v / r ]))
    field τϕ⊨RO∨ϕ[[a]/r][ff/Q] : ∀ ϕ → (τ(∅)(ϕ) ⊨ (RO ∨ (ϕ [[ a ]/ r ] [ ff /Q])))

    field τϕ⊨μ[a]=rlx : (μ ≡ ra) → ∀ ϕ → (τ(∅)(ϕ) ⊨ (μ[ a ]==rlx))

  record STORE (a : Address) (μ : AccessMode) (M : Expression) (P : PomsetWithPredicateTransformers) : Set₁ where

    open PomsetWithPredicateTransformers P

    field v : Value

    field d=e : ∀ d e → (d ∈ E) → (e ∈ E) → (d ≡ e)
    field act=Wav :  ∀ e → (e ∈ E) → act(e) ≡ (W a v)
    field pre⊨M=v :  ∀ e → (e ∈ E) → pre(e) ⊨ (M == value v)
    field pre⊨RW :  ∀ e → (e ∈ E) → pre(e) ⊨ RW
    field pre⊨Q[a] : ∀ e → (e ∈ E) → (pre(e) ⊨ Q[ a ])
    field τϕ⊨ϕ[M/[a]][μ/μ[a]][Q[a]∧M=v/Q[a]] : ∀ C ϕ → (τ(C)(ϕ) ⊨ (ϕ [ M /[ a ]] [ μ /μ[ a ]] [ (Q[ a ] ∧ (M == value v)) /Q[ a ]])) 
    field τϕ⊨ϕ[M/[a]][μ/μ[a]][ff/Q[a]] : ∀ ϕ → (τ(∅)(ϕ) ⊨ (ϕ [ M /[ a ]] [ μ /μ[ a ]] [ ff /Q[ a ]])) 
    
    field pre⊨Q : (μ ≡ ra) → ∀ e → (e ∈ E) → (pre(e) ⊨ Q)
 
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
  
