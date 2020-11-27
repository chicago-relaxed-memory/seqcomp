open import prelude
open import data-model
import command
import pomset
import seqcomp
import parcomp
import semantics

module augmentation (MM : MemoryModel) (Event : Set) where

  open MemoryModel MM
  open command(MM)
  open pomset(DM)(Event)
  open seqcomp(DM)(Event)
  open parcomp(DM)(Event)
  open semantics(MM)(Event)

  record _≲p_ (P P′ : PomsetWithPreconditions) : Set₁ where

    open PomsetWithPreconditions P using (E ; act ; pre ; _≤_ ; ↓)
    open PomsetWithPreconditions P′ using () renaming (E to E′ ; act to act′ ; pre to pre′ ; _≤_ to _≤′_; ≤-refl to ≤′-refl ; ↓ to ↓′)

    field E′⊆E : (E′ ⊆ E)
    field E⊆E′ : (E ⊆ E′)
    field act=act′ : ∀ e → (e ∈ E) → (act(e) ≡ act′(e))
    field pre′⊨pre : ∀ e → (e ∈ E) → (pre′(e) ⊨ pre(e))
    field ≤⊆≤′ : ∀ d e → (d ≤ e) → (d ≤′ e)

    ↓⊆↓' : ∀ e → (e ∈ E) → (↓(e) ⊆ ↓′(e))
    ↓⊆↓' e e∈E d (d∈E , d≤e) = (E⊆E′ d d∈E , ≤⊆≤′ d e d≤e)
    
  record _≲τ_ (P P′ : PomsetWithPredicateTransformers) : Set₁ where

    open PomsetWithPredicateTransformers P using (PwP ; τ)
    open PomsetWithPredicateTransformers P′ using () renaming (PwP to PwP′ ; τ to τ′)

    field PwP≲PwP′ : (PwP ≲p PwP′)
    open _≲p_ PwP≲PwP′ public
    
    field τ′⊨τ : ∀ C ϕ → (τ′(C)(ϕ) ⊨ τ(C)(ϕ))
    
  sem-resp-≲τ : ∀ {P P′} C → (P ≲τ P′) → (P ∈ ⟦ C ⟧) → (P′ ∈ ⟦ C ⟧)
  sem-resp-≲p : ∀ {P P′} G → (P ≲p P′) → (P ∈ ⟪ G ⟫) → (P′ ∈ ⟪ G ⟫)

  sem-resp-≲τ {P₀} {P′₀} skip P₀≲P′₀ P₀∈SKIP = P′₀∈SKIP where

    open SKIP P₀∈SKIP using (E₀⊆∅ ; τ₀ϕ⊨ϕ)
    open _≲τ_ P₀≲P′₀ using () renaming (E′⊆E to E′₀⊆E₀ ; τ′⊨τ to τ′₀⊨τ₀)
      
    P′₀∈SKIP : P′₀ ∈ SKIP
    P′₀∈SKIP = record
                { E₀⊆∅ = λ e e∈E′₀ → E₀⊆∅ e (E′₀⊆E₀ e e∈E′₀)
                ; τ₀ϕ⊨ϕ = λ C ϕ → ⊨-trans (τ′₀⊨τ₀ C ϕ) (τ₀ϕ⊨ϕ C ϕ) }

  sem-resp-≲τ {P₀} {P′₀} (C₁ ∙ C₂) P₀≲P′₀ P₀∈⟦C₁⟧●⟦C₂⟧ = P′₀∈⟦C₁⟧●⟦C₂⟧ where

    open _●_ P₀∈⟦C₁⟧●⟦C₂⟧
    open PomsetWithPredicateTransformers P₁ using () renaming (τ to τ₁ ; τ-resp-⊆ to τ₁-resp-⊆)
    open PomsetWithPredicateTransformers P₂ using () renaming (E to E₂ ; pre to pre₂)
    open PomsetWithPredicateTransformers P₀ using () renaming (↓ to ↓₀)
    open PomsetWithPredicateTransformers P′₀ using () renaming (↓ to ↓′₀)
    open _≲τ_ P₀≲P′₀ using () renaming (E′⊆E to E′₀⊆E₀ ; E⊆E′ to E₀⊆E′₀ ; act=act′ to act₀=act′₀ ; pre′⊨pre to pre′₀⊨pre₀ ; ≤⊆≤′ to ≤₀⊆≤′₀ ; τ′⊨τ to τ′₀⊨τ₀ ; ↓⊆↓' to ↓₀⊆↓'₀) 

    rhs′₀ : Event → Formula
    rhs′₀(e) = τ₁(↓′₀(e))(pre₂(e))
   
    rhs₀⊨rhs′₀ : ∀ e → (e ∈ E₂) → (rhs₀(e) ⊨ rhs′₀(e))
    rhs₀⊨rhs′₀ e e∈E₂ = τ₁-resp-⊆ (↓₀⊆↓'₀ e (E₂⊆E₀ e e∈E₂))
    
    P′₀∈⟦C₁⟧●⟦C₂⟧ : P′₀ ∈ (⟦ C₁ ⟧ ● ⟦ C₂ ⟧)
    P′₀∈⟦C₁⟧●⟦C₂⟧ = record
                      { P₁ = P₁
                      ; P₂ = P₂
                      ; P₁∈𝒫₁ = P₁∈𝒫₁
                      ; P₂∈𝒫₂ = P₂∈𝒫₂
                      ; E₀⊆E₁∪E₂ = λ e e∈E′₀ → E₀⊆E₁∪E₂ e (E′₀⊆E₀ e e∈E′₀)
                      ; E₁⊆E₀ = λ e e∈E₁ → E₀⊆E′₀ e (E₁⊆E₀ e e∈E₁)
                      ; E₂⊆E₀ = λ e e∈E₂ → E₀⊆E′₀ e (E₂⊆E₀ e e∈E₂)
                      ; ≤₁⊆≤₀ = λ d e d≤₁e → ≤₀⊆≤′₀ d e (≤₁⊆≤₀ d e d≤₁e)
                      ; ≤₂⊆≤₀ = λ d e d≤₂e → ≤₀⊆≤′₀ d e (≤₂⊆≤₀ d e d≤₂e)
                      ; coherence = λ d e d∈E₁ e∈E₂ d#e → ≤₀⊆≤′₀ d e (coherence d e d∈E₁ e∈E₂ d#e)
                      ; pre₀⊨lhs₀ = λ e e∈E₁ e∉E₂ → ⊨-trans (pre′₀⊨pre₀ e (E₁⊆E₀ e e∈E₁)) (pre₀⊨lhs₀ e e∈E₁ e∉E₂)
                      ; pre₀⊨rhs₀ = λ e e∉E₁ e∈E₂ → ⊨-trans (pre′₀⊨pre₀ e (E₂⊆E₀ e e∈E₂)) (⊨-trans (pre₀⊨rhs₀ e e∉E₁ e∈E₂) (rhs₀⊨rhs′₀ e  e∈E₂))
                      ; pre₀⊨lhs₀∨rhs₀ = λ e e∈E₁ e∈E₂ → ⊨-trans (pre′₀⊨pre₀ e (E₂⊆E₀ e e∈E₂)) (⊨-trans (pre₀⊨lhs₀∨rhs₀ e e∈E₁ e∈E₂) (⊨-resp-∨ ⊨-refl (rhs₀⊨rhs′₀ e  e∈E₂)))
                      ; act₀=act₁ = λ e e∈E₁ → ≡-trans (≡-symm (act₀=act′₀ e (E₁⊆E₀ e e∈E₁))) (act₀=act₁ e e∈E₁)
                      ; act₀=act₂ =  λ e e∈E₂ → ≡-trans (≡-symm (act₀=act′₀ e (E₂⊆E₀ e e∈E₂))) (act₀=act₂ e e∈E₂)
                      ; τ₀ϕ⊨τ₁τ₂ϕ = λ C ϕ → ⊨-trans (τ′₀⊨τ₀ C ϕ) (τ₀ϕ⊨τ₁τ₂ϕ C ϕ)
                      }
    
  sem-resp-≲τ {P₀} {P′₀} (if ψ then C₁ else C₂) P₀≲P′₀ P₀∈IF = P′₀∈IF where

    open IF P₀∈IF
    open _≲τ_ P₀≲P′₀ using () renaming (E′⊆E to E′₀⊆E₀ ; E⊆E′ to E₀⊆E′₀ ; act=act′ to act₀=act′₀ ; pre′⊨pre to pre′₀⊨pre₀ ; ≤⊆≤′ to ≤₀⊆≤′₀ ; τ′⊨τ to τ′₀⊨τ₀)
    
    P′₀∈IF : P′₀ ∈ (IF ψ ⟦ C₁ ⟧ ⟦ C₂ ⟧)
    P′₀∈IF = record
               { P₁ = P₁
               ; P₂ = P₂
               ; P₁∈𝒫₁ = P₁∈𝒫₁
               ; P₂∈𝒫₂ = P₂∈𝒫₂
               ; E₀⊆E₁∪E₂ = ⊆-trans E′₀⊆E₀ E₀⊆E₁∪E₂
               ; E₁⊆E₀ = ⊆-trans E₁⊆E₀ E₀⊆E′₀
               ; E₂⊆E₀ = ⊆-trans E₂⊆E₀ E₀⊆E′₀
               ; ≤₁⊆≤₀ = λ d e d≤₁e → ≤₀⊆≤′₀ d e (≤₁⊆≤₀ d e d≤₁e)
               ; ≤₂⊆≤₀ = λ d e d≤₂e → ≤₀⊆≤′₀ d e (≤₂⊆≤₀ d e d≤₂e)
               ; pre₀⊨lhs₀ = λ e e∈E₁ e∉E₂ → ⊨-trans (pre′₀⊨pre₀ e (E₁⊆E₀ e e∈E₁)) (pre₀⊨lhs₀ e e∈E₁ e∉E₂)
               ; pre₀⊨rhs₀ = λ e e∉E₁ e∈E₂ → ⊨-trans (pre′₀⊨pre₀ e (E₂⊆E₀ e e∈E₂)) (pre₀⊨rhs₀ e e∉E₁ e∈E₂)
               ; pre₀⊨lhs₀∨rhs₀ =  λ e e∈E₁ e∈E₂ → ⊨-trans (pre′₀⊨pre₀ e (E₂⊆E₀ e e∈E₂)) (pre₀⊨lhs₀∨rhs₀ e e∈E₁ e∈E₂)
               ; act₀=act₁ = λ e e∈E₁ → ≡-trans (≡-symm (act₀=act′₀ e (E₁⊆E₀ e e∈E₁))) (act₀=act₁ e e∈E₁)
               ; act₀=act₂ = λ e e∈E₂ → ≡-trans (≡-symm (act₀=act′₀ e (E₂⊆E₀ e e∈E₂))) (act₀=act₂ e e∈E₂)
               ; τ₀ϕ⊨τ₁ϕ = λ C ϕ → ⊨-trans (⊨-resp-∧ ⊨-refl (τ′₀⊨τ₀ C ϕ)) (τ₀ϕ⊨τ₁ϕ C ϕ)
               ; τ₀ϕ⊨τ₂ϕ =  λ C ϕ → ⊨-trans (⊨-resp-∧ ⊨-refl (τ′₀⊨τ₀ C ϕ)) (τ₀ϕ⊨τ₂ϕ C ϕ)
               }


  sem-resp-≲τ {P} {P′} (r :=[ a ]^ μ) P≲P′ P∈LOAD = P′∈LOAD where

    open LOAD P∈LOAD
    open _≲τ_ P≲P′

    P′∈LOAD : P′ ∈ LOAD r a μ
    P′∈LOAD = record
                { v = v
                ; d=e = λ d e d∈E′ e∈E′ → d=e d e (E′⊆E d d∈E′) (E′⊆E e e∈E′)
                ; act=Rav = λ e e∈E′ → ≡-trans (≡-symm (act=act′ e (E′⊆E e e∈E′))) (act=Rav e (E′⊆E e e∈E′))
                ; τϕ⊨ϕ[v/r] = λ C ϕ → ⊨-trans (τ′⊨τ C ϕ) (τϕ⊨ϕ[v/r] C ϕ)
                ; τϕ⊨ϕ[[a]/r] = λ ϕ → ⊨-trans (τ′⊨τ ∅ ϕ) (τϕ⊨ϕ[[a]/r] ϕ)
                ; τϕ⊨ff = λ μ=ra ϕ → ⊨-trans (τ′⊨τ ∅ ϕ) (τϕ⊨ff μ=ra ϕ)
                }

  sem-resp-≲τ {P} {P′} ([ a ]^ μ := M) P≲P′ P∈STORE = P′∈STORE where

    open STORE P∈STORE
    open _≲τ_ P≲P′

    P′∈STORE : P′ ∈ STORE a μ M
    P′∈STORE = record
                { v = v
                ; d=e = λ d e d∈E′ e∈E′ → d=e d e (E′⊆E d d∈E′) (E′⊆E e e∈E′)
                ; act=Wav = λ e e∈E′ → ≡-trans (≡-symm (act=act′ e (E′⊆E e e∈E′))) (act=Wav e (E′⊆E e e∈E′))
                ; pre⊨M=v = λ e e∈E′ → ⊨-trans (pre′⊨pre e (E′⊆E e e∈E′)) (pre⊨M=v e (E′⊆E e e∈E′))
                ; τϕ⊨ϕ[M/[a]] = λ C ϕ → ⊨-trans (τ′⊨τ C ϕ) (τϕ⊨ϕ[M/[a]] C ϕ)
                ; pre⊨Q = λ μ=ra e e∈E′ → ⊨-trans (pre′⊨pre e (E′⊆E e e∈E′)) (pre⊨Q μ=ra e (E′⊆E e e∈E′))
                ; τϕ⊨ϕ[M/[a]][ff/Q] = λ μ=ra ϕ → ⊨-trans (τ′⊨τ ∅ ϕ) (τϕ⊨ϕ[M/[a]][ff/Q] μ=ra ϕ)
                }
                
  sem-resp-≲τ {P} {P′} (r := M) P≲P′ P∈LET = P′∈LET where
    
    open LET P∈LET
    open _≲τ_ P≲P′

    P′∈LET : P′ ∈ LET r M
    P′∈LET = record
              { E⊆∅ = ⊆-trans E′⊆E E⊆∅
              ; τϕ⊨ϕ[M/r] = λ C ϕ → ⊨-trans (τ′⊨τ C ϕ) (τϕ⊨ϕ[M/r] C ϕ)
              }

  sem-resp-≲τ {P₀} {P′₀} (fork G) P₀≲P′₀ P₀∈FORK = P′₀∈FORK where

    open FORK P₀∈FORK
    open _≲τ_ P₀≲P′₀ using () renaming (E′⊆E to E′₀⊆E₀ ; E⊆E′ to E₀⊆E′₀ ; act=act′ to act₀=act′₀ ; pre′⊨pre to pre′₀⊨pre₀ ; ≤⊆≤′ to ≤₀⊆≤′₀ ; τ′⊨τ to τ′₀⊨τ₀)
    
    P′₀∈FORK : P′₀ ∈ FORK ⟪ G ⟫
    P′₀∈FORK = record
                  { P₁ = P₁
                  ; P₁∈𝒫 = P₁∈𝒫
                  ; E₁⊆E₀ = ⊆-trans E₁⊆E₀ E₀⊆E′₀
                  ; E₀⊆E₁ = ⊆-trans E′₀⊆E₀ E₀⊆E₁
                  ; ≤₁⊆≤₀ = λ d e d≤₁e → ≤₀⊆≤′₀ d e (≤₁⊆≤₀ d e d≤₁e)
                  ; pre₀⊨pre₁[tt/Q] = λ e e∈E₁ → ⊨-trans (pre′₀⊨pre₀ e (E₁⊆E₀ e e∈E₁)) (pre₀⊨pre₁[tt/Q] e e∈E₁)
                  ; act₀=act₁ = λ e e∈E₁ → ≡-trans (≡-symm (act₀=act′₀ e (E₁⊆E₀ e e∈E₁))) (act₀=act₁ e e∈E₁)
                  ; τ₀ϕ⊨ϕ = λ C ϕ → ⊨-trans (τ′₀⊨τ₀ C ϕ) (τ₀ϕ⊨ϕ C ϕ)
                  }

  sem-resp-≲p {P} {P′} nil P≲P′ P∈NIL = P′∈NIL where

    open NIL P∈NIL
    open _≲p_ P≲P′
    
    P′∈NIL : P′ ∈ NIL
    P′∈NIL = record { E₀⊆∅ = ⊆-trans E′⊆E E₀⊆∅ }
    
  sem-resp-≲p {P₀} {P′₀} (thread C) P₀≲P′₀ P₀∈THREAD = P′₀∈THREAD where

    open THREAD P₀∈THREAD
    open _≲p_ P₀≲P′₀ using () renaming (E′⊆E to E′₀⊆E₀ ; E⊆E′ to E₀⊆E′₀ ; act=act′ to act₀=act′₀ ; pre′⊨pre to pre′₀⊨pre₀ ; ≤⊆≤′ to ≤₀⊆≤′₀) 
    
    P′₀∈THREAD : P′₀ ∈ THREAD ⟦ C ⟧
    P′₀∈THREAD = record
                  { P₁ = P₁
                  ; P₁∈𝒫 = P₁∈𝒫
                  ; E₁⊆E₀ = ⊆-trans E₁⊆E₀ E₀⊆E′₀
                  ; E₀⊆E₁ = ⊆-trans E′₀⊆E₀ E₀⊆E₁
                  ; ≤₁⊆≤₀ = λ d e d≤₁e → ≤₀⊆≤′₀ d e (≤₁⊆≤₀ d e d≤₁e)
                  ; pre₀⊨pre₁ = λ e e∈E₁ → ⊨-trans (pre′₀⊨pre₀ e (E₁⊆E₀ e e∈E₁)) (pre₀⊨pre₁ e e∈E₁)
                  ; act₀=act₁ = λ e e∈E₁ → ≡-trans (≡-symm (act₀=act′₀ e (E₁⊆E₀ e e∈E₁))) (act₀=act₁ e e∈E₁)
                  }
    
  sem-resp-≲p {P₀} {P′₀} (G₁ ∥ G₂) P₀≲P′₀ P₀∈⟪G₁⟫|||⟪G₂⟫ = P′₀∈⟪G₁⟫|||⟪G₂⟫ where

    open _|||_ P₀∈⟪G₁⟫|||⟪G₂⟫
    open _≲p_ P₀≲P′₀ using () renaming (E′⊆E to E′₀⊆E₀ ; E⊆E′ to E₀⊆E′₀ ; act=act′ to act₀=act′₀ ; pre′⊨pre to pre′₀⊨pre₀ ; ≤⊆≤′ to ≤₀⊆≤′₀) 

    P′₀∈⟪G₁⟫|||⟪G₂⟫ : P′₀ ∈ (⟪ G₁ ⟫ ||| ⟪ G₂ ⟫)
    P′₀∈⟪G₁⟫|||⟪G₂⟫ = record
                        { P₁ = P₁
                        ; P₂ = P₂
                        ; P₁∈𝒫₁ = P₁∈𝒫₁
                        ; P₂∈𝒫₂ = P₂∈𝒫₂
                        ; E₀⊆E₁⊎E₂ = ⊆-trans E′₀⊆E₀ E₀⊆E₁⊎E₂
                        ; E₁⊆E₀ = ⊆-trans E₁⊆E₀ E₀⊆E′₀
                        ; E₂⊆E₀ = ⊆-trans E₂⊆E₀ E₀⊆E′₀
                        ; E₁∩E₂⊆∅ = E₁∩E₂⊆∅
                        ; ≤₁⊆≤₀ = λ d e d≤₁e → ≤₀⊆≤′₀ d e (≤₁⊆≤₀ d e d≤₁e)
                        ; ≤₂⊆≤₀ = λ d e d≤₂e → ≤₀⊆≤′₀ d e (≤₂⊆≤₀ d e d≤₂e)
                        ; pre₀⊨pre₁ = λ e e∈E₁ → ⊨-trans (pre′₀⊨pre₀ e (E₁⊆E₀ e e∈E₁)) (pre₀⊨pre₁ e e∈E₁)
                        ; pre₀⊨pre₂ = λ e e∈E₂ → ⊨-trans (pre′₀⊨pre₀ e (E₂⊆E₀ e e∈E₂)) (pre₀⊨pre₂ e e∈E₂)
                        ; act₀=act₁ =  λ e e∈E₁ → ≡-trans (≡-symm (act₀=act′₀ e (E₁⊆E₀ e e∈E₁))) (act₀=act₁ e e∈E₁)
                        ; act₀=act₂ = λ e e∈E₂ → ≡-trans (≡-symm (act₀=act′₀ e (E₂⊆E₀ e e∈E₂))) (act₀=act₂ e e∈E₂)
                        }
    
    
