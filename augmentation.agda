open import prelude
open import data-model
import command
import pomset
import seqcomp
import parcomp
import semantics

module augmentation (Event : Set) (MM : MemoryModel(Event)) where

  open MemoryModel MM
  open command(Event)(MM)
  open pomset(Event)(DM)
  open seqcomp(Event)(DM)
  open parcomp(Event)(DM)
  open semantics(Event)(MM)

  record _≲_ (P P′ : PomsetWithPredicateTransformers) : Set₁ where

    open PomsetWithPredicateTransformers P using (E ; ℓ ; κ ; _≤_ ; ↓ ; τ ; ✓)
    open PomsetWithPredicateTransformers P′ using () renaming (E to E′ ; ℓ to ℓ′ ; κ to κ′ ; _≤_ to _≤′_; ≤-refl to ≤′-refl ; ↓ to ↓′ ; τ to τ′ ; ✓ to ✓′)

    field E′⊆E : (E′ ⊆ E)
    field E⊆E′ : (E ⊆ E′)
    field ℓ=ℓ′ : ∀ e → (e ∈ E) → (ℓ(e) ≡ ℓ′(e))
    field κ′⊨κ : ∀ e → (e ∈ E) → (κ′(e) ⊨ κ(e))
    field τ′⊨τ : ∀ C ϕ → (τ′(C)(ϕ) ⊨ τ(C)(ϕ))
    field ✓′⊨✓ : (✓′ ⊨ ✓)
    field ≤⊆≤′ : ∀ d e → (d ≤ e) → (d ≤′ e)
    
    ↓⊆↓' : ∀ e → (e ∈ E) → (↓(e) ⊆ ↓′(e))
    ↓⊆↓' e e∈E d (d∈E , d≤e) = (E⊆E′ d d∈E , ≤⊆≤′ d e d≤e)
    
  sem-resp-≲ : ∀ {P P′} C → (P ≲ P′) → (P ∈ ⟦ C ⟧) → (P′ ∈ ⟦ C ⟧)

  sem-resp-≲ {P₀} {P′₀} skip P₀≲P′₀ P₀∈SKIP = P′₀∈SKIP where

    open SKIP P₀∈SKIP using (E₀⊆∅ ; τ₀ϕ⊨ϕ)
    open _≲_ P₀≲P′₀ using () renaming (E′⊆E to E′₀⊆E₀ ; τ′⊨τ to τ′₀⊨τ₀)
      
    P′₀∈SKIP : P′₀ ∈ SKIP
    P′₀∈SKIP = record
                { E₀⊆∅ = λ e e∈E′₀ → E₀⊆∅ e (E′₀⊆E₀ e e∈E′₀)
                ; τ₀ϕ⊨ϕ = λ C ϕ → ⊨-trans (τ′₀⊨τ₀ C ϕ) (τ₀ϕ⊨ϕ C ϕ) }

  sem-resp-≲ {P₀} {P′₀} (C₁ ∙ C₂) P₀≲P′₀ P₀∈⟦C₁⟧●⟦C₂⟧ = P′₀∈⟦C₁⟧●⟦C₂⟧ where

    open _●_ P₀∈⟦C₁⟧●⟦C₂⟧
    open PomsetWithPredicateTransformers P₁ using () renaming (τ to τ₁ ; τ-resp-⊆ to τ₁-resp-⊆)
    open PomsetWithPredicateTransformers P₂ using () renaming (E to E₂ ; κ to κ₂)
    open PomsetWithPredicateTransformers P₀ using () renaming (↓ to ↓₀)
    open PomsetWithPredicateTransformers P′₀ using () renaming (↓ to ↓′₀)
    open _≲_ P₀≲P′₀ using () renaming (E′⊆E to E′₀⊆E₀ ; E⊆E′ to E₀⊆E′₀ ; ℓ=ℓ′ to ℓ₀=ℓ′₀ ; κ′⊨κ to κ′₀⊨κ₀ ; ✓′⊨✓ to ✓′₀⊨✓₀ ;  ≤⊆≤′ to ≤₀⊆≤′₀ ; τ′⊨τ to τ′₀⊨τ₀ ; ↓⊆↓' to ↓₀⊆↓'₀) 

    rhs′₀ : Event → Formula
    rhs′₀(e) = τ₁(↓′₀(e))(κ₂(e))
   
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
                      ; κ₀⊨lhs₀ = λ e e∈E₁ e∉E₂ → ⊨-trans (κ′₀⊨κ₀ e (E₁⊆E₀ e e∈E₁)) (κ₀⊨lhs₀ e e∈E₁ e∉E₂)
                      ; κ₀⊨rhs₀ = λ e e∉E₁ e∈E₂ → ⊨-trans (κ′₀⊨κ₀ e (E₂⊆E₀ e e∈E₂)) (⊨-trans (κ₀⊨rhs₀ e e∉E₁ e∈E₂) (rhs₀⊨rhs′₀ e  e∈E₂))
                      ; κ₀⊨lhs₀∨rhs₀ = λ e e∈E₁ e∈E₂ → ⊨-trans (κ′₀⊨κ₀ e (E₂⊆E₀ e e∈E₂)) (⊨-trans (κ₀⊨lhs₀∨rhs₀ e e∈E₁ e∈E₂) (⊨-resp-∨ ⊨-refl (rhs₀⊨rhs′₀ e  e∈E₂)))
                      ; ℓ₀=ℓ₁ = λ e e∈E₁ → ≡-trans (≡-symm (ℓ₀=ℓ′₀ e (E₁⊆E₀ e e∈E₁))) (ℓ₀=ℓ₁ e e∈E₁)
                      ; ℓ₀=ℓ₂ =  λ e e∈E₂ → ≡-trans (≡-symm (ℓ₀=ℓ′₀ e (E₂⊆E₀ e e∈E₂))) (ℓ₀=ℓ₂ e e∈E₂)
                      ; τ₀ϕ⊨τ₁τ₂ϕ = λ C ϕ → ⊨-trans (τ′₀⊨τ₀ C ϕ) (τ₀ϕ⊨τ₁τ₂ϕ C ϕ)
                      ; ✓₀⊨✓₁ = ⊨-trans ✓′₀⊨✓₀ ✓₀⊨✓₁
                      ; ✓₀⊨τ₁✓₂ = ⊨-trans ✓′₀⊨✓₀ ✓₀⊨τ₁✓₂
                      }
    
  sem-resp-≲ {P₀} {P′₀} (if ψ then C₁ else C₂) P₀≲P′₀ P₀∈IF = P′₀∈IF where

    open IF P₀∈IF
    open _≲_ P₀≲P′₀ using () renaming (E′⊆E to E′₀⊆E₀ ; E⊆E′ to E₀⊆E′₀ ; ℓ=ℓ′ to ℓ₀=ℓ′₀ ; κ′⊨κ to κ′₀⊨κ₀ ; ✓′⊨✓ to ✓′₀⊨✓₀ ; ≤⊆≤′ to ≤₀⊆≤′₀ ; τ′⊨τ to τ′₀⊨τ₀)
    
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
               ; κ₀⊨lhs₀ = λ e e∈E₁ e∉E₂ → ⊨-trans (κ′₀⊨κ₀ e (E₁⊆E₀ e e∈E₁)) (κ₀⊨lhs₀ e e∈E₁ e∉E₂)
               ; κ₀⊨rhs₀ = λ e e∉E₁ e∈E₂ → ⊨-trans (κ′₀⊨κ₀ e (E₂⊆E₀ e e∈E₂)) (κ₀⊨rhs₀ e e∉E₁ e∈E₂)
               ; κ₀⊨lhs₀∨rhs₀ =  λ e e∈E₁ e∈E₂ → ⊨-trans (κ′₀⊨κ₀ e (E₂⊆E₀ e e∈E₂)) (κ₀⊨lhs₀∨rhs₀ e e∈E₁ e∈E₂)
               ; ℓ₀=ℓ₁ = λ e e∈E₁ → ≡-trans (≡-symm (ℓ₀=ℓ′₀ e (E₁⊆E₀ e e∈E₁))) (ℓ₀=ℓ₁ e e∈E₁)
               ; ℓ₀=ℓ₂ = λ e e∈E₂ → ≡-trans (≡-symm (ℓ₀=ℓ′₀ e (E₂⊆E₀ e e∈E₂))) (ℓ₀=ℓ₂ e e∈E₂)
               ; τ₀ϕ⊨τ₁ϕ = λ C ϕ → ⊨-trans (⊨-resp-∧ ⊨-refl (τ′₀⊨τ₀ C ϕ)) (τ₀ϕ⊨τ₁ϕ C ϕ)
               ; τ₀ϕ⊨τ₂ϕ =  λ C ϕ → ⊨-trans (⊨-resp-∧ ⊨-refl (τ′₀⊨τ₀ C ϕ)) (τ₀ϕ⊨τ₂ϕ C ϕ)
               ; ψ∧✓₀⊨✓₁ = ⊨-trans (⊨-resp-∧ ⊨-refl ✓′₀⊨✓₀) ψ∧✓₀⊨✓₁
               ; ¬ψ∧✓₀⊨✓₂ = ⊨-trans (⊨-resp-∧ ⊨-refl ✓′₀⊨✓₀) ¬ψ∧✓₀⊨✓₂
               }


  sem-resp-≲ {P} {P′} (r :=[ L ]^ μ) P≲P′ P∈LOAD = P′∈LOAD where

    open LOAD P∈LOAD
    open _≲_ P≲P′

    P′∈LOAD : P′ ∈ LOAD r L μ
    P′∈LOAD = record
                { v = v
                ; d=e = λ d e d∈E′ e∈E′ → d=e d e (E′⊆E d d∈E′) (E′⊆E e e∈E′)
                ; ℓ=Rav = λ e e∈E′ → ≡-trans (≡-symm (ℓ=ℓ′ e (E′⊆E e e∈E′))) (ℓ=Rav e (E′⊆E e e∈E′))
                ; κ⊨κLOAD = λ e e∈E′ → ⊨-trans (κ′⊨κ e (E′⊆E e e∈E′)) (κ⊨κLOAD e (E′⊆E e e∈E′))
                ; τC⊨τLOADD = λ C ϕ a e e∈E′ e∈C → ⊨-trans (τ′⊨τ C ϕ) (τC⊨τLOADD C ϕ a e (E′⊆E e e∈E′) e∈C)
                ; τC⊨τLOADI = λ C ϕ a e e∈E′ e∉C → ⊨-trans (τ′⊨τ C ϕ) (τC⊨τLOADI C ϕ a e (E′⊆E e e∈E′) e∉C)
                ; τC⊨τLOAD∅ = λ C ϕ a s χ χ⊨¬ψ → ⊨-trans (τ′⊨τ C ϕ) (τC⊨τLOAD∅ C ϕ a s χ (λ e e∈E → χ⊨¬ψ e (E⊆E′ e e∈E)))
                ; ✓LOAD = λ χ χ⊨¬ψ μ≠rlx → ⊨-trans ✓′⊨✓ (✓LOAD χ (λ e e∈E → χ⊨¬ψ e (E⊆E′ e e∈E)) μ≠rlx)
                }

  sem-resp-≲ {P} {P′} ([ L ]^ μ := M) P≲P′ P∈STORE = P′∈STORE where

    open STORE P∈STORE
    open _≲_ P≲P′

    P′∈STORE : P′ ∈ STORE L μ M
    P′∈STORE = record
                { v = v
                ; d=e = λ d e d∈E′ e∈E′ → d=e d e (E′⊆E d d∈E′) (E′⊆E e e∈E′)
                ; ℓ=Wav = λ e e∈E′ → ≡-trans (≡-symm (ℓ=ℓ′ e (E′⊆E e e∈E′))) (ℓ=Wav e (E′⊆E e e∈E′))
                ; κ⊨κSTORE = λ e e∈E′ → ⊨-trans (κ′⊨κ e (E′⊆E e e∈E′)) (κ⊨κSTORE e (E′⊆E e e∈E′))
                ; τC⊨τSTORED = λ C ϕ a e e∈E′ e∈C → ⊨-trans (τ′⊨τ C ϕ) (τC⊨τSTORED C ϕ a e (E′⊆E e e∈E′) e∈C)
                ; τC⊨τSTOREI = λ C ϕ a χ χ⊨¬ψ → ⊨-trans (τ′⊨τ C ϕ) (τC⊨τSTOREI C ϕ a χ (λ e e∈E e∉C → χ⊨¬ψ e (E⊆E′ e e∈E) e∉C))
                ; ✓STOREa = λ e e∈E′ → ⊨-trans ✓′⊨✓ (✓STOREa e (E′⊆E e e∈E′))
                ; ✓STOREb = λ χ χ⊨¬ψ → ⊨-trans ✓′⊨✓ (✓STOREb χ (λ e e∈E → χ⊨¬ψ e (E⊆E′ e e∈E)))
                }
                
  sem-resp-≲ {P} {P′} (r := M) P≲P′ P∈LET = P′∈LET where
    
    open LET P∈LET
    open _≲_ P≲P′

    P′∈LET : P′ ∈ LET r M
    P′∈LET = record
              { E⊆∅ = ⊆-trans E′⊆E E⊆∅
              ; τϕ⊨ϕ[M/r] = λ C ϕ → ⊨-trans (τ′⊨τ C ϕ) (τϕ⊨ϕ[M/r] C ϕ)
              }

  sem-resp-≲ {P₀} {P′₀} (C₁ ∥ C₂) P₀≲P′₀ P₀∈⟦C₁⟧|||⟦C₂⟧ = P′₀∈⟦C₁⟧|||⟦C₂⟧ where

    open _|||_ P₀∈⟦C₁⟧|||⟦C₂⟧
    open _≲_ P₀≲P′₀ using () renaming (E′⊆E to E′₀⊆E₀ ; E⊆E′ to E₀⊆E′₀ ; ℓ=ℓ′ to ℓ₀=ℓ′₀ ; κ′⊨κ to κ′₀⊨κ₀ ; ✓′⊨✓ to ✓′₀⊨✓₀ ; ≤⊆≤′ to ≤₀⊆≤′₀) 

    P′₀∈⟦C₁⟧|||⟦C₂⟧ : P′₀ ∈ (⟦ C₁ ⟧ ||| ⟦ C₂ ⟧)
    P′₀∈⟦C₁⟧|||⟦C₂⟧ = record
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
                        ; κ₀⊨κ₁ = λ e e∈E₁ → ⊨-trans (κ′₀⊨κ₀ e (E₁⊆E₀ e e∈E₁)) (κ₀⊨κ₁ e e∈E₁)
                        ; κ₀⊨κ₂ = λ e e∈E₂ → ⊨-trans (κ′₀⊨κ₀ e (E₂⊆E₀ e e∈E₂)) (κ₀⊨κ₂ e e∈E₂)
                        ; ✓₀⊨✓₁ = ⊨-trans ✓′₀⊨✓₀ ✓₀⊨✓₁
                        ; ✓₀⊨✓₂ = ⊨-trans ✓′₀⊨✓₀ ✓₀⊨✓₂
                        ; ℓ₀=ℓ₁ =  λ e e∈E₁ → ≡-trans (≡-symm (ℓ₀=ℓ′₀ e (E₁⊆E₀ e e∈E₁))) (ℓ₀=ℓ₁ e e∈E₁)
                        ; ℓ₀=ℓ₂ = λ e e∈E₂ → ≡-trans (≡-symm (ℓ₀=ℓ′₀ e (E₂⊆E₀ e e∈E₂))) (ℓ₀=ℓ₂ e e∈E₂)
                        }
    
    
