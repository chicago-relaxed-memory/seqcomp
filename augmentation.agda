open import prelude
open import data-model using ( DataModel )
import command
import pomset
import semantics

module augmentation (DM : DataModel) (Event : Set) where

  open DataModel DM
  open command(DM)
  open pomset(DM)(Event)
  open semantics(DM)(Event)

  record _≲_ (P P′ : Pomset) : Set₁ where

    open Pomset P using (E ; act ; pre ; _≤_ ; τ ; ✓ ; RE ; WE ; ↓RW)
    open Pomset P′ using () renaming (E to E′ ; act to act′ ; pre to pre′ ; _≤_ to _≤′_; ≤-refl to ≤′-refl ; τ to τ′ ; ✓ to ✓′ ; RE to RE′ ; WE to WE′ ; ↓RW to ↓RW′)

    field E′⊆E : (E′ ⊆ E)
    field E⊆E′ : (E ⊆ E′)
    field act=act′ : ∀ e → (e ∈ E) → (act(e) ≡ act′(e))
    field pre′⊨pre : ∀ e → (e ∈ E) → (pre′(e) ⊨ pre(e))
    field ≤⊆≤′ : ∀ d e → (d ≤ e) → (d ≤′ e)
    field τ′⊨τ : ∀ C ϕ → (τ′(C)(ϕ) ⊨ τ(C)(ϕ))
    field ✓′⊨✓ : ✓′ ⊨ ✓
    
    RE⊆RE′ : (RE ⊆ RE′)
    RE⊆RE′ e (e∈E , ae∈R) = (E⊆E′ e e∈E , ≡-subst Reads (act=act′ e e∈E) ae∈R)
    
    RE′⊆RE : (RE′ ⊆ RE)
    RE′⊆RE e (e∈E′ , ae∈R) = (E′⊆E e e∈E′ , ≡-subst Reads (≡-symm (act=act′ e (E′⊆E e e∈E′))) ae∈R)

    WE⊆WE′ : (WE ⊆ WE′)
    WE⊆WE′ e (e∈E , ae∈W) = (E⊆E′ e e∈E , ≡-subst Writes (act=act′ e e∈E) ae∈W)
    
    WE′⊆WE : (WE′ ⊆ WE)
    WE′⊆WE e (e∈E′ , ae∈W) = (E′⊆E e e∈E′ , ≡-subst Writes (≡-symm (act=act′ e (E′⊆E e e∈E′))) ae∈W)

    ↓RW⊆↓RW' : ∀ e → (e ∈ E) → (↓RW(e) ⊆ ↓RW′(e))
    ↓RW⊆↓RW' e e∈E d (d∈E , d∈↓RWe) = (E⊆E′ d d∈E , λ d∈RE′ e∈WE′ → ≤⊆≤′ d e (d∈↓RWe (RE′⊆RE d d∈RE′) (WE′⊆WE e e∈WE′)))
    
  sem-resp-≲ : ∀ {P P′} C → (P ≲ P′) → (P ∈ ⟦ C ⟧) → (P′ ∈ ⟦ C ⟧)
  sen-resp-≲ : ∀ {P P′} G → (P ≲ P′) → (P ∈ ⟪ G ⟫) → (P′ ∈ ⟪ G ⟫)

  sem-resp-≲ {P₀} {P′₀} skip P₀≲P′₀ P₀∈SKIP = P′₀∈SKIP  where

    open SKIP P₀∈SKIP using (E₀⊆∅ ; τ₀ϕ⊨ϕ)
    open _≲_ P₀≲P′₀ using () renaming (E′⊆E to E′₀⊆E₀ ; τ′⊨τ to τ′₀⊨τ₀)
      
    P′₀∈SKIP : P′₀ ∈ SKIP
    P′₀∈SKIP = record
                { E₀⊆∅ = λ e e∈E′₀ → E₀⊆∅ e (E′₀⊆E₀ e e∈E′₀)
                ; τ₀ϕ⊨ϕ = λ C ϕ → ⊨-trans (τ′₀⊨τ₀ C ϕ) (τ₀ϕ⊨ϕ C ϕ) }

  sem-resp-≲ {P₀} {P′₀} (C₁ ∙ C₂) P₀≲P′₀ P₀∈⟦C₁⟧●⟦C₂⟧ = P′₀∈⟦C₁⟧●⟦C₂⟧ where

    open _●_ P₀∈⟦C₁⟧●⟦C₂⟧
    open Pomset P₁ using () renaming (τ to τ₁ ; τ-resp-⊆ to τ₁-resp-⊆)
    open Pomset P₂ using () renaming (E to E₂ ; pre to pre₂)
    open Pomset P₀ using () renaming (↓RW to ↓RW₀)
    open Pomset P′₀ using () renaming (↓RW to ↓RW′₀)
    open _≲_ P₀≲P′₀ using () renaming (E′⊆E to E′₀⊆E₀ ; E⊆E′ to E₀⊆E′₀ ; act=act′ to act₀=act′₀ ; pre′⊨pre to pre′₀⊨pre₀ ; ≤⊆≤′ to ≤₀⊆≤′₀ ; τ′⊨τ to τ′₀⊨τ₀ ; ✓′⊨✓ to ✓′₀⊨✓₀ ; ↓RW⊆↓RW' to ↓RW₀⊆↓RW'₀) 

    rhs′₀ : Event → Formula
    rhs′₀(e) = τ₁(↓RW′₀(e))(pre₂(e))
   
    rhs₀⊨rhs′₀ : ∀ e → (e ∈ E₂) → (rhs₀(e) ⊨ rhs′₀(e))
    rhs₀⊨rhs′₀ e e∈E₂ = τ₁-resp-⊆ (↓RW₀⊆↓RW'₀ e (E₂⊆E₀ e e∈E₂))
    
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
                      ; ✓₀⊨✓₁ = ⊨-trans ✓′₀⊨✓₀ ✓₀⊨✓₁
                      ; ✓₀⊨τ₁✓₂ = ⊨-trans ✓′₀⊨✓₀ ✓₀⊨τ₁✓₂
                      }
    
  sem-resp-≲ {P₀} {P′₀} (if ψ then C₁ else C₂) P₀≲P′₀ P₀∈IF = P′₀∈IF where

    open IF P₀∈IF
    open _≲_ P₀≲P′₀ using () renaming (E′⊆E to E′₀⊆E₀ ; E⊆E′ to E₀⊆E′₀ ; act=act′ to act₀=act′₀ ; pre′⊨pre to pre′₀⊨pre₀ ; ≤⊆≤′ to ≤₀⊆≤′₀ ; τ′⊨τ to τ′₀⊨τ₀ ; ✓′⊨✓ to ✓′₀⊨✓₀)
    
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
               ; ✓₀⊨✓₁ = ⊨-trans (⊨-resp-∧ ⊨-refl ✓′₀⊨✓₀) ✓₀⊨✓₁
               ; ✓₀⊨✓₂ = ⊨-trans (⊨-resp-∧ ⊨-refl ✓′₀⊨✓₀) ✓₀⊨✓₂
               }


  sem-resp-≲ {P} {P′} (r :=[ a ]) P≲P′ P∈LOAD = P′∈LOAD where

    open LOAD P∈LOAD
    open _≲_ P≲P′

    P′∈LOAD : P′ ∈ LOAD r a
    P′∈LOAD = record
                { v = v
                ; d=e = λ d e d∈E′ e∈E′ → d=e d e (E′⊆E d d∈E′) (E′⊆E e e∈E′)
                ; act=Rav = λ e e∈E′ → ≡-trans (≡-symm (act=act′ e (E′⊆E e e∈E′))) (act=Rav e (E′⊆E e e∈E′))
                ; τϕ⊨ϕ[v/r] = λ C ϕ → ⊨-trans (τ′⊨τ ϕ C) (τϕ⊨ϕ[v/r] C ϕ)
                ; τϕ⊨ϕ[[a]/r] = λ C ϕ C∩E⊆∅ → ⊨-trans (τ′⊨τ ϕ C) (τϕ⊨ϕ[[a]/r] C ϕ (⊆-trans (⊆-resp-∩ ⊆-refl E⊆E′) C∩E⊆∅))
                ; ✓⊨ff = λ E′⊆∅ → ⊨-trans ✓′⊨✓ (✓⊨ff (⊆-trans E⊆E′ E′⊆∅))
                }

  sem-resp-≲ {P} {P′} ([ a ]:= M) P≲P′ P∈STORE = P′∈STORE where

    open STORE P∈STORE
    open _≲_ P≲P′

    P′∈STORE : P′ ∈ STORE a M
    P′∈STORE = record
                { v = v
                ; d=e = λ d e d∈E′ e∈E′ → d=e d e (E′⊆E d d∈E′) (E′⊆E e e∈E′)
                ; act=Wav = λ e e∈E′ → ≡-trans (≡-symm (act=act′ e (E′⊆E e e∈E′))) (act=Wav e (E′⊆E e e∈E′))
                ; pre⊨M=v = λ e e∈E′ → ⊨-trans (pre′⊨pre e (E′⊆E e e∈E′)) (pre⊨M=v e (E′⊆E e e∈E′))
                ; τϕ⊨ϕ[v/[a]] = λ C ϕ → ⊨-trans (τ′⊨τ C ϕ) (τϕ⊨ϕ[v/[a]] C ϕ)
                ; ✓⊨ff = λ E′⊆∅ → ⊨-trans ✓′⊨✓ (✓⊨ff (⊆-trans E⊆E′ E′⊆∅))
                }
                
  sem-resp-≲ {P} {P′} (r := M) P≲P′ P∈LET = P′∈LET where
    
    open LET P∈LET
    open _≲_ P≲P′

    P′∈LET : P′ ∈ LET r M
    P′∈LET = record
              { E⊆∅ = ⊆-trans E′⊆E E⊆∅
              ; τϕ⊨ϕ[M/r] = λ C ϕ → ⊨-trans (τ′⊨τ C ϕ) (τϕ⊨ϕ[M/r] C ϕ)
              }

  sem-resp-≲ {P} {P′} (fork G join) P≲P′ P∈⟪G⟫ = sen-resp-≲ G P≲P′ P∈⟪G⟫

  sen-resp-≲ {P} {P′} nil P≲P′ P∈NIL = sem-resp-≲ skip P≲P′ P∈NIL
  
  sen-resp-≲ {P₀} {P′₀} (thread C) P₀≲P′₀ P₀∈THREAD = P′₀∈THREAD where

    open THREAD P₀∈THREAD
    open _≲_ P₀≲P′₀ using () renaming (E′⊆E to E′₀⊆E₀ ; E⊆E′ to E₀⊆E′₀ ; act=act′ to act₀=act′₀ ; pre′⊨pre to pre′₀⊨pre₀ ; ≤⊆≤′ to ≤₀⊆≤′₀ ; τ′⊨τ to τ′₀⊨τ₀ ; ✓′⊨✓ to ✓′₀⊨✓₀) 
    
    P′₀∈THREAD : P′₀ ∈ THREAD ⟦ C ⟧
    P′₀∈THREAD = record
                  { P₁ = P₁
                  ; P₁∈𝒫 = P₁∈𝒫
                  ; E₁⊆E₀ = ⊆-trans E₁⊆E₀ E₀⊆E′₀
                  ; E₀⊆E₁ = ⊆-trans E′₀⊆E₀ E₀⊆E₁
                  ; ≤₁⊆≤₀ = λ d e d≤₁e → ≤₀⊆≤′₀ d e (≤₁⊆≤₀ d e d≤₁e)
                  ; pre₀⊨pre₁ = λ e e∈E₁ → ⊨-trans (pre′₀⊨pre₀ e (E₁⊆E₀ e e∈E₁)) (pre₀⊨pre₁ e e∈E₁)
                  ; act₀=act₁ = λ e e∈E₁ → ≡-trans (≡-symm (act₀=act′₀ e (E₁⊆E₀ e e∈E₁))) (act₀=act₁ e e∈E₁)
                  ; τ₀ϕ⊨ϕ =  λ C ϕ → ⊨-trans (τ′₀⊨τ₀ C ϕ) (τ₀ϕ⊨ϕ C ϕ)
                  ; ✓₀⊨✓₁ = ⊨-trans ✓′₀⊨✓₀ ✓₀⊨✓₁
                  }
    
  sen-resp-≲ {P₀} {P′₀} (G₁ ∥ G₂) P₀≲P′₀ P₀∈⟪G₁⟫|||⟪G₂⟫ = P′₀∈⟪G₁⟫|||⟪G₂⟫ where

    open _|||_ P₀∈⟪G₁⟫|||⟪G₂⟫
    open _≲_ P₀≲P′₀ using () renaming (E′⊆E to E′₀⊆E₀ ; E⊆E′ to E₀⊆E′₀ ; act=act′ to act₀=act′₀ ; pre′⊨pre to pre′₀⊨pre₀ ; ≤⊆≤′ to ≤₀⊆≤′₀ ; τ′⊨τ to τ′₀⊨τ₀ ; ✓′⊨✓ to ✓′₀⊨✓₀) 

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
                        ; τ₀ϕ⊨τ₁ϕ = λ C ϕ → ⊨-trans (τ′₀⊨τ₀ C ϕ) (τ₀ϕ⊨τ₁ϕ C ϕ)
                        ; τ₀ϕ⊨τ₂ϕ =  λ C ϕ → ⊨-trans (τ′₀⊨τ₀ C ϕ) (τ₀ϕ⊨τ₂ϕ C ϕ)
                        ; ✓₀⊨✓₁ = ⊨-trans ✓′₀⊨✓₀ ✓₀⊨✓₁
                        ; ✓₀⊨✓₂ = ⊨-trans ✓′₀⊨✓₀ ✓₀⊨✓₂                        }
    
    
