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

  record _≲_ (P P′ : Pomset) : Set where

    open Pomset P using (E ; X ; I ; E⊆I⊎X ; act ; pre ; post ; _≤_ ; ↓ ; I-max)
    open Pomset P′ using () renaming (E to E′ ; X to X′ ; I to I′ ; X⊆E to X′⊆E′ ; act to act′ ; pre to pre′ ; post to post′ ; _≤_ to _≤′_; ≤-refl to ≤′-refl ; ↓ to ↓′)

    field E′⊆E : (E′ ⊆ E)
    field X⊆X′ : (X ⊆ X′)
    field act=act′ : ∀ e → (e ∈ X′) → (act(e) ≡ act′(e))
    field pre′⊨pre : ∀ e → (e ∈ E′) → (pre′(e) ⊨ pre(e))
    field post⊨post′ : ∀ e → (e ∈ I′) → (post(e) ⊨ post′(e))
    field ≤⊆≤′ : ∀ d e → (d ∈ E′) → (e ∈ E′) → (d ≤ e) → (d ≤′ e)
    
    X′⊆X : (X′ ⊆ X)
    X′⊆X e (e∈E′ , be∈Ext) = (E′⊆E e e∈E′ , ≡-subst Externals (≡-symm (act=act′ e (e∈E′ , be∈Ext))) be∈Ext)

    X⊆E′ : (X ⊆ E′)
    X⊆E′ e e∈X = X′⊆E′ e (X⊆X′ e e∈X)

    I′⊆I : (I′ ⊆ I)
    I′⊆I e (e∈E′ , be∉Ext) = (E′⊆E e e∈E′ , λ ae∈Ext → be∉Ext (≡-subst Externals (act=act′ e (X⊆X′ e (E′⊆E e e∈E′ , ae∈Ext))) ae∈Ext))
    
    E′∩I⊆I′ : ((E′ ∩ I) ⊆ I′)
    E′∩I⊆I′ e (e∈E′ , (e∈E , ae∉Ext)) = (e∈E′ , λ be∈Ext → ae∉Ext (≡-subst Externals (≡-symm (act=act′ e (e∈E′ , be∈Ext))) be∈Ext))

    ↓⊆↓′ : ∀ e → (e ∈ E′) → (↓(e) ⊆ ↓′(e))
    ↓⊆↓′ e e∈E′ d (d∈E , d≤e) with E⊆I⊎X d d∈E
    ↓⊆↓′ e e∈E′ d (d∈E , d≤e) | left d∈I _ with I-max d≤e d∈I
    ↓⊆↓′ e e∈E′ _ (e∈E , e≤e) | left e∈I _ | refl = (e∈E′ , ≤′-refl)
    ↓⊆↓′ e e∈E′ d (d∈E , d≤e) | right _ d∈X with X′⊆E′ d (X⊆X′ d d∈X)
    ↓⊆↓′ e e∈E′ d (d∈E , d≤e) | right _ d∈X | d∈E′ = (d∈E′ , ≤⊆≤′ d e d∈E′ e∈E′ d≤e)
    
  sem-resp-≲ : ∀ {P P′ C} → (P ≲ P′) → (P ∈ ⟦ C ⟧) → (P′ ∈ ⟦ C ⟧)

  sem-resp-≲ {P₀} {P′₀} {skip} P₀≲P′₀ P₀∈SKIP = P′₀∈SKIP  where

    open SKIP P₀∈SKIP using (E₀⊆I₀ ; pre₀⊨post₀)

    open Pomset P′₀ using () renaming (E to E′₀ ; I to I′₀ ; pre to pre′₀ ; post to post′₀)
    open _≲_ P₀≲P′₀ using () renaming (E′⊆E to E′₀⊆E₀ ; E′∩I⊆I′ to E′₀∩I₀⊆I′₀ ; pre′⊨pre to pre′₀⊨pre₀ ; post⊨post′ to post₀⊨post′₀)

    E′₀⊆I′₀ : (E′₀ ⊆ I′₀)
    E′₀⊆I′₀ e e∈E′₀ = E′₀∩I₀⊆I′₀ e (e∈E′₀ , (E₀⊆I₀ e (E′₀⊆E₀ e e∈E′₀)))
    
    pre′₀⊨post′₀ : ∀ e → (e ∈ E′₀) → pre′₀(e) ⊨ post′₀(e)
    pre′₀⊨post′₀ e e∈E′₀ = ⊨-trans (pre′₀⊨pre₀ e e∈E′₀) (⊨-trans (pre₀⊨post₀ e (E′₀⊆E₀ e e∈E′₀)) (post₀⊨post′₀ e (E′₀⊆I′₀ e e∈E′₀)))
      
    P′₀∈SKIP : P′₀ ∈ SKIP
    P′₀∈SKIP = record { E₀⊆I₀ = E′₀⊆I′₀ ; pre₀⊨post₀ = pre′₀⊨post′₀ }

  sem-resp-≲ {P₀} {P′₀} {C₁ ∙ C₂} P₀≲P′₀ P₀∈⟦C₁⟧●⟦C₂⟧ = P′₀∈⟦C₁⟧●⟦C₂⟧ where

    open _●_ P₀∈⟦C₁⟧●⟦C₂⟧
    open Pomset P₁ using () renaming (RE⊆X to RE₁⊆X₁)
    open Pomset P₂ using () renaming (WE⊆X to WE₂⊆X₂)
    open Pomset P′₀ using () renaming (I⊆E to I′₀⊆E′₀ ; X⊆E to X′₀⊆E′₀)
    open _≲_ P₀≲P′₀ using () renaming (E′⊆E to E′₀⊆E₀ ; X⊆X′ to X₀⊆X′₀ ; X′⊆X to X′₀⊆X₀ ; I′⊆I to I′₀⊆I₀ ; act=act′ to act₀=act′₀ ; pre′⊨pre to pre′₀⊨pre₀ ; post⊨post′ to post₀⊨post′₀ ; ↓⊆↓′ to ↓₀⊆↓′₀ ; ≤⊆≤′ to ≤₀⊆≤′₀) 

    X₁⊆X′₀ = λ e e∈X₁ → X₀⊆X′₀ e (X₁⊆X₀ e e∈X₁)
    X₂⊆X′₀ = λ e e∈X₂ → X₀⊆X′₀ e (X₂⊆X₀ e e∈X₂)

    P′₀∈⟦C₁⟧●⟦C₂⟧ : P′₀ ∈ (⟦ C₁ ⟧ ● ⟦ C₂ ⟧)
    P′₀∈⟦C₁⟧●⟦C₂⟧ = record
                     { P₁ = P₁
                     ; P₂ = P₂
                     ; P₁∈𝒫₁ = P₁∈𝒫₁
                     ; P₂∈𝒫₂ = P₂∈𝒫₂
                     ; E₀⊆E₁∪E₂ = λ e e∈E′₀ → E₀⊆E₁∪E₂ e (E′₀⊆E₀ e e∈E′₀) 
                     ; I₀⊆I₁ = λ e e∈I′₀ → I₀⊆I₁ e (I′₀⊆I₀ e e∈I′₀)
                     ; I₀⊆I₂ = λ e e∈I′₀ → I₀⊆I₂ e (I′₀⊆I₀ e e∈I′₀)
                     ; X₀⊆X₁∪X₂ = λ e e∈X′₀ → X₀⊆X₁∪X₂ e (X′₀⊆X₀ e e∈X′₀) 
                     ; X₁⊆X₀ = X₁⊆X′₀
                     ; X₂⊆X₀ = X₂⊆X′₀
                     ; int-pre₀⊨pre₁ = λ e e∈I′₀ → ⊨-trans (pre′₀⊨pre₀ e (I′₀⊆E′₀ e e∈I′₀)) (int-pre₀⊨pre₁ e (I′₀⊆I₀ e e∈I′₀))
                     ; int-post₁⊨pre₂ = λ e e∈I′₀ → int-post₁⊨pre₂ e (I′₀⊆I₀ e e∈I′₀)
                     ; int-post₂⊨post₀ = λ e e∈I′₀ → ⊨-trans (int-post₂⊨post₀ e (I′₀⊆I₀ e e∈I′₀)) (post₀⊨post′₀ e e∈I′₀)
                     ; just = just
                     ; just-I = just-I
                     ; just-≤  = λ d e d∈RE₁ e∈WE₂ d≤₁e → ≤₀⊆≤′₀ d e (X′₀⊆E′₀ d (X₁⊆X′₀ d (RE₁⊆X₁ d d∈RE₁))) (X′₀⊆E′₀ e (X₂⊆X′₀ e (WE₂⊆X₂ e e∈WE₂))) (just-≤ d e d∈RE₁ e∈WE₂ d≤₁e)
                     ; ext-post′₁⊨pre₂ = ext-post′₁⊨pre₂
                     ; ext-pre₀⊨pre₁ = λ e e∈X₁ e∉E₂ → ⊨-trans (pre′₀⊨pre₀ e (X′₀⊆E′₀ e (X₁⊆X′₀ e e∈X₁))) (ext-pre₀⊨pre₁ e e∈X₁ e∉E₂)
                     ; ext-pre₀⊨pre′₂ = λ e e∉E₁ e∈X₂ → ⊨-trans (pre′₀⊨pre₀ e (X′₀⊆E′₀ e (X₂⊆X′₀ e e∈X₂))) (ext-pre₀⊨pre′₂ e e∉E₁ e∈X₂)
                     ; ext-pre₀⊨pre₁∨pre′₂ = λ e e∈X₁ e∈X₂ → ⊨-trans (pre′₀⊨pre₀ e (X′₀⊆E′₀ e (X₁⊆X′₀ e e∈X₁))) (ext-pre₀⊨pre₁∨pre′₂ e e∈X₁ e∈X₂)
                     ; ext-act₀=act₁ = λ e e∈X₁ → ≡-trans (≡-symm (act₀=act′₀ e (X₁⊆X′₀ e e∈X₁))) (ext-act₀=act₁ e e∈X₁)
                     ; ext-act₀=act₂ =  λ e e∈X₂ → ≡-trans (≡-symm (act₀=act′₀ e (X₂⊆X′₀ e e∈X₂))) (ext-act₀=act₂ e e∈X₂)
                     ; ≤₁⊆≤₀ = λ{ d e (d∈E′₀ , d∈E₁) (e∈E′₀ , e∈E₁) d≤₁e → ≤₀⊆≤′₀ d e d∈E′₀ e∈E′₀ (≤₁⊆≤₀ d e (E′₀⊆E₀ d d∈E′₀ , d∈E₁) (E′₀⊆E₀ e e∈E′₀ , e∈E₁) d≤₁e) }
                     ; ≤₂⊆≤₀ = λ{ d e (d∈E′₀ , d∈E₂) (e∈E′₀ , e∈E₂) d≤₂e → ≤₀⊆≤′₀ d e d∈E′₀ e∈E′₀ (≤₂⊆≤₀ d e (E′₀⊆E₀ d d∈E′₀ , d∈E₂) (E′₀⊆E₀ e e∈E′₀ , e∈E₂) d≤₂e) }
                     ; coherence = λ d e d∈X₁ e∈X₂ d#e → ≤₀⊆≤′₀ d e (X′₀⊆E′₀ d (X₁⊆X′₀ d d∈X₁)) (X′₀⊆E′₀ e (X₂⊆X′₀ e e∈X₂)) (coherence d e d∈X₁ e∈X₂ d#e)
                     }
    
  -- TODO
  sem-resp-≲ {P} {P′} {if ϕ then C} P≲P′ P∈ϕ▷⟦C⟧ = record {}
  sem-resp-≲ {P} {P′} {r :=[ a ]} P≲P′ P∈LOAD = record {}
  sem-resp-≲ {P} {P′} {[ x ]:= x₁} P≲P′ P∈STORE = record {}
  sem-resp-≲ {P} {P′} {r := M} P≲P′ P∈LET = record {}
