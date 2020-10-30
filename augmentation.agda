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

  record _≲_ (P Q : Pomset) : Set where

    open Pomset P using (E ; X ; I ; ℓ ; act ; pre ; post ; _≤_ ; ↓)
    open Pomset Q using () renaming (E to F ; X to Y ; I to J ; X⊆E to Y⊆F ; ℓ to m ; act to bct ; pre to qre ; post to qost ; _≤_ to _≼_ ; ↓ to ⇓)

    field F⊆E : (F ⊆ E)
    field X⊆Y : (X ⊆ Y)
    field act=bct : ∀ e → (e ∈ Y) → (act(e) ≡ bct(e))
    field qre⊨pre : ∀ e → (e ∈ F) → (qre(e) ⊨ pre(e))
    field post⊨qost : ∀ e → (e ∈ J) → (post(e) ⊨ qost(e))
    field ≤⊆≼ : ∀ d e → (d ≤ e) → (d ≼ e)
    
    Y⊆X : (Y ⊆ X)
    Y⊆X e (e∈F , be∈Ext) = (F⊆E e e∈F , ≡-subst Externals (≡-symm (act=bct e (e∈F , be∈Ext))) be∈Ext)

    X⊆F : (X ⊆ F)
    X⊆F e e∈X = Y⊆F e (X⊆Y e e∈X)

    J⊆I : (J ⊆ I)
    J⊆I e (e∈F , be∉Ext) = (F⊆E e e∈F , λ ae∈Ext → be∉Ext (≡-subst Externals (act=bct e (X⊆Y e (F⊆E e e∈F , ae∈Ext))) ae∈Ext))
    
    F∩I⊆J : ((F ∩ I) ⊆ J)
    F∩I⊆J e (e∈F , (e∈E , ae∉Ext)) = (e∈F , λ be∈Ext → ae∉Ext (≡-subst Externals (≡-symm (act=bct e (e∈F , be∈Ext))) be∈Ext))
    
    ↓⊆⇓ : ∀ e → (↓(e) ⊆ ⇓(e))
    ↓⊆⇓ e d d≤e = ≤⊆≼ d e d≤e
    
  sem-resp-≲ : ∀ {P Q C} → (P ≲ Q) → (P ∈ ⟦ C ⟧) → (Q ∈ ⟦ C ⟧)

  sem-resp-≲ {P₀} {Q₀} {skip} P₀≲Q₀ P₀∈SKIP = Q₀∈SKIP  where

    open SKIP P₀∈SKIP using (E₀⊆I₀ ; pre₀⊨post₀)

    open Pomset Q₀ using () renaming (E to F₀ ; I to J₀ ; pre to qre₀ ; post to qost₀)
    open _≲_ P₀≲Q₀ using () renaming (F⊆E to F₀⊆E₀ ; F∩I⊆J to F₀∩I₀⊆J₀ ; qre⊨pre to qre₀⊨pre₀ ; post⊨qost to post₀⊨qost₀)

    F₀⊆J₀ : (F₀ ⊆ J₀)
    F₀⊆J₀ e e∈F₀ = F₀∩I₀⊆J₀ e (e∈F₀ , (E₀⊆I₀ e (F₀⊆E₀ e e∈F₀)))
    
    qre₀⊨qost₀ : ∀ e → (e ∈ F₀) → qre₀(e) ⊨ qost₀(e)
    qre₀⊨qost₀ e e∈F₀ = ⊨-trans (qre₀⊨pre₀ e e∈F₀) (⊨-trans (pre₀⊨post₀ e (F₀⊆E₀ e e∈F₀)) (post₀⊨qost₀ e (F₀⊆J₀ e e∈F₀)))
      
    Q₀∈SKIP : Q₀ ∈ SKIP
    Q₀∈SKIP = record { E₀⊆I₀ = F₀⊆J₀ ; pre₀⊨post₀ = qre₀⊨qost₀ }

  sem-resp-≲ {P₀} {Q₀} {C₁ ∙ C₂} P₀≲Q₀ P₀∈⟦C₁⟧●⟦C₂⟧ = Q₀∈⟦C₁⟧●⟦C₂⟧ where

    open _●_ P₀∈⟦C₁⟧●⟦C₂⟧
    open Pomset P₁ using () renaming (▷-resp-⊆ to ▷₁-resp-⊆)
    open Pomset Q₀ using () renaming (I⊆E to J₀⊆F₀ ; X⊆E to Y₀⊆F₀)
    open _≲_ P₀≲Q₀ using () renaming (F⊆E to F₀⊆E₀ ; X⊆Y to X₀⊆Y₀ ; J⊆I to J₀⊆I₀ ; act=bct to act₀=bct₀ ; qre⊨pre to qre₀⊨pre₀ ; post⊨qost to post₀⊨qost₀ ; ↓⊆⇓ to ↓₀⊆⇓₀ ; ≤⊆≼ to ≤₀⊆≼₀) 

    Q₀∈⟦C₁⟧●⟦C₂⟧ : Q₀ ∈ (⟦ C₁ ⟧ ● ⟦ C₂ ⟧)
    Q₀∈⟦C₁⟧●⟦C₂⟧ = record
                     { P₁ = P₁
                     ; P₂ = P₂
                     ; P₁∈𝒫₁ = P₁∈𝒫₁
                     ; P₂∈𝒫₂ = P₂∈𝒫₂
                     ; E₀⊆E₁∪E₂ = λ e e∈F₀ → E₀⊆E₁∪E₂ e (F₀⊆E₀ e e∈F₀)
                     ; X₁∪X₂⊆X₀ = λ e e∈X₁∪X₂ → X₀⊆Y₀ e (X₁∪X₂⊆X₀ e e∈X₁∪X₂) 
                     ; int-pre₀⊨pre₁ = λ e e∈J₀ → ⊨-trans (qre₀⊨pre₀ e (J₀⊆F₀ e e∈J₀)) (int-pre₀⊨pre₁ e (J₀⊆I₀ e e∈J₀))
                     ; int-post₁⊨pre₂ = λ e e∈J₀ → int-post₁⊨pre₂ e (J₀⊆I₀ e e∈J₀)
                     ; int-post₂⊨post₀ = λ e e∈J₀ → ⊨-trans (int-post₂⊨post₀ e (J₀⊆I₀ e e∈J₀)) (post₀⊨qost₀ e e∈J₀)
                     ; pre′₂ = pre′₂
                     ; pre′₂✓ = λ e e∈X₂ → ▷₁-resp-⊆ (↓₀⊆⇓₀ e) (pre′₂✓ e e∈X₂)
                     ; ext-pre₀⊨pre₁ = λ e e∈X₁ e∉E₂ → ⊨-trans (qre₀⊨pre₀ e (Y₀⊆F₀ e (X₀⊆Y₀ e (X₁∪X₂⊆X₀ e (inl e∈X₁))))) (ext-pre₀⊨pre₁ e e∈X₁ e∉E₂)
                     ; ext-pre₀⊨pre′₂ = λ e e∉E₁ e∈X₂ → ⊨-trans (qre₀⊨pre₀ e (Y₀⊆F₀ e (X₀⊆Y₀ e (X₁∪X₂⊆X₀ e (inr e∈X₂))))) (ext-pre₀⊨pre′₂ e e∉E₁ e∈X₂)
                     ; ext-pre₀⊨pre₁∨pre′₂ = λ e e∈X₁ e∈X₂ → ⊨-trans (qre₀⊨pre₀ e (Y₀⊆F₀ e (X₀⊆Y₀ e (X₁∪X₂⊆X₀ e (inl e∈X₁))))) (ext-pre₀⊨pre₁∨pre′₂ e e∈X₁ e∈X₂)
                     ; ext-act₀=act₁ = λ e e∈X₁ → ≡-trans (≡-symm (act₀=bct₀ e (X₀⊆Y₀ e (X₁∪X₂⊆X₀ e (inl e∈X₁))))) (ext-act₀=act₁ e e∈X₁)
                     ; ext-act₀=act₂ =  λ e e∈X₂ → ≡-trans (≡-symm (act₀=bct₀ e (X₀⊆Y₀ e (X₁∪X₂⊆X₀ e (inr e∈X₂))))) (ext-act₀=act₂ e e∈X₂)
                     ; ≤₁⊆≤₀ = λ d e d∈F₀ e∈F₀ d≤₁e → ≤₀⊆≼₀ d e (≤₁⊆≤₀ d e (F₀⊆E₀ d d∈F₀) (F₀⊆E₀ e e∈F₀) d≤₁e)
                     ; ≤₂⊆≤₀ = λ d e d∈F₀ e∈F₀ d≤₂e → ≤₀⊆≼₀ d e (≤₂⊆≤₀ d e (F₀⊆E₀ d d∈F₀) (F₀⊆E₀ e e∈F₀) d≤₂e)
                     ; coherence = λ d e d∈E₁ e∈E₂ d#e → ≤₀⊆≼₀ d e (coherence d e d∈E₁ e∈E₂ d#e)
                     }
    
  -- TODO
  sem-resp-≲ {P} {Q} {if ϕ then C} P≲Q P∈ϕ▷⟦C⟧ = record {}
  sem-resp-≲ {P} {Q} {r :=[ a ]} P≲Q P∈LOAD = record {}
  sem-resp-≲ {P} {Q} {[ x ]:= x₁} P≲Q P∈STORE = record {}
  sem-resp-≲ {P} {Q} {r := M} P≲Q P∈LET = record {}
