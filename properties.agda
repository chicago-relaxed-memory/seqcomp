open import prelude
open import data-model using ( DataModel )
import command
import pomset
import semantics

module properties (DM : DataModel) (Event : Set) where

  open DataModel DM
  open command(DM)
  open pomset(DM)(Event)
  open semantics(DM)(Event)

  record _≲_ (P Q : Pomset) : Set where

    open Pomset P using (E ; V ; I ; ℓ ; act ; pre ; post ; _≤_ ; ↓)
    open Pomset Q using () renaming (E to F ; V to U ; I to J ; V⊆E to U⊆F ; ℓ to m ; act to bct ; pre to qre ; post to qost ; _≤_ to _≼_ ; ↓ to ⇓)

    field F⊆E : (F ⊆ E)
    field V⊆U : (V ⊆ U)
    field act=bct : ∀ e → (e ∈ U) → (act(e) ≡ bct(e))
    field qre⊨pre : ∀ e → (e ∈ F) → (qre(e) ⊨ pre(e))
    field post⊨qost : ∀ e → (e ∈ J) → (post(e) ⊨ qost(e))
    field ≤⊆≼ : ∀ d e → (d ≤ e) → (d ≼ e)
    
    U⊆V : (U ⊆ V)
    U⊆V e (e∈F , be∈Vis) = (F⊆E e e∈F , ≡-subst Visibles (≡-symm (act=bct e (e∈F , be∈Vis))) be∈Vis)

    V⊆F : (V ⊆ F)
    V⊆F e e∈V = U⊆F e (V⊆U e e∈V)

    J⊆I : (J ⊆ I)
    J⊆I e (e∈F , be∉Vis) = (F⊆E e e∈F , λ ae∈Vis → be∉Vis (≡-subst Visibles (act=bct e (V⊆U e (F⊆E e e∈F , ae∈Vis))) ae∈Vis))
    
    F∩I⊆J : ((F ∩ I) ⊆ J)
    F∩I⊆J e (e∈F , (e∈E , ae∉Vis)) = (e∈F , λ be∈Vis → ae∉Vis (≡-subst Visibles (≡-symm (act=bct e (e∈F , be∈Vis))) be∈Vis))
    
    ↓⊆⇓ : ∀ e → (↓(e) ⊆ ⇓(e))
    ↓⊆⇓ e d d≤e = ≤⊆≼ d e d≤e
    
  sem-resp-≲ : ∀ {P Q C} → (P ≲ Q) → (P ∈ ⟦ C ⟧) → (Q ∈ ⟦ C ⟧)

  sem-resp-≲ {P} {Q} P≲Q (⟦skip⟧ P hyp-E) = ⟦skip⟧ Q lemma-E where

    open Pomset P using (ℓ ; act ; V)
    open Pomset Q using () renaming (E to F ; I to J ; V to U ; ℓ to m ; act to bct ; pre to qre ; post to qost)
    open _≲_ P≲Q using (F⊆E ; U⊆V ; V⊆U ; F∩I⊆J ; qre⊨pre ; post⊨qost)

    lemma-E : ∀ e → (e ∈ F) → (e ∈ SKIP Q)
    lemma-E e e∈F with hyp-E e (F⊆E e e∈F)
    lemma-E e e∈F | impl e∈I pre⊨post = impl e∈J qre⊨qost where

      e∈J : (e ∈ J)
      e∈J = F∩I⊆J e (e∈F , e∈I)
      
      qre⊨qost : qre(e) ⊨ qost(e)
      qre⊨qost = ⊨-trans (qre⊨pre e e∈F) (⊨-trans pre⊨post (post⊨qost e e∈J))
      
  sem-resp-≲ {P} {Q} P≲Q (⟦comp⟧ C₁ C₂ P P₁ P₂ P₁∈C₁ P₂∈C₂ hyp-E hyp-ℓ hyp-≤) = ⟦comp⟧ C₁ C₂ Q P₁ P₂ P₁∈C₁ P₂∈C₂ lemma-E lemma-ℓ lemma-≤  where

    open Pomset P using (E ; V)
    open Pomset P₁ using () renaming (V to V₁ ; V⊆E to V₁⊆E₁ ; I∩V⊆∅ to I₁∩V₁⊆∅ ; ⇝-resp-⊆ to ⇝₁-resp-⊆)
    open Pomset P₂ using () renaming (V to V₂ ; V⊆E to V₂⊆E₂ ;  I∩V⊆∅ to I₂∩V₂⊆∅)
    open Pomset Q using () renaming (E to F ; V⊆E to U⊆F ; ℓ to m ; _≤_ to _≼_ ; act to bct ; pre to qre ; post to qost)
    open _≲_ P≲Q using (F⊆E ; V⊆F ; U⊆V ; V⊆U ; F∩I⊆J ; act=bct ; qre⊨pre ; post⊨qost ; ≤⊆≼ ; ↓⊆⇓)

    V₁⊆V : V₁ ⊆ V
    V₁⊆V e e∈V₁ with hyp-ℓ e (hyp-E e (left e∈V₁))
    V₁⊆V e e∈V₁ | cut _ e∈I₁ _ _ _ _ = CONTRADICTION (I₁∩V₁⊆∅ e (e∈I₁ , e∈V₁))
    V₁⊆V e e∈V₁ | left e∈V _ _ _ _ = e∈V
    V₁⊆V e e∈V₁ | right e∈V _ _ _ _ _ = e∈V
    V₁⊆V e e∈V₁ | both e∈V _ _ _ _ _ _ = e∈V

    V₂⊆V : V₂ ⊆ V
    V₂⊆V e e∈V₂ with hyp-ℓ e (hyp-E e (right e∈V₂))
    V₂⊆V e e∈V₂ | cut _ _ e∈I₂ _ _ _ = CONTRADICTION (I₂∩V₂⊆∅ e (e∈I₂ , e∈V₂))
    V₂⊆V e e∈V₂ | left e∈V _ _ _ _ = e∈V
    V₂⊆V e e∈V₂ | right e∈V _ _ _ _ _ = e∈V
    V₂⊆V e e∈V₂ | both e∈V _ _ _ _ _ _ = e∈V
    
    lemma-E : (∀ e → (e ∈ E-COMP Q P₁ P₂) → (e ∈ F))
    lemma-E e (left e∈V₁) with hyp-E e (left e∈V₁)
    lemma-E e (left e∈V₁) | e∈E = V⊆F e (V₁⊆V e e∈V₁)
    lemma-E e (right e∈V₂) with hyp-E e (right e∈V₂)
    lemma-E e (right e∈V₂) | e∈E = V⊆F e (V₂⊆V e e∈V₂)

    lemma-ℓ : (∀ e → (e ∈ F) → (e ∈ ℓ-COMP Q P₁ P₂))
    lemma-ℓ e e∈F with hyp-ℓ e (F⊆E e e∈F)
    lemma-ℓ e e∈F | cut e∈I e∈I₁ e∈I₂ pre⊨pre₁ post₁⊨pre₂ post₂⊨post =
      cut
        (F∩I⊆J e (e∈F , e∈I))
        e∈I₁
        e∈I₂
        (⊨-trans (qre⊨pre e e∈F) pre⊨pre₁)
        post₁⊨pre₂
        (⊨-trans post₂⊨post (post⊨qost e (F∩I⊆J e (e∈F , e∈I))))
    lemma-ℓ e e∈F | left e∈V e∈V₁ e∉E₂ a=a₁ pre⊨pre₁ =
      left
        (V⊆U e e∈V)
        e∈V₁
        e∉E₂
        (≡-trans (≡-symm (act=bct e (V⊆U e (V₁⊆V e e∈V₁)))) a=a₁)
        (⊨-trans (qre⊨pre e e∈F) pre⊨pre₁)
    lemma-ℓ e e∈F | right e∈V e∉E₁ e∈V₂ a=a₂ pre⊨ϕ ↓e⊨₁ϕ⇝pre₂ =
      right
        (V⊆U e e∈V)
        e∉E₁
        e∈V₂
        ((≡-trans (≡-symm (act=bct e (V⊆U e (V₂⊆V e e∈V₂)))) a=a₂))
        (⊨-trans (qre⊨pre e e∈F) pre⊨ϕ)
        (⇝₁-resp-⊆ (↓⊆⇓ e) ↓e⊨₁ϕ⇝pre₂)
    lemma-ℓ e e∈F | both e∈V e∈V₁ e∈V₂ a=a₁ a=a₂ pre⊨pre₁∨ϕ ↓e⊨₁ϕ⇝pre₂ =
      both
        (V⊆U e e∈V)
        e∈V₁
        e∈V₂
        ((≡-trans (≡-symm (act=bct e (V⊆U e (V₁⊆V e e∈V₁)))) a=a₁))
        (((≡-trans (≡-symm (act=bct e (V⊆U e (V₂⊆V e e∈V₂)))) a=a₂)))
        (⊨-trans (qre⊨pre e e∈F) pre⊨pre₁∨ϕ)
        (⇝₁-resp-⊆ (↓⊆⇓ e) ↓e⊨₁ϕ⇝pre₂)

    lemma-≤ : (∀ d e → ((d , e) ∈ ≤-COMP P₁ P₂) → (d ≼ e))
    lemma-≤ d e X = ≤⊆≼ d e (hyp-≤ d e X)
   
  right-unit-sub : ∀ C → ⟦ C ⟧ ⊆ ⟦ C ∙ skip ⟧
  right-unit-sub C P₀ P₀∈C = ⟦comp⟧ C skip P₀ P₀ P₂ P₀∈C P₂∈⟦skip⟧ lemma-E lemma-ℓ lemma-≤ where

    open Pomset P₀ using () renaming (E to E₀ ; I to I₀ ; V⊆E to V₀⊆E₀ ; E⊆I∪V to E₀⊆I₀∪V₀ ; I∩V⊆∅ to I₀∩V₀⊆∅ ; ℓ to ℓ₀ ; act to act₀ ; post to post₀ ; pre to pre₀ ; _≤_ to _≤₀_ ; ≤-refl to ≤₀-refl ; dec-V to dec-V₀)

    ℓ₂ : Event → (Formula × Action)
    ℓ₂ e = (post₀(e) , ✓(post₀(e)))

    ✓-max₂ : ∀ {d e} → ((d ≡ e) × (d ≢ e)) → _
    ✓-max₂ (d=e , d≠e) = CONTRADICTION (d≠e d=e)
    
    P₂ : Pomset
    P₂ = record { E = I₀ ; _≤_ = _≡_ ; ℓ = ℓ₂ ; ✓-max = ✓-max₂ ; ≤-refl = refl ; ≤-trans = ≡-trans ; ≤-asym = (λ _ d=e → d=e) }

    open Pomset P₂ using () renaming (I to I₂ ; pre to pre₂)

    I₀⊆I₂ : (I₀ ⊆ I₂)
    I₀⊆I₂ = {!!}

    P₂∈⟦skip⟧ : P₂ ∈ ⟦ skip ⟧
    P₂∈⟦skip⟧ = ⟦skip⟧ P₂ (λ e e∈I₀ → impl (I₀⊆I₂ e e∈I₀) ⊨-refl)

    lemma-E : (∀ e → (e ∈ E-COMP P₀ P₀ P₂) → (e ∈ E₀))
    lemma-E e (left e∈V₀) = V₀⊆E₀ e e∈V₀
    
    lemma-ℓ : (∀ e → (e ∈ E₀) → (e ∈ ℓ-COMP P₀ P₀ P₂))
    lemma-ℓ e e∈E₀ with E₀⊆I₀∪V₀ e e∈E₀ 
    lemma-ℓ e e∈E₀ | inl e∈I₀ = cut e∈I₀ e∈I₀ (I₀⊆I₂ e e∈I₀) ⊨-refl ⊨-refl ⊨-refl
    lemma-ℓ e e∈E₀ | inr e∈V₀ = left e∈V₀ e∈V₀ (λ e∈I₀ → I₀∩V₀⊆∅ e (e∈I₀ , e∈V₀)) refl ⊨-refl
    
    lemma-≤ : (∀ d e → ((d , e) ∈ ≤-COMP P₀ P₂) → (d ≤₀ e))
    lemma-≤ d e (left d≤₀e) = d≤₀e
    lemma-≤ d .d (right refl) = ≤₀-refl
  
  right-unit-sup : ∀ C → ⟦ C ∙ skip ⟧ ⊆ ⟦ C ⟧
  right-unit-sup C P₀ (⟦comp⟧ _ _ _ P₁ P₂ P₁∈C (⟦skip⟧ _ hyp-E₂) hyp-E₁ hyp-ℓ₁ hyp-≤₁) = sem-resp-≲ P₁≲P₀ P₁∈C where
  
    P₁≲P₀ : P₁ ≲ P₀
    P₁≲P₀ = {!!}
    
