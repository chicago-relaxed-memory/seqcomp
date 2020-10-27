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

    open Pomset P using (E ; V ; ℓ ; act ; pre ; post)
    open Pomset Q using () renaming (E to F ; ℓ to m ; act to bct ; pre to qre ; post to qost ; V to U)

    field F⊆E : (F ⊆ E)
    field V⊆F : (V ⊆ F)
    field ℓ=m : ∀ e → (e ∈ F) → (ℓ(e) ≡ m(e))

    act=bct : ∀ e → (e ∈ F) → (act(e) ≡ bct(e))
    act=bct e e∈E = ≡-cong snd (ℓ=m e e∈E)

    pre=qre : ∀ e → (e ∈ F) → (pre(e) ≡ qre(e))
    pre=qre e e∈E = ≡-cong fst (ℓ=m e e∈E)

    post=qost : ∀ e → (e ∈ F) → (post(e) ≡ qost(e))
    post=qost e e∈E = ≡-cong postcondition (act=bct e e∈E)

    U⊆V : (U ⊆ V)
    U⊆V e (e∈F , ae∈Vis) = (F⊆E e e∈F , ≡-subst Visibles (≡-symm (act=bct e e∈F)) ae∈Vis)
    
  sem-resp-≲ : ∀ {P Q C} → (P ≲ Q) → (P ∈ ⟦ C ⟧) → (Q ∈ ⟦ C ⟧)

  sem-resp-≲ {P} {Q} P≲Q (⟦skip⟧ P hyp-E) = ⟦skip⟧ Q lemma-E where

    open Pomset P using (ℓ ; act ; V)
    open Pomset Q using () renaming (E to F ; ℓ to m ; act to bct ; pre to qre ; post to qost ; V to U)
    open _≲_ P≲Q using (F⊆E ; ℓ=m ; act=bct ; pre=qre ; post=qost ; U⊆V)

    lemma-E : ∀ e → (e ∈ F) → (e ∈ SKIP Q)
    lemma-E e e∈F with hyp-E e (F⊆E e e∈F)
    lemma-E e e∈F | impl e∉V pre⊨post = impl e∉U qre⊨qost where

      e∉U : (e ∉ U)
      e∉U e∈U = e∉V (U⊆V e e∈U)
      
      qre⊨qost : qre(e) ⊨ qost(e)
      qre⊨qost = ≡-subst₂ _⊨_ (pre=qre e e∈F) (post=qost e e∈F) pre⊨post
      
  sem-resp-≲ {P} {Q} P≲Q (⟦comp⟧ C₁ C₂ P P₁ P₂ P₁∈C₁ P₂∈C₂ hyp-E hyp-ℓ hyp-≤) = ⟦comp⟧ C₁ C₂ Q P₁ P₂ P₁∈C₁ P₂∈C₂ lemma-E lemma-ℓ lemma-≤  where

    open Pomset P using (E ; V)
    open Pomset P₁ using () renaming (V to V₁ ; V⊆E to V₁⊆E₁)
    open Pomset P₂ using () renaming (V to V₂ ; V⊆E to V₂⊆E₂)
    open Pomset Q using () renaming (E to F ; ℓ to m ; _≤_ to _≼_ ; act to bct ; pre to qre ; post to qost)
    open _≲_ P≲Q using (F⊆E ; V⊆F ; ℓ=m ; act=bct ; pre=qre ; post=qost)

    E∩V₁⊆V : (E ∩ V₁) ⊆ V
    E∩V₁⊆V e (e∈E , e∈V₁) with hyp-ℓ e e∈E
    E∩V₁⊆V e (e∈E , e∈V₁) | cut _ _ _ e∉V₁ _ _ _ _ = CONTRADICTION (e∉V₁ e∈V₁)
    E∩V₁⊆V e (e∈E , e∈V₁) | left _ _ a₀e=a₁e _ = (e∈E , (≡-subst Visibles (≡-symm a₀e=a₁e) (snd e∈V₁)))
    E∩V₁⊆V e (e∈E , e∈V₁) | right e∉E₁ _ _ _ = CONTRADICTION (e∉E₁ (V₁⊆E₁ e e∈V₁))
    E∩V₁⊆V e (e∈E , e∈V₁) | both _ _ a₀e=a₁e _ _ _ = (e∈E , (≡-subst Visibles (≡-symm a₀e=a₁e) (snd e∈V₁)))

    E∩V₂⊆V : (E ∩ V₂) ⊆ V
    E∩V₂⊆V e (e∈E , e∈V₂) with hyp-ℓ e e∈E
    E∩V₂⊆V e (e∈E , e∈V₂) | cut _ _ _ _ e∉V₂ _ _ _ = CONTRADICTION (e∉V₂ e∈V₂)
    E∩V₂⊆V e (e∈E , e∈V₂) | left _ e∉E₂ _ _ = CONTRADICTION (e∉E₂ (V₂⊆E₂ e e∈V₂))
    E∩V₂⊆V e (e∈E , e∈V₂) | right _ _ a₀e=a₂e _ = (e∈E , (≡-subst Visibles (≡-symm a₀e=a₂e) (snd e∈V₂)))
    E∩V₂⊆V e (e∈E , e∈V₂) | both _ _ _ a₀e=a₂e _ _ = (e∈E , (≡-subst Visibles (≡-symm a₀e=a₂e) (snd e∈V₂)))
    
    lemma-E : (∀ e → (e ∈ E-COMP Q P₁ P₂) → (e ∈ F))
    lemma-E e (left e∈V₁) with hyp-E e (left e∈V₁)
    lemma-E e (left e∈V₁) | e∈E = V⊆F e (E∩V₁⊆V e (e∈E , e∈V₁))
    lemma-E e (right e∈V₂) with hyp-E e (right e∈V₂)
    lemma-E e (right e∈V₂) | e∈E = V⊆F e (E∩V₂⊆V e (e∈E , e∈V₂))

    lemma-ℓ : (∀ e → (e ∈ F) → (e ∈ ℓ-COMP Q P₁ P₂))
    lemma-ℓ e e∈F with hyp-ℓ e (F⊆E e e∈F)
    lemma-ℓ e e∈F | X = {!!}

    lemma-≤ : (∀ d e → ((d , e) ∈ ≤-COMP P₁ P₂) → (d ≼ e))
    lemma-≤ = {!!}
   
  right-unit-sub : ∀ C → ⟦ C ⟧ ⊆ ⟦ C ∙ skip ⟧
  right-unit-sub C P₀ P₀∈C = ⟦comp⟧ C skip P₀ P₀ P₂ P₀∈C P₂∈⟦skip⟧ lemma-E lemma-ℓ lemma-≤ where

    open Pomset P₀ using () renaming (E to E₀ ; ℓ to ℓ₀ ; act to act₀ ; post to post₀ ; pre to pre₀ ; _≤_ to _≤₀_ ; ≤-refl to ≤₀-refl ; dec-V to dec-V₀ ; V⊆E to V₀⊆E₀)

    E₂ : Event → Set
    E₂ e = (e ∈ E₀) × (act₀(e) ∉ Visibles)

    ℓ₂ : Event → (Formula × Action)
    ℓ₂ e = (post₀(e) , ✓(post₀(e)))

    ✓-max₂ : ∀ {d e} → ((d ≡ e) × (d ≢ e)) → _
    ✓-max₂ (d=e , d≠e) = CONTRADICTION (d≠e d=e)
    
    P₂ : Pomset
    P₂ = record { E = E₂ ; _≤_ = _≡_ ; ℓ = ℓ₂ ; ✓-max = ✓-max₂ ; ≤-refl = refl ; ≤-trans = ≡-trans ; ≤-asym = (λ _ d=e → d=e) }

    open Pomset P₂ using () renaming (pre to pre₂)
    
    P₂∈⟦skip⟧ : P₂ ∈ ⟦ skip ⟧
    P₂∈⟦skip⟧ = ⟦skip⟧ P₂ (λ _ _ → impl (λ ()) ⊨-refl)

    lemma-E : (∀ e → (e ∈ E-COMP P₀ P₀ P₂) → (e ∈ E₀))
    lemma-E e (left e∈V₀) = V₀⊆E₀ e e∈V₀
    
    lemma-ℓ : (∀ e → (e ∈ E₀) → (e ∈ ℓ-COMP P₀ P₀ P₂))
    lemma-ℓ e e∈E₀ with dec-V₀ e e∈E₀ 
    lemma-ℓ e e∈E₀ | yes e∈V₀ = left e∈V₀ {!!} refl ⊨-refl
    lemma-ℓ e e∈E₀ | no  e∉V₀ = cut e∈E₀ {!!} e∉V₀ e∉V₀ {!!} ⊨-refl ⊨-refl ⊨-refl
    
    lemma-≤ : (∀ d e → ((d , e) ∈ ≤-COMP P₀ P₂) → (d ≤₀ e))
    lemma-≤ d e (left d≤₀e) = d≤₀e
    lemma-≤ d .d (right refl) = ≤₀-refl
  
  right-unit-sup : ∀ C → ⟦ C ∙ skip ⟧ ⊆ ⟦ C ⟧
  right-unit-sup C P₀ (⟦comp⟧ _ _ _ P₁ P₂ P₁∈C (⟦skip⟧ _ hyp-E₂) hyp-E₁ hyp-ℓ₁ hyp-≤₁) = sem-resp-≲ P₁≲P₀ P₁∈C where
  
    P₁≲P₀ : P₁ ≲ P₀
    P₁≲P₀ = {!!}
    
