2022-10-19

Given a declaration

  protocol ρ α* = { Cᵢ Tᵢ* | i ∈ I }

we write 𝓒_ρ ⊆ { Cᵢ | i ∈ I } for any non-empty subset I.

In this case, notation ρ{𝓒_ρ} means the protocol

  protocol ρ' α* = { Cᵢ Tᵢ* | Cᵢ ∈ 𝓒_ρ }

Page 9. Syntax

  T ::= ... | ρ{𝓒} | ...

perhaps ρ \upharpoonright 𝓒, that is, ρ restricted-to 𝓒, is a better syntax.


Fig 2. Type formation	Γ, Δ ⊢ T : κ

  T-Protocol

  ρ : P* → P ∈ Δ
  Δ ⊢ T* ⇐ P*
  --------------------
  Δ ⊢ ρ{ 𝓒_ρ } T* ⇒ ℙ

    we write ρ to mean ρ{Cᵢ|i∈I}

Fig <new>. Subtyping     Σ ⊢ T ≤ T : κ

Σ is a list of α ≤ β : κ triples

  Sub-In

  Σ ⊢ T₁ ≤ T₂ : ℙ
  Σ ⊢ S₁ ≤ S₂ : 𝕊
  --------------------
  Σ ⊢ ?T₁.S₁ ≤ ?T₂.S₂ : 𝕊

  Sub-Out

  Σ ⊢ T₂ ≤ T₁ : ℙ
  Σ ⊢ S₁ ≤ S₂ : 𝕊
  --------------------
  Σ ⊢ !T₁.S₁ ≤ !T₂.S₂ : 𝕊

  Sub-Proto (type parameters are treated invariantly)

  𝓒¹_ρ ⊆ 𝓒²_ρ
  ----------------------------
  Σ ⊢ ρ{ 𝓒¹_ρ } T* ≤ ρ{ 𝓒²_ρ } T* : ℙ

  Sub-Neg

  Σ ⊢ U ≤ T : ℙ
  -----------
  Σ ⊢ -T ≤ -U : ℙ

  Sub-Lifted

  T₁ ≤ T₂ : 𝕋
  --------------------
  T₁ ≤ T₂ : ℙ

  Sub-Lifted (alternative)

  Σ ⊢ T₁ ≤ T₂ : κ₁
  κ₁ < κ₂
  --------------------
  Σ ⊢ T₁ ≤ T₂ : κ₂

  Sub-Assumption

  ——————————–
  ⊢ α ≤ α : κ

  Sub-Forall
  T ≤ U : κ'
  ———————————————————–————--
  ∀α:κ.T  ≤ ∀α:κ. U : κ'

  A ≡ B
  -----
  A ≤ B


Fig 5. Types for constants

typeof (select Cⱼ) =
  ∀ α*:ℙ*. ∀ β:𝕊. ∀ 𝓒_ρ ⊆ { Cᵢ }. Cⱼ ∈ 𝓒_ρ.
  !(ρ{ 𝓒_ρ } α*).β → § (+ (Tⱼ* [ρ{ 𝓒_ρ } / ρ])).β 
(alternative:)
  ∀ α*:ℙ*. ∀ β:𝕊.
  !(ρ{𝓒_ρ} α*).β → § (+ (Tⱼ* [ρ{𝓒_ρ} / ρ])).β
  if protocol ρ α* ={𝐶𝑖: 𝑇𝑖}_𝑖∈𝐼 and 𝑘 ∈ 𝐼



Fig 6. Expressions typing        Γ | Δ ⊢ T | Γ

  e-Match
  ...
  Δ | Γ₁ ⊢ e ⇒ ? (ρ{ 𝓒_ρ } U*).S | Γ₂
  ∀ i, Cᵢ ∈ 𝓒_ρ:
    Δ | Γ₂, xᵢ : § (- (T* [ρ{ 𝓒_ρ } / ρ] [U*/α*])).S ⊢ eᵢ ⇒ Vᵢ | Γᵢ
  ...
(I don't understand the  ∀Cᵢ ∈ 𝓒 part. Two nested ∀?)

  E-Check
  Δ | Γ₁ ⊢ e ⇒ U | Γ₂
  U ≤ T : 𝕋
  --------------------
  Δ | Γ₁ ⊢ e ⇐ T | Γ₂

Fig 10. Labelled transition system for typing contexts

  L-Match

  Cⱼ ∈ 𝓒_ρ
  ------------------------------------------------------------
  x : ? (ρ{𝓒_ρ} U*).S —x?Cⱼ→ x : § (-(Tⱼ*[ρ{𝓒_ρ}/ρ][U*/α*])).S

  L-Sel

  Cⱼ ∈ 𝓒_ρ
  ------------------------------------------------------------
  x : ! (ρ{𝓒_ρ} U*).S —x!Cⱼ→ x : § (+(Tⱼ*[ρ{𝓒_ρ}/ρ][U*/α*])).S

Theorem 5.1 (Preservation)
Part (1) concludes ... ⇒ T′ and ⊢ T′ ≤ T : 𝕋


