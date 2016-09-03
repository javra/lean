/-
Copyright (c) 2016 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jakob von Raumer

Taking the pushout of a span of pushouts is taking the pushout of their
span's pushouts (sometimes called "3x3 lemma").
-/

import .pushout

open eq function pushout equiv

namespace pushout
section
  parameters {A₀₀ A₀₂ A₀₄ A₂₀ A₂₂ A₂₄ A₄₀ A₄₂ A₄₄ : Type}
    {f₀₁ : A₀₂ → A₀₀} {f₀₃ : A₀₂ → A₀₄}
    {f₁₀ : A₂₀ → A₀₀} {f₁₂ : A₂₂ → A₀₂} {f₁₄ : A₂₄ → A₀₄}
    {f₂₁ : A₂₂ → A₂₀} {f₂₃ : A₂₂ → A₂₄}
    {f₃₀ : A₂₀ → A₄₀} {f₃₂ : A₂₂ → A₄₂} {f₃₄ : A₂₄ → A₄₄}
    {f₄₁ : A₄₂ → A₄₀} {f₄₃ : A₄₂ → A₄₄}
    (H₁₁ : Π x, f₁₀ (f₂₁ x) = f₀₁ (f₁₂ x)) (H₁₁' : Π x, f₀₁ (f₁₂ x) = f₁₀ (f₂₁ x))
    (H₁₃ : Π x, f₀₃ (f₁₂ x) = f₁₄ (f₂₃ x))
    (H₃₁ : Π x, f₃₀ (f₂₁ x) = f₄₁ (f₃₂ x))
    (H₃₃ : Π x, f₄₃ (f₃₂ x) = f₃₄ (f₂₃ x)) (H₃₃' : Π x, f₃₄ (f₂₃ x) = f₄₃ (f₃₂ x))

  private definition A₀p := pushout f₀₁ f₀₃
  private definition A₂p := pushout f₂₁ f₂₃
  private definition A₄p := pushout f₄₁ f₄₃
  private definition Ap₀ := pushout f₁₀ f₃₀
  private definition Ap₂ := pushout f₁₂ f₃₂
  private definition Ap₄ := pushout f₁₄ f₃₄

  local abbreviation f₁p : A₂p → A₀p :=
  pushout.elim (inl ∘ f₁₀) (inr ∘ f₁₄) (λ x, ap inl !H₁₁ ⬝ !glue ⬝ ap inr !H₁₃)
  local abbreviation f₃p : A₂p → A₄p :=
  pushout.elim (inl ∘ f₃₀) (inr ∘ f₃₄) (λ x, ap inl !H₃₁ ⬝ !glue ⬝ ap inr !H₃₃)
  local abbreviation fp₁ : Ap₂ → Ap₀ :=
  pushout.elim (inl ∘ f₀₁) (inr ∘ f₄₁) (λ x, ap inl !H₁₁' ⬝ !glue ⬝ ap inr !H₃₁)
  local abbreviation fp₃ : Ap₂ → Ap₄ :=
  pushout.elim (inl ∘ f₀₃) (inr ∘ f₄₃) (λ x, ap inl !H₁₃ ⬝ !glue ⬝ ap inr !H₃₃')
  
  local abbreviation Avh := pushout f₁p f₃p
  local abbreviation Ahv := pushout fp₁ fp₃

  --set_option pp.implicit true
  protected definition of_pushouts_fun : Avh → Ahv :=
  begin
    intro x, induction x,
    exact pushout.elim (inl ∘ inl) (inr ∘ inl) (λ x, glue (inl x)) a,
    exact pushout.elim (inl ∘ inr) (inr ∘ inr) (λ x, glue (inr x)) a,
    exact sorry
  end

end
section
  parameters {A₀₀ A₀₂ A₀₄ A₂₀ A₂₂ A₂₄ A₄₀ A₄₂ A₄₄ : Type}
    {f₀₁ : A₀₂ → A₀₀} {f₀₃ : A₀₂ → A₀₄}
    {f₁₀ : A₂₀ → A₀₀} {f₁₂ : A₂₂ → A₀₂} {f₁₄ : A₂₄ → A₀₄}
    {f₂₁ : A₂₂ → A₂₀} {f₂₃ : A₂₂ → A₂₄}
    {f₃₀ : A₂₀ → A₄₀} {f₃₂ : A₂₂ → A₄₂} {f₃₄ : A₂₄ → A₄₄}
    {f₄₁ : A₄₂ → A₄₀} {f₄₃ : A₄₂ → A₄₄}
    (H₁₁ : Π x, f₁₀ (f₂₁ x) = f₀₁ (f₁₂ x)) (H₁₁' : Π x, f₀₁ (f₁₂ x) = f₁₀ (f₂₁ x))
    (H₁₃ : Π x, f₀₃ (f₁₂ x) = f₁₄ (f₂₃ x))
    (H₃₁ : Π x, f₃₀ (f₂₁ x) = f₄₁ (f₃₂ x))
    (H₃₃ : Π x, f₄₃ (f₃₂ x) = f₃₄ (f₂₃ x)) (H₃₃' : Π x, f₃₄ (f₂₃ x) = f₄₃ (f₃₂ x))
  include H₁₁ H₁₁' H₁₃ H₃₁ H₃₃ H₃₃'

  local abbreviation f := pushout.of_pushouts_fun H₁₁ H₁₁' H₁₃ H₃₁ H₃₃ H₃₃'
  local abbreviation f' := pushout.of_pushouts_fun H₁₁' H₁₁ H₃₁ H₁₃ H₃₃' H₃₃

  definition of_pushouts_fun_is_involution : f' ∘ f ~ id :=
  sorry

end

section
  parameters {A₀₀ A₀₂ A₀₄ A₂₀ A₂₂ A₂₄ A₄₀ A₄₂ A₄₄ : Type}
    {f₀₁ : A₀₂ → A₀₀} {f₀₃ : A₀₂ → A₀₄}
    {f₁₀ : A₂₀ → A₀₀} {f₁₂ : A₂₂ → A₀₂} {f₁₄ : A₂₄ → A₀₄}
    {f₂₁ : A₂₂ → A₂₀} {f₂₃ : A₂₂ → A₂₄}
    {f₃₀ : A₂₀ → A₄₀} {f₃₂ : A₂₂ → A₄₂} {f₃₄ : A₂₄ → A₄₄}
    {f₄₁ : A₄₂ → A₄₀} {f₄₃ : A₄₂ → A₄₄}
    (H₁₁ : Π x, f₁₀ (f₂₁ x) = f₀₁ (f₁₂ x))
    (H₁₃ : Π x, f₀₃ (f₁₂ x) = f₁₄ (f₂₃ x))
    (H₃₁ : Π x, f₃₀ (f₂₁ x) = f₄₁ (f₃₂ x))
    (H₃₃ : Π x, f₄₃ (f₃₂ x) = f₃₄ (f₂₃ x))

  local abbreviation H₁₁' := λ x, (H₁₁ x)⁻¹
  local abbreviation H₃₃' := λ x, (H₃₃ x)⁻¹
  local abbreviation f := pushout.of_pushouts_fun H₁₁ H₁₁' H₁₃ H₃₁ H₃₃ H₃₃'
  local abbreviation f' := pushout.of_pushouts_fun H₁₁' H₁₁ H₃₁ H₁₃ H₃₃' H₃₃

  definition of_pushouts_fun_is_equiv : is_equiv f :=
  begin
    fapply is_equiv.adjointify, exact f',
    do 2 (intro; apply of_pushouts_fun_is_involution)
  end

  protected definition of_pushouts :=
  equiv.mk f !of_pushouts_fun_is_equiv

end
end pushout
