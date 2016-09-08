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
    (H₁₁ : f₁₀ ∘ f₂₁ ~ f₀₁ ∘ f₁₂) (H₁₁' : f₀₁ ∘ f₁₂ ~ f₁₀ ∘ f₂₁)
    (H₁₃ : f₀₃ ∘ f₁₂ ~ f₁₄ ∘ f₂₃) (H₁₃' : f₁₄ ∘ f₂₃ ~ f₀₃ ∘ f₁₂)
    (H₃₁ : f₃₀ ∘ f₂₁ ~ f₄₁ ∘ f₃₂) (H₃₁' : f₄₁ ∘ f₃₂ ~ f₃₀ ∘ f₂₁)
    (H₃₃ : f₄₃ ∘ f₃₂ ~ f₃₄ ∘ f₂₃) (H₃₃' : f₃₄ ∘ f₂₃ ~ f₄₃ ∘ f₃₂)
    (H₁₁'' : Π x, (H₁₁ x) = (H₁₁' x)⁻¹)
    (H₁₃'' : Π x, (H₁₃ x) = (H₁₃' x)⁻¹)
    (H₃₁'' : Π x, (H₃₁ x) = (H₃₁' x)⁻¹)
    (H₃₃'' : Π x, (H₃₃ x) = (H₃₃' x)⁻¹)
  include H₁₁ H₁₁' H₁₃ H₁₃' H₃₁ H₃₁' H₃₃ H₃₃' H₁₁'' H₁₃'' H₃₁'' H₃₃''

  private definition A₀p [reducible] := pushout f₀₁ f₀₃
  private definition A₂p [reducible] := pushout f₂₁ f₂₃
  private definition A₄p [reducible] := pushout f₄₁ f₄₃
  private definition Ap₀ [reducible] := pushout f₁₀ f₃₀
  private definition Ap₂ [reducible] := pushout f₁₂ f₃₂
  private definition Ap₄ [reducible] := pushout f₁₄ f₃₄

  local abbreviation f₁p : A₂p → A₀p :=
  pushout.functor f₂₁ f₂₃ f₀₁ f₀₃ f₁₂ f₁₀ f₁₄ H₁₁ H₁₃'
  local abbreviation f₃p : A₂p → A₄p :=
  pushout.functor f₂₁ f₂₃ f₄₁ f₄₃ f₃₂ f₃₀ f₃₄ H₃₁ H₃₃'
  local abbreviation fp₁ : Ap₂ → Ap₀ :=
  pushout.functor f₁₂ f₃₂ f₁₀ f₃₀ f₂₁ f₀₁ f₄₁ H₁₁' H₃₁'
  local abbreviation fp₃ : Ap₂ → Ap₄ :=
  pushout.functor f₁₂ f₃₂ f₁₄ f₃₄ f₂₃ f₀₃ f₄₃ H₁₃ H₃₃
  
  local abbreviation Avh := pushout f₁p f₃p
  local abbreviation Ahv := pushout fp₁ fp₃

  private definition of_pushouts_fun_aux1 (a b : A₄₄) (p : a = b) :
    ap (pushout.elim (inl ∘ inr) (inr ∘ inr) (λ x, @glue _ _ _ fp₁ fp₃ (inr x))) (ap inr p⁻¹)
    = ap inr (ap inr p⁻¹) :=
  by cases p; reflexivity

  private definition of_pushouts_fun_aux2 (a b : A₀₄) (p : a = b) :
    ap (pushout.elim (inl ∘ inl) (inr ∘ inl) (λ x, @glue _ _ _ fp₁ fp₃ (inl x))) (ap inr p⁻¹)
    = ap inr (ap inl p⁻¹) :=
  by cases p; reflexivity

  private definition of_pushout_A₀pfun : A₀p → Ahv :=
  λ a, pushout.elim (inl ∘ inl) (inr ∘ inl) (λ x, glue (inl x)) a

  private definition of_pushout_A₄pfun : A₄p → Ahv :=
  λ a, pushout.elim (inl ∘ inr) (inr ∘ inr) (λ x, glue (inr x)) a

  private definition of_pushout_fun_square (x : A₂₂) : 
    square (ap inl (glue (f₂₁ x))) (ap inr (glue (f₂₃ x)))
    (ap (λ a, of_pushout_A₀pfun (pushout.functor f₂₁ f₂₃ f₀₁ f₀₃ f₁₂ f₁₀ f₁₄ H₁₁ H₁₃' a)) (glue x))
    (ap (λ a, of_pushout_A₄pfun (pushout.functor f₂₁ f₂₃ f₄₁ f₄₃ f₃₂ f₃₀ f₃₄ H₃₁ H₃₃' a)) (glue x)) :=
  begin
    refine !(ap_compose (λ x, pushout.elim _ _ _ x)) ⬝ph _,
    refine _ ⬝hp !(ap_compose (λ x, pushout.elim _ _ _ x))⁻¹, 
    refine ap !ap !elim_glue ⬝ph _ ⬝hp ap !ap !elim_glue⁻¹,
    refine !ap_con ⬝ph _ ⬝hp !ap_con⁻¹,
    refine ap (λ x, x ⬝ _) !ap_con ⬝ph _ ⬝hp ap (λ x, x ⬝ _) !ap_con⁻¹,
    refine ap (λ x, _ ⬝ x ⬝ _) !elim_glue ⬝ph _ ⬝hp ap (λ x, _ ⬝ x ⬝ _) !elim_glue⁻¹,
    fapply vconcat, fapply vconcat, rotate 1, 
    { apply transpose, apply pushout.glue_square, apply glue },
    { refine ap (ap inr) !elim_glue ⬝pv _, 
      refine !of_pushouts_fun_aux2 ⬝ph _ ⬝hp !of_pushouts_fun_aux1⁻¹,
      apply aps inr, apply move_top_of_right, apply move_top_of_left',
      apply eq_hconcat, apply ap (λ x, _ ⬝ ap inl x), apply !H₁₃''⁻¹,
      apply eq_hconcat, apply con.left_inv, 
      refine _ ⬝hp ap (λ x, _ ⬝ ap inr x) !H₃₃'',
      refine _ ⬝hp ap (λ x, x ⬝ _) !ap_inv⁻¹,
      refine _ ⬝hp !con.left_inv⁻¹, apply vrfl },
  end

  --set_option pp.implicit true
  protected definition of_pushouts_fun : Avh → Ahv :=
  begin
    intro x, induction x,
    exact of_pushout_A₀pfun a,
    exact of_pushout_A₄pfun a,
    induction x,
    { apply ap inl, apply glue },
    { apply ap inr, apply glue },
    { apply eq_pathover, apply of_pushout_fun_square }
  end
end

section
  parameters {A₀₀ A₀₂ A₀₄ A₂₀ A₂₂ A₂₄ A₄₀ A₄₂ A₄₄ : Type}
    {f₀₁ : A₀₂ → A₀₀} {f₀₃ : A₀₂ → A₀₄}
    {f₁₀ : A₂₀ → A₀₀} {f₁₂ : A₂₂ → A₀₂} {f₁₄ : A₂₄ → A₀₄}
    {f₂₁ : A₂₂ → A₂₀} {f₂₃ : A₂₂ → A₂₄}
    {f₃₀ : A₂₀ → A₄₀} {f₃₂ : A₂₂ → A₄₂} {f₃₄ : A₂₄ → A₄₄}
    {f₄₁ : A₄₂ → A₄₀} {f₄₃ : A₄₂ → A₄₄}
    (H₁₁ : f₁₀ ∘ f₂₁ ~ f₀₁ ∘ f₁₂)
    (H₁₃ : f₀₃ ∘ f₁₂ ~ f₁₄ ∘ f₂₃)
    (H₃₁ : f₃₀ ∘ f₂₁ ~ f₄₁ ∘ f₃₂)
    (H₃₃ : f₄₃ ∘ f₃₂ ~ f₃₄ ∘ f₂₃)
  include H₁₁ H₁₃ H₃₁ H₃₃

  local abbreviation H₁₁' := λ x, (H₁₁ x)⁻¹
  local abbreviation H₁₃' := λ x, (H₁₃ x)⁻¹
  local abbreviation H₃₁' := λ x, (H₃₁ x)⁻¹
  local abbreviation H₃₃' := λ x, (H₃₃ x)⁻¹

  local abbreviation f := pushout.of_pushouts_fun H₁₁ H₁₁' H₁₃ H₁₃' H₃₁ H₃₁' H₃₃ H₃₃' 
    (λ x, !inv_inv⁻¹) (λ x, !inv_inv⁻¹) (λ x, !inv_inv⁻¹) (λ x, !inv_inv⁻¹)
  local abbreviation f' := pushout.of_pushouts_fun H₁₁' H₁₁ H₃₁ H₃₁' H₁₃ H₁₃' H₃₃' H₃₃
    _ _ _ _

  protected definition of_pushouts_fun_is_involution : f' ∘ f ~ id :=
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
