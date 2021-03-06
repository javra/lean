/-
Copyright (c) 2015 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis

Basic facts about the positive natural numbers.

Developed primarily for use in the construction of ℝ. For the most part, the only theorems here
are those needed for that construction.
-/
import data.rat.order data.nat
open nat rat subtype eq.ops

definition pnat := { n : ℕ | n > 0 }

namespace pnat

protected definition prio := num.pred nat.prio

notation `ℕ+` := pnat

definition pos (n : ℕ) (H : n > 0) : ℕ+ := tag n H

definition nat_of_pnat (p : ℕ+) : ℕ := elt_of p
reserve postfix `~`:std.prec.max_plus
local postfix ~ := nat_of_pnat

theorem pnat_pos (p : ℕ+) : p~ > 0 := has_property p

protected definition add (p q : ℕ+) : ℕ+ :=
tag (p~ + q~) (add_pos (pnat_pos p) (pnat_pos q))

protected definition mul (p q : ℕ+) : ℕ+ :=
tag (p~ * q~) (mul_pos (pnat_pos p) (pnat_pos q))

protected definition le (p q : ℕ+) := p~ ≤ q~

protected definition lt (p q : ℕ+) := p~ < q~

definition pnat_has_add [instance] [priority pnat.prio] : has_add pnat :=
has_add.mk pnat.add

definition pnat_has_mul [instance] [priority pnat.prio] : has_mul pnat :=
has_mul.mk pnat.mul

definition pnat_has_le [instance] [priority pnat.prio] : has_le pnat :=
has_le.mk pnat.le

definition pnat_has_lt [instance] [priority pnat.prio] : has_lt pnat :=
has_lt.mk pnat.lt

definition pnat_has_one [instance] [priority pnat.prio] : has_one pnat :=
has_one.mk (pos (1:nat) dec_trivial)

protected lemma mul_def (p q : ℕ+) : p * q = tag (p~ * q~) (mul_pos (pnat_pos p) (pnat_pos q)) :=
rfl

protected lemma le_def (p q : ℕ+) : (p ≤ q) = (p~ ≤ q~) :=
rfl

protected lemma lt_def (p q : ℕ+) : (p < q) = (p~ < q~) :=
rfl

protected theorem pnat.eq {p q : ℕ+} : p~ = q~ → p = q :=
subtype.eq

protected definition decidable_lt : decidable_rel pnat.lt :=
λa b, nat.decidable_lt a~ b~

protected theorem le_refl (a : ℕ+) : a ≤ a :=
begin rewrite pnat.le_def end

protected theorem le_trans {p q r : ℕ+} : p ≤ q → q ≤ r → p ≤ r :=
begin rewrite *pnat.le_def, apply nat.le_trans end

protected theorem le_antisymm {n m : ℕ+} : n ≤ m → m ≤ n → n = m :=
begin rewrite +pnat.le_def, intros, apply (pnat.eq (nat.le_antisymm a a_1)) end

protected theorem le_iff_lt_or_eq (m n : ℕ+) : m ≤ n ↔ m < n ∨ m = n :=
begin
  rewrite [pnat.lt_def, pnat.le_def], apply iff.intro,
  { intro, apply or.elim (nat.lt_or_eq_of_le a),
    intro, apply or.intro_left, assumption,
    intro, apply or.intro_right, apply pnat.eq, assumption },
  { intro, apply or.elim a, apply nat.le_of_lt, intro, rewrite a_1 }
end

protected theorem le_total (m n : ℕ+) : m ≤ n ∨ n ≤ m :=
begin rewrite pnat.le_def, apply nat.le_total end

protected theorem lt_irrefl (a : ℕ+) : ¬ a < a :=
begin rewrite pnat.lt_def, apply nat.lt_irrefl end

protected definition decidable_linear_order [trans_instance] : decidable_linear_order pnat :=
⦃ decidable_linear_order,
  le              := pnat.le,
  le_refl         := by apply pnat.le_refl,
  le_trans        := by apply @pnat.le_trans,
  le_antisymm     := by apply @pnat.le_antisymm,
  lt              := pnat.lt,
  lt_irrefl       := by apply pnat.lt_irrefl,
  le_iff_lt_or_eq := by apply pnat.le_iff_lt_or_eq,
  decidable_lt    := pnat.decidable_lt,
  le_total        := by apply pnat.le_total ⦄

notation 2 := (tag 2 dec_trivial : ℕ+)
notation 3 := (tag 3 dec_trivial : ℕ+)
definition pone : ℕ+ := tag 1 dec_trivial

definition rat_of_pnat [reducible] (n : ℕ+) : ℚ :=
n~

theorem pnat.to_rat_of_nat (n : ℕ+) : rat_of_pnat n = of_nat n~ :=
rfl

-- these will come in rat

theorem rat_of_nat_nonneg (n : ℕ) : 0 ≤ of_nat n :=
trivial

theorem rat_of_pnat_ge_one (n : ℕ+) : rat_of_pnat n ≥ 1 :=
of_nat_le_of_nat_of_le (pnat_pos n)

theorem rat_of_pnat_is_pos (n : ℕ+) : rat_of_pnat n > 0 :=
of_nat_lt_of_nat_of_lt (pnat_pos n)

theorem of_nat_le_of_nat_of_le {m n : ℕ} (H : m ≤ n) : of_nat m ≤ of_nat n :=
of_nat_le_of_nat_of_le H

theorem of_nat_lt_of_nat_of_lt {m n : ℕ} (H : m < n) : of_nat m < of_nat n :=
of_nat_lt_of_nat_of_lt H

theorem rat_of_pnat_le_of_pnat_le {m n : ℕ+} (H : m ≤ n) : rat_of_pnat m ≤ rat_of_pnat n :=
begin rewrite pnat.le_def at H, exact of_nat_le_of_nat_of_le H end

theorem rat_of_pnat_lt_of_pnat_lt {m n : ℕ+} (H : m < n) : rat_of_pnat m < rat_of_pnat n :=
begin rewrite pnat.lt_def at H, exact of_nat_lt_of_nat_of_lt H end

theorem pnat_le_of_rat_of_pnat_le {m n : ℕ+} (H : rat_of_pnat m ≤ rat_of_pnat n) : m ≤ n :=
begin rewrite pnat.le_def, exact le_of_of_nat_le_of_nat H end

definition inv (n : ℕ+) : ℚ :=
(1 : ℚ) / rat_of_pnat n

local postfix `⁻¹` := inv

protected theorem inv_pos (n : ℕ+) : n⁻¹ > 0 := one_div_pos_of_pos !rat_of_pnat_is_pos

theorem inv_le_one (n : ℕ+) : n⁻¹ ≤ (1 : ℚ) :=
begin
  unfold inv,
  change 1 / rat_of_pnat n ≤ 1 / 1,
  apply one_div_le_one_div_of_le,
  apply zero_lt_one,
  apply rat_of_pnat_ge_one
end

theorem inv_lt_one_of_gt {n : ℕ+} (H : n~ > 1) : n⁻¹ < (1 : ℚ) :=
begin
  unfold inv,
  change 1 / rat_of_pnat n < 1 / 1,
  apply one_div_lt_one_div_of_lt,
  apply zero_lt_one,
  rewrite pnat.to_rat_of_nat,
  apply (of_nat_lt_of_nat_of_lt H)
end

theorem pone_inv : pone⁻¹ = 1 := rfl

theorem add_invs_nonneg (m n : ℕ+) : 0 ≤ m⁻¹ + n⁻¹ :=
begin
  apply le_of_lt,
  apply add_pos,
  repeat apply pnat.inv_pos
end

protected theorem one_mul (n : ℕ+) : pone * n = n :=
begin
  apply pnat.eq,
  unfold pone,
  rewrite [pnat.mul_def, ↑nat_of_pnat, one_mul]
end

theorem pone_le (n : ℕ+) : pone ≤ n :=
begin rewrite pnat.le_def, exact succ_le_of_lt (pnat_pos n) end

theorem pnat_to_rat_mul (a b : ℕ+) : rat_of_pnat (a * b) = rat_of_pnat a * rat_of_pnat b := rfl

theorem mul_lt_mul_left {a b c : ℕ+} (H : a < b) : a * c < b * c :=
begin rewrite [pnat.lt_def at *], exact mul_lt_mul_of_pos_right H !pnat_pos end

theorem one_lt_two : pone < 2 :=
!nat.le_refl

theorem inv_two_mul_lt_inv (n : ℕ+) : (2 * n)⁻¹ < n⁻¹ :=
begin
  rewrite ↑inv,
  apply one_div_lt_one_div_of_lt,
  apply rat_of_pnat_is_pos,
  have H : n~ < (2 * n)~, begin
    rewrite -(pnat.one_mul n) at {1},
    rewrite -pnat.lt_def,
    apply mul_lt_mul_left,
    apply one_lt_two
  end,
  apply of_nat_lt_of_nat_of_lt,
  apply H
end

theorem inv_two_mul_le_inv (n : ℕ+) : (2 * n)⁻¹ ≤ n⁻¹ := rat.le_of_lt !inv_two_mul_lt_inv

theorem inv_ge_of_le {p q : ℕ+} (H : p ≤ q) : q⁻¹ ≤ p⁻¹ :=
one_div_le_one_div_of_le !rat_of_pnat_is_pos (rat_of_pnat_le_of_pnat_le H)

theorem inv_gt_of_lt {p q : ℕ+} (H : p < q) : q⁻¹ < p⁻¹ :=
one_div_lt_one_div_of_lt !rat_of_pnat_is_pos (rat_of_pnat_lt_of_pnat_lt H)

theorem ge_of_inv_le {p q : ℕ+} (H : p⁻¹ ≤ q⁻¹) : q ≤ p :=
pnat_le_of_rat_of_pnat_le (le_of_one_div_le_one_div !rat_of_pnat_is_pos H)

theorem two_mul (p : ℕ+) : rat_of_pnat (2 * p) = (1 + 1) * rat_of_pnat p :=
by rewrite pnat_to_rat_mul

protected theorem add_halves (p : ℕ+) : (2 * p)⁻¹ + (2 * p)⁻¹ = p⁻¹ :=
begin
  rewrite [↑inv, -(add_halves (1 / (rat_of_pnat p))), div_div_eq_div_mul],
  have H : rat_of_pnat (2 * p) = rat_of_pnat p * (1 + 1), by rewrite [rat.mul_comm, two_mul],
  rewrite *H
end

theorem add_halves_double (m n : ℕ+) :
        m⁻¹ + n⁻¹ = ((2 * m)⁻¹ + (2 * n)⁻¹) + ((2 * m)⁻¹ + (2 * n)⁻¹) :=
have hsimp : ∀ a b : ℚ, (a + a) + (b + b) = (a + b) + (a + b),
  by intros; rewrite [rat.add_assoc, -(rat.add_assoc a b b), {_+b}rat.add_comm, -*rat.add_assoc],
by rewrite [-pnat.add_halves m, -pnat.add_halves n, hsimp]

protected theorem inv_mul_eq_mul_inv {p q : ℕ+} : (p * q)⁻¹ = p⁻¹ * q⁻¹ :=
begin rewrite [↑inv, pnat_to_rat_mul, one_div_mul_one_div] end

protected theorem inv_mul_le_inv (p q : ℕ+) : (p * q)⁻¹ ≤ q⁻¹ :=
begin
  rewrite [pnat.inv_mul_eq_mul_inv, -{q⁻¹}rat.one_mul at {2}],
  apply mul_le_mul,
  apply inv_le_one,
  apply le.refl,
  apply le_of_lt,
  apply pnat.inv_pos,
  apply rat.le_of_lt rat.zero_lt_one
end

theorem pnat_mul_le_mul_left' (a b c : ℕ+) : a ≤ b → c * a ≤ c * b :=
begin
  rewrite +pnat.le_def, intro H,
  apply mul_le_mul_of_nonneg_left H,
  apply le_of_lt,
  apply pnat_pos
end

protected theorem mul_assoc (a b c : ℕ+) : a * b * c = a * (b * c) :=
pnat.eq !mul.assoc

protected theorem mul_comm (a b : ℕ+) : a * b = b * a :=
pnat.eq !mul.comm

protected theorem add_assoc (a b c : ℕ+) : a + b + c = a + (b + c) :=
pnat.eq !add.assoc

protected theorem mul_le_mul_left (p q : ℕ+) : q ≤ p * q :=
begin
  rewrite [-pnat.one_mul q at {1}, pnat.mul_comm, pnat.mul_comm p],
  apply pnat_mul_le_mul_left',
  apply pone_le
end

protected theorem mul_le_mul_right (p q : ℕ+) : p ≤ p * q :=
by rewrite pnat.mul_comm; apply pnat.mul_le_mul_left

protected theorem inv_cancel_left (p : ℕ+) : rat_of_pnat p * p⁻¹ = (1 : ℚ) :=
mul_one_div_cancel (ne.symm (ne_of_lt !rat_of_pnat_is_pos))

protected theorem inv_cancel_right (p : ℕ+) : p⁻¹ * rat_of_pnat p = (1 : ℚ) :=
by rewrite rat.mul_comm; apply pnat.inv_cancel_left

theorem lt_add_left (p q : ℕ+) : p < p + q :=
begin
  have H : p~ < p~ + q~, begin
    rewrite -(nat.add_zero (p~)) at {1},
    apply nat.add_lt_add_left,
    apply pnat_pos
  end,
  apply H
end

theorem inv_add_lt_left (p q : ℕ+) : (p + q)⁻¹ < p⁻¹ :=
by apply inv_gt_of_lt; apply lt_add_left

theorem div_le_pnat (q : ℚ) (n : ℕ+) (H : q ≥ n⁻¹) : 1 / q ≤ rat_of_pnat n :=
begin
  apply div_le_of_le_mul,
  apply lt_of_lt_of_le,
  apply pnat.inv_pos,
  rotate 1,
  apply H,
  apply le_mul_of_div_le,
  apply rat_of_pnat_is_pos,
  apply H
end

theorem pnat_cancel' (n m : ℕ+) : (n * n * m)⁻¹ * (rat_of_pnat n * rat_of_pnat n) = m⁻¹ :=
have hsimp : ∀ a b c : ℚ, (a * a * (b * b * c)) = (a * b) * (a * b) * c,
  begin
    intro a b c,
    rewrite[-*rat.mul_assoc],
    exact (!mul.right_comm ▸ rfl),
  end,
by rewrite [rat.mul_comm, *pnat.inv_mul_eq_mul_inv, hsimp, *pnat.inv_cancel_left, *rat.one_mul]

definition pceil (a : ℚ) : ℕ+ := tag (ubound a) !ubound_pos

theorem pceil_helper {a : ℚ} {n : ℕ+} (H : pceil a ≤ n) (Ha : a > 0) : n⁻¹ ≤ 1 / a :=
le.trans (inv_ge_of_le H) (one_div_le_one_div_of_le Ha (ubound_ge a))

theorem inv_pceil_div (a b : ℚ) (Ha : a > 0) (Hb : b > 0) : (pceil (a / b))⁻¹ ≤ b / a :=
have (pceil (a / b))⁻¹ ≤ 1 / (1 / (b / a)),
  begin
    apply one_div_le_one_div_of_le,
    show 0 < 1 / (b / a), from
      one_div_pos_of_pos (div_pos_of_pos_of_pos Hb Ha),
    show 1 / (b / a) ≤ rat_of_pnat (pceil (a / b)),
    begin
      rewrite div_div_eq_mul_div,
      rewrite one_mul,
      apply ubound_ge
    end
  end,
begin
  rewrite one_div_one_div at this,
  exact this
end

theorem sep_by_inv {a b : ℚ} : a > b → ∃ N : ℕ+, a > (b + N⁻¹ + N⁻¹) :=
begin
  change b < a → ∃ N : ℕ+, (b + N⁻¹ + N⁻¹) < a,
  intro H,
  apply exists.elim (exists_add_lt_and_pos_of_lt H),
  intro c Hc,
  existsi (pceil ((1 + 1 + 1) / c)),
  apply lt.trans,
  rotate 1,
  apply and.left Hc,
  rewrite rat.add_assoc,
  apply rat.add_lt_add_left,
  rewrite -(add_halves c) at {3},
  apply add_lt_add,
  repeat (apply lt_of_le_of_lt;
    apply inv_pceil_div;
    apply dec_trivial;
    apply and.right Hc;
    apply div_lt_div_of_pos_of_lt_of_pos;
    apply two_pos;
    exact dec_trivial;
    apply and.right Hc)
end

theorem nonneg_of_ge_neg_invs (a : ℚ) : (∀ n : ℕ+, -n⁻¹ ≤ a) → 0 ≤ a :=
begin
  intro H,
  apply le_of_not_gt,
  suppose a < 0,
  have H2 : 0 < -a, from neg_pos_of_neg this,
  (not_lt_of_ge !H) (iff.mp !lt_neg_iff_lt_neg (calc
    (pceil (of_num 2 / -a))⁻¹ ≤ -a / of_num 2
        : !inv_pceil_div dec_trivial H2
                           ... < -a / 1
        : div_lt_div_of_pos_of_lt_of_pos dec_trivial dec_trivial H2
                           ... = -a : !div_one))
end

theorem pnat_bound {ε : ℚ} (Hε : ε > 0) : ∃ p : ℕ+, p⁻¹ ≤ ε :=
begin
  existsi (pceil (1 / ε)),
  rewrite -(one_div_one_div ε) at {2},
  apply pceil_helper,
  apply pnat.le_refl,
  apply one_div_pos_of_pos Hε
end

theorem p_add_fractions (n : ℕ+) : (2 * n)⁻¹ + (2 * 3 * n)⁻¹ + (3 * n)⁻¹ = n⁻¹ :=
have T : 2⁻¹ + 2⁻¹ * 3⁻¹ + 3⁻¹ = 1, from dec_trivial,
by rewrite[*pnat.inv_mul_eq_mul_inv,-*right_distrib,T,rat.one_mul]

theorem rat_power_two_le (k : ℕ+) : rat_of_pnat k ≤ 2^k~ :=
!binary_nat_bound

end pnat
