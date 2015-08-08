/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jeremy Avigad

The order relation on the integers. We show that int is an instance of linear_comm_ordered_ring
and transfer the results.
-/
import types.int.basic algebra.ordered_ring types algebra.group
open nat
open decidable
open eq.ops sum algebra prod eq
open int

namespace int

-- Things to Add to Nat
theorem of_nat_add (n m : nat) : of_nat (n + m) = of_nat n + of_nat m := rfl
theorem of_nat_mul (n m : ℕ) : of_nat (n * m) = of_nat n * of_nat m := rfl

--Things to Add to Int
protected definition prio : num := num.pred std.priority.default

-- Main
private definition nonneg (a : ℤ) : Type.{0} := int.cases_on a (take n, unit) (take n, empty)
definition le (a b : ℤ) : Type.{0} := nonneg (b - a)
definition lt (a b : ℤ) : Type.{0} := le (int.add a (of_nat (nat.succ nat.zero))) b

infix [priority int.prio] - := int.sub
infix [priority int.prio] <= := int.le
infix [priority int.prio] ≤  := int.le
infix [priority int.prio] <  := int.lt

local attribute nonneg [reducible]
private definition decidable_nonneg [instance] (a : ℤ) : decidable (nonneg a) := int.cases_on a _ _
definition decidable_le [instance] (a b : ℤ) : decidable (a ≤ b) := decidable_nonneg _
definition decidable_lt [instance] (a b : ℤ) : decidable (a < b) := decidable_nonneg _

private theorem nonneg.elim {a : ℤ} : nonneg a → Σn : ℕ, a = n :=
int.cases_on a (take n H, sigma.mk n rfl) (take n', empty.elim)

private theorem nonneg_or_nonneg_neg (a : ℤ) : nonneg a ⊎ nonneg (-a) :=
int.cases_on a (take n, sum.inl unit.star) (take n, sum.inr unit.star)

theorem le.intro {a b : ℤ} {n : ℕ} (H : a + n = b) : a ≤ b :=
have n = b - a, from eq_add_neg_of_add_eq (!add.comm ▸ H),
show nonneg (b - a), from this ▸ unit.star

theorem le.elim {a b : ℤ} (H : a ≤ b) : Σn : ℕ, int.add a n = b := --TODO note this is terrible
obtain (n : ℕ) (H1 : b - a = n), from nonneg.elim H,
sigma.mk n (!add.comm ▸ add_eq_of_eq_add_neg (H1⁻¹))

theorem le.total (a b : ℤ) : a ≤ b ⊎ b ≤ a :=
begin
cases (nonneg_or_nonneg_neg (b - a)),
apply sum.inl,
exact a_1,
apply sum.inr,
exact (transport nonneg (neg_sub b a) a_1)
end


theorem of_nat_le_of_nat_of_le {m n : ℕ} (H : #nat m ≤ n) : of_nat m ≤ of_nat n :=
obtain (k : ℕ) (Hk : m + k = n), from nat.le.elim H,
le.intro (Hk ▸ (of_nat_add m k)⁻¹)

theorem le_of_of_nat_le_of_nat {m n : ℕ} (H : of_nat m ≤ of_nat n) : (#nat m ≤ n) :=
obtain (k : ℕ) (Hk : of_nat m + of_nat k = of_nat n), from le.elim H,
have m + k = n, from of_nat.inj (of_nat_add m k ⬝ Hk),
nat.le.intro this

theorem of_nat_le_of_nat (m n : ℕ) : of_nat m ≤ of_nat n ↔ m ≤ n :=
iff.intro le_of_of_nat_le_of_nat of_nat_le_of_nat_of_le

theorem lt_add_succ (a : ℤ) (n : ℕ) : a < a + succ n :=
le.intro (show a + 1 + n = a + succ n, from
  calc
    a + 1 + n = a + (1 + n) : add.assoc
      ... = a + (n + 1)     : nat.add.comm
      ... = a + succ n      : rfl)

theorem lt.intro {a b : ℤ} {n : ℕ} (H : a + succ n = b) : a < b :=
H ▸ lt_add_succ a n

set_option pp.all true

--protected definition int_has_one [instance] [reducible] : has_one ℤ := has_one.mk (of_nat (nat.succ nat.zero))

theorem lt.elim {a b : ℤ} (H : a < b) : Σn : ℕ, int.add a (succ n) = b :=
begin
cases (le.elim H),
esimp [succ],
fapply sigma.mk,
assumption,
rewrite [add.comm a_1 (of_nat (nat.succ nat.zero)), (add.assoc a (of_nat (nat.succ nat.zero)) a_1)⁻¹],
assumption
end



theorem of_nat_lt_of_nat (n m : ℕ) : of_nat n < of_nat m ↔ n < m :=
calc
  of_nat n < of_nat m ↔ of_nat n + 1 ≤ of_nat m : iff.refl
    ... ↔ of_nat (nat.succ n) ≤ of_nat m        : of_nat_succ n ▸ !iff.refl
    ... ↔ nat.succ n ≤ m                        : of_nat_le_of_nat
    ... ↔ n < m                                 : iff.symm (lt_iff_succ_le _ _)

theorem lt_of_of_nat_lt_of_nat {m n : ℕ} (H : of_nat m < of_nat n) : #nat m < n := iff.mp !of_nat_lt_of_nat H

theorem of_nat_lt_of_nat_of_lt {m n : ℕ} (H : #nat m < n) : of_nat m < of_nat n := iff.mp' !of_nat_lt_of_nat H

/- show that the integers form an ordered additive group -/

theorem le.refl (a : ℤ) : a ≤ a :=
le.intro (add_zero a)

theorem le.trans {a b c : ℤ} (H1 : a ≤ b) (H2 : b ≤ c) : a ≤ c :=
obtain (n : ℕ) (Hn : a + n = b), from le.elim H1,
obtain (m : ℕ) (Hm : b + m = c), from le.elim H2,
have a + of_nat (n + m) = c, from
  calc
    a + of_nat (n + m) = a + (of_nat n + m) : {of_nat_add n m}
      ... = a + n + m : (add.assoc a n m)⁻¹
      ... = b + m : {Hn}
      ... = c : Hm,
le.intro this

theorem le.antisymm : Π {a b : ℤ}, a ≤ b → b ≤ a → a = b :=
take a b : ℤ, assume (H₁ : a ≤ b) (H₂ : b ≤ a),
obtain (n : ℕ) (Hn : a + n = b), from le.elim H₁,
obtain (m : ℕ) (Hm : b + m = a), from le.elim H₂,
have a + of_nat (n + m) = a + 0, from
  calc
    a + of_nat (n + m) = a + (of_nat n + m) : of_nat_add
      ... = a + n + m                       : add.assoc
      ... = b + m                           : Hn
      ... = a                               : Hm
      ... = a + 0                           : add_zero,
have of_nat (n + m) = of_nat 0, from add.left_cancel this,
have n + m = 0,                 from of_nat.inj this,
have n = 0,                     from nat.eq_zero_of_add_eq_zero_right this,
show a = b, from
  calc
    a = a + 0        : add_zero
      ... = a + n    : this
      ... = b        : Hn

theorem lt.irrefl (a : ℤ) : ¬ a < a :=
(suppose a < a,
  obtain (n : ℕ) (Hn : a + succ n = a), from lt.elim this,
  have a + succ n = a + 0, from
    Hn ⬝ !add_zero⁻¹,
  !succ_ne_zero (of_nat.inj (add.left_cancel this)))

theorem ne_of_lt {a b : ℤ} (H : a < b) : a ≠ b :=
(suppose a = b, absurd (this ▸ H) (lt.irrefl b))

theorem le_of_lt {a b : ℤ} (H : a < b) : a ≤ b :=
obtain (n : ℕ) (Hn : a + succ n = b), from lt.elim H,
le.intro Hn

theorem lt_iff_le_and_ne (a b : ℤ) : a < b ↔ (a ≤ b × a ≠ b) :=
iff.intro
  (assume H, pair (le_of_lt H) (ne_of_lt H))
  (assume H,
    have a ≤ b, from prod.pr1 H,
    have a ≠ b, from prod.pr2 H,
    obtain (n : ℕ) (Hn : a + n = b), from le.elim `a ≤ b`,
    have n ≠ 0, from (assume H' : n = 0, `a ≠ b` (!add_zero ▸ H' ▸ Hn)),
    obtain (k : ℕ) (Hk : n = nat.succ k), from nat.exists_eq_succ_of_ne_zero this,
    lt.intro (Hk ▸ Hn))

theorem le_iff_lt_or_eq (a b : ℤ) : a ≤ b ↔ (a < b ⊎ a = b) :=
iff.intro
  (assume H,
    by_cases
      (suppose a = b, sum.inr this)
      (suppose a ≠ b,
        obtain (n : ℕ) (Hn : a + n = b), from le.elim H,
        have n ≠ 0, from (assume H' : n = 0, `a ≠ b` (!add_zero ▸ H' ▸ Hn)),
        obtain (k : ℕ) (Hk : n = nat.succ k), from nat.exists_eq_succ_of_ne_zero this,
        sum.inl (lt.intro (Hk ▸ Hn))))
  (assume H,
    sum.rec_on H
      (assume H1, le_of_lt H1)
      (assume H1, H1 ▸ !le.refl))

theorem lt_succ (a : ℤ) : a < a + 1 :=
le.refl (a + 1)

theorem add_le_add_left {a b : ℤ} (H : a ≤ b) (c : ℤ) : c + a ≤ c + b :=
obtain (n : ℕ) (Hn : a + n = b), from le.elim H,
have H2 : c + a + n = c + b, from
  calc
    c + a + n = c + (a + n) : add.assoc c a n
      ... = c + b : {Hn},
le.intro H2

theorem add_lt_add_left {a b : ℤ} (H : a < b) (c : ℤ) : c + a < c + b :=
let H' := le_of_lt H in
(iff.mp' (lt_iff_le_and_ne _ _)) (pair (add_le_add_left H' _)
                                  (take Heq, let Heq' := add_left_cancel Heq in
                                   !lt.irrefl (Heq' ▸ H)))

theorem mul_nonneg {a b : ℤ} (Ha : 0 ≤ a) (Hb : 0 ≤ b) : 0 ≤ a * b :=
obtain (n : ℕ) (Hn : 0 + n = a), from le.elim Ha,
obtain (m : ℕ) (Hm : 0 + m = b), from le.elim Hb,
le.intro
  (inverse
    (calc
      a * b = (0 + n) * b : Hn
        ... = n * b       : nat.zero_add
        ... = n * (0 + m) : {Hm⁻¹}
        ... = n * m       : nat.zero_add
        ... = 0 + n * m   : zero_add))

theorem mul_pos {a b : ℤ} (Ha : 0 < a) (Hb : 0 < b) : 0 < a * b :=
obtain (n : ℕ) (Hn : 0 + nat.succ n = a), from lt.elim Ha,
obtain (m : ℕ) (Hm : 0 + nat.succ m = b), from lt.elim Hb,
lt.intro
  (inverse
    (calc
      a * b = (0 + nat.succ n) * b                     : Hn
        ... = nat.succ n * b                           : nat.zero_add
        ... = nat.succ n * (0 + nat.succ m)            : {Hm⁻¹}
        ... = nat.succ n * nat.succ m                  : nat.zero_add
        ... = of_nat (nat.succ n * nat.succ m)         : of_nat_mul
        ... = of_nat (nat.succ n * m + nat.succ n)     : nat.mul_succ
        ... = of_nat (nat.succ (nat.succ n * m + n))   : nat.add_succ
        ... = 0 + nat.succ (nat.succ n * m + n)        : zero_add))


theorem zero_lt_one : (0 : ℤ) < 1 := unit.star

theorem not_le_of_gt {a b : ℤ} (H : a < b) : ¬ b ≤ a :=
  assume Hba,
  let Heq := le.antisymm (le_of_lt H) Hba in
  !lt.irrefl (Heq ▸ H)

theorem lt_of_lt_of_le {a b c : ℤ} (Hab : a < b) (Hbc : b ≤ c) : a < c :=
  let Hab' := le_of_lt Hab in
  let Hac := le.trans Hab' Hbc in
  (iff.mp' !lt_iff_le_and_ne) (pair Hac
    (assume Heq, not_le_of_gt (Heq ▸ Hab) Hbc))

theorem lt_of_le_of_lt  {a b c : ℤ} (Hab : a ≤ b) (Hbc : b < c) : a < c :=
  let Hbc' := le_of_lt Hbc in
  let Hac := le.trans Hab Hbc' in
  (iff.mp' !lt_iff_le_and_ne) (pair Hac
    (assume Heq, not_le_of_gt (Heq⁻¹ ▸ Hbc) Hab))

section migrate_algebra
  open [classes] algebra

--print fields linear_ordered_comm_ring

  protected definition linear_ordered_comm_ring [reducible] :
    algebra.linear_ordered_comm_ring int :=
  ⦃algebra.linear_ordered_comm_ring, int.integral_domain,
    le               := le,
    le_refl          := le.refl,
    le_trans         := @le.trans,
    le_antisymm      := @le.antisymm,
    lt               := lt,
--    le_of_lt         := @le_of_lt,
--    lt_irrefl        := lt.irrefl,
--    lt_of_lt_of_le   := @lt_of_lt_of_le,
--    lt_of_le_of_lt   := @lt_of_le_of_lt,
    add_le_add_left  := @add_le_add_left,
    mul_nonneg       := @mul_nonneg,
    mul_pos          := @mul_pos,
    lt_iff_le_and_ne := lt_iff_le_and_ne,
    le_iff_lt_or_eq  := le_iff_lt_or_eq,
    le_total         := le.total,
    zero_ne_one      := zero_ne_one
--    zero_lt_one      := zero_lt_one,
--    add_lt_add_left  := @add_lt_add_left
⦄

  protected definition decidable_linear_ordered_comm_ring [reducible] :
    algebra.decidable_linear_ordered_comm_ring int :=
  ⦃algebra.decidable_linear_ordered_comm_ring,
    int.linear_ordered_comm_ring,
    decidable_lt := decidable_lt⦄

  local attribute int.integral_domain [instance]
  local attribute int.linear_ordered_comm_ring [instance]
  local attribute int.decidable_linear_ordered_comm_ring [instance]

  definition ge [reducible] (a b : ℤ) := algebra.has_le.ge a b
  definition gt [reducible] (a b : ℤ) := algebra.has_lt.gt a b
  infix >= := int.ge
  infix ≥  := int.ge
  infix >  := int.gt
  definition decidable_ge [instance] (a b : ℤ) : decidable (a ≥ b) :=
  show decidable (b ≤ a), from _
  definition decidable_gt [instance] (a b : ℤ) : decidable (a > b) :=
  show decidable (b < a), from _
--  definition min : ℤ → ℤ → ℤ := algebra.min
--  definition max : ℤ → ℤ → ℤ := algebra.max
  definition abs : ℤ → ℤ := algebra.abs
  definition sign : ℤ → ℤ := algebra.sign

  migrate from algebra with int
  replacing has_le.ge → ge, has_lt.gt → gt, dvd → dvd, sub → sub, -- min → min, max → max,
            abs → abs, sign → sign

  attribute le.trans ge.trans lt.trans gt.trans [trans]
  attribute lt_of_lt_of_le lt_of_le_of_lt gt_of_gt_of_ge gt_of_ge_of_gt [trans]
end migrate_algebra

/- more facts specific to int -/

theorem of_nat_nonneg (n : ℕ) : 0 ≤ of_nat n := unit.star

theorem of_nat_pos {n : ℕ} (Hpos : #nat n > 0) : of_nat n > 0 :=
of_nat_lt_of_nat_of_lt Hpos

theorem of_nat_succ_pos (n : nat) : of_nat (nat.succ n) > 0 :=
of_nat_pos !nat.succ_pos

theorem exists_eq_of_nat {a : ℤ} (H : 0 ≤ a) : Σn : ℕ, a = of_nat n :=
obtain (n : ℕ) (H1 : 0 + of_nat n = a), from le.elim H,
sigma.mk n (!zero_add ▸ (H1⁻¹))

theorem exists_eq_neg_of_nat {a : ℤ} (H : a ≤ 0) : Σn : ℕ, a = -(of_nat n) :=
have -a ≥ 0, from iff.mp' !neg_nonneg_iff_nonpos H,
obtain (n : ℕ) (Hn : -a = of_nat n), from exists_eq_of_nat this,
sigma.mk n (eq_neg_of_eq_neg (Hn⁻¹))

theorem of_nat_nat_abs_of_nonneg {a : ℤ} (H : a ≥ 0) : of_nat (nat_abs a) = a :=
obtain (n : ℕ) (Hn : a = of_nat n), from exists_eq_of_nat H,
Hn⁻¹ ▸ ap of_nat (nat_abs_of_nat n)

theorem of_nat_nat_abs_of_nonpos {a : ℤ} (H : a ≤ 0) : of_nat (nat_abs a) = -a :=
have -a ≥ 0, from iff.mp' !neg_nonneg_iff_nonpos H,
calc
  of_nat (nat_abs a) = of_nat (nat_abs (-a)) : nat_abs_neg
                 ... = -a                    : of_nat_nat_abs_of_nonneg this

theorem of_nat_nat_abs (b : ℤ) : nat_abs b = abs b :=
sum.rec_on (le.total 0 b)
  (assume H : b ≥ 0, of_nat_nat_abs_of_nonneg H ⬝ (abs_of_nonneg H)⁻¹)
  (assume H : b ≤ 0, of_nat_nat_abs_of_nonpos H ⬝ (abs_of_nonpos H)⁻¹)

theorem nat_abs_abs (a : ℤ) : nat_abs (abs a) = nat_abs a :=
abs.by_cases rfl !nat_abs_neg

theorem lt_of_add_one_le {a b : ℤ} (H : int.add a (of_nat (nat.succ nat.zero)) ≤ b) : a < b :=
obtain n (H1 : int.add (int.add a (of_nat (nat.succ nat.zero))) n = b), from le.elim H,
have a + succ n = b, by rewrite [-H1, add.assoc, add.comm (of_nat (nat.succ nat.zero))],
lt.intro this

theorem add_one_le_of_lt {a b : ℤ} (H : a < b) : int.add a (of_nat (nat.succ nat.zero)) ≤ b :=
obtain n (H1 : int.add a (succ n) = b), from lt.elim H,
have int.add (int.add a 1) n = b, by rewrite [-H1, add.assoc, add.comm 1],
le.intro this

theorem lt_add_one_of_le {a b : ℤ} (H : a ≤ b) : a < b + 1 :=
lt_add_of_le_of_pos H unit.star

theorem le_of_lt_add_one {a b : ℤ} (H : a < b + 1) : a ≤ b :=
have H1 : a + 1 ≤ b + 1, from add_one_le_of_lt H,
le_of_add_le_add_right H1

theorem sub_one_le_of_lt {a b : ℤ} (H : a ≤ b) : a - 1 < b :=
lt_of_add_one_le (!sub_add_cancel⁻¹ ▸ H)

theorem lt_of_sub_one_le {a b : ℤ} (H : a - 1 < b) : a ≤ b :=
!sub_add_cancel ▸ add_one_le_of_lt H

theorem le_sub_one_of_lt {a b : ℤ} (H : a < b) : a ≤ b - 1 :=
le_of_lt_add_one (!sub_add_cancel⁻¹ ▸ H)

theorem lt_of_le_sub_one {a b : ℤ} (H : a ≤ b - 1) : a < b :=
!sub_add_cancel ▸ (lt_add_one_of_le H)

theorem sign_of_succ (n : nat) : sign (nat.succ n) = 1 :=
sign_of_pos (of_nat_pos !nat.succ_pos)

theorem exists_eq_neg_succ_of_nat {a : ℤ} : a < 0 → Σm : ℕ, a = int.neg_succ_of_nat m :=
int.cases_on a
  (take m H, absurd (of_nat_nonneg m : 0 ≤ m) (not_le_of_gt H))
  (take m H, sigma.mk m rfl)

theorem eq_one_of_mul_eq_one_right {a b : ℤ} (H : a ≥ 0) (H' : a * b = 1) : a = 1 :=
have a * b > 0, by rewrite H'; apply unit.star,
have b > 0, from pos_of_mul_pos_left this H,
have a > 0, from pos_of_mul_pos_right `a * b > 0` (le_of_lt `b > 0`),
sum.rec_on (le_or_gt a 1)
  (suppose a ≤ 1,
    show a = 1, from le.antisymm this (add_one_le_of_lt `a > 0`))
  (suppose a > 1,
    assert a * b ≥ 2 * 1,
      from mul_le_mul (add_one_le_of_lt `a > 1`) (add_one_le_of_lt `b > 0`) unit.star H,
    have empty, by rewrite [H' at this]; exact this,
    empty.elim this)

theorem eq_one_of_mul_eq_one_left {a b : ℤ} (H : b ≥ 0) (H' : a * b = 1) : b = 1 :=
eq_one_of_mul_eq_one_right H (!mul.comm ▸ H')

theorem eq_one_of_mul_eq_self_left {a b : ℤ} (Hpos : a ≠ 0) (H : b * a = a) : b = 1 :=
eq_of_mul_eq_mul_right Hpos (H ⬝ (one_mul a)⁻¹)

theorem eq_one_of_mul_eq_self_right {a b : ℤ} (Hpos : b ≠ 0) (H : b * a = b) : a = 1 :=
eq_one_of_mul_eq_self_left Hpos (!mul.comm ▸ H)

theorem eq_one_of_dvd_one {a : ℤ} (H : a ≥ 0) (H' : a ∣ 1) : a = 1 :=
dvd.elim H'
  (take b,
    suppose 1 = a * b,
    eq_one_of_mul_eq_one_right H this⁻¹)

end int
