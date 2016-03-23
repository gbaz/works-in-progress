import types.int algebra.field hit.set_quotient hit.trunc int_order
open eq sigma sigma.ops equiv is_equiv equiv.ops eq.ops int algebra set_quotient is_trunc trunc quotient

record prerat : Type := (num : ℤ) (denom : ℤ) --(dp : denom > 0)

inductive rat_rel : prerat → prerat → Type :=
 | Rmk : Π (a b : prerat), int.mul (prerat.num a) (prerat.denom b) =
                           int.mul (prerat.num b) (prerat.denom a)
         → rat_rel a b

namespace prerat

definition of_int (i : int) : prerat := prerat.mk i (of_num 1)

definition zero : prerat := of_int (of_num 0)

definition one : prerat := of_int (of_num 1)

definition add (a b : prerat) : prerat :=
prerat.mk (num a * denom b + num b * denom a) (denom a * denom b)

definition mul (a b : prerat) : prerat :=
prerat.mk (num a * num b) (denom a * denom b)

definition neg (a : prerat) : prerat :=
prerat.mk (- num a) (denom a)

definition rat_rel_refl (a : ℤ) (b : ℤ) : rat_rel (mk a b) (mk a b) :=
rat_rel.Rmk (prerat.mk a b) (prerat.mk a b) (refl _)

theorem of_int_add (a b : ℤ) : rat_rel (of_int (#int a + b))  (add (of_int a) (of_int b)) :=
begin
esimp [of_int, add, nat.mul, nat.add, one, zero],
rewrite [+int.mul_one],
fapply rat_rel_refl
end

theorem of_int_mul (a b : ℤ) : rat_rel (of_int (#int a * b))  (mul (of_int a) (of_int b)) :=
begin
esimp [of_int, add, nat.mul, mul],
rewrite [+int.mul_one],
fapply rat_rel_refl
end

theorem of_int_neg (a : ℤ) : rat_rel (of_int (#int -a)) (neg (of_int a)) :=
begin
esimp [neg, of_int],
fapply rat_rel_refl
end


theorem of_int.inj {a b : ℤ} : rat_rel (of_int a) (of_int b) → a = b :=
begin
intros,
cases a_1 with [a,b,p],
generalize p,
clear p,
esimp [denom],
rewrite[+mul_one],
intros,
exact p
end


theorem equiv_zero_of_num_eq_zero {a : prerat} (H : num a = of_num 0) : rat_rel a zero :=
rat_rel.Rmk a zero (
begin
rewrite [H],
esimp [zero, of_int, num],
rewrite[+zero_mul]
end
)

theorem num_eq_zero_of_equiv_zero {a : prerat} : rat_rel a zero → num a = 0 :=
begin
intros,
cases a_1 with [a,z,p],
generalize p,
clear p,
esimp [denom],
rewrite [zero_mul,mul_one],
exact (λ x, x),
end

theorem add_rel_add {a1 b1 a2 b2 : prerat} (r1 : rat_rel a1 a2) (r2 : rat_rel b1 b2) : rat_rel (add a1 b1) (add a2 b2) :=
rat_rel.cases_on r1 (λ a_1 a_2 H1,
rat_rel.cases_on r2 (λ b_1 b_2 H2,
rat_rel.Rmk (add a_1 b_1) (add a_2 b_2)
(calc
      num (add a_1 b_1) * denom (add a_2 b_2)
    = (num a_1 * denom b_1 + num b_1 * denom a_1) * (denom a_2 * denom b_2) : by esimp [add]
... = num a_1 * denom a_2 * denom b_1 * denom b_2 + num b_1 * denom b_2 * denom a_1 * denom a_2 :
         by rewrite [mul.right_distrib, *mul.assoc, mul.left_comm (denom b_1), mul.comm (denom b_2), *mul.assoc]
... = num a_2 * denom a_1 * denom b_1 * denom b_2 + num b_2 * denom b_1 * denom a_1 * denom a_2 :
         by rewrite [H1, H2]
... = (num a_2 * denom b_2 + num b_2 * denom a_2) * (denom a_1 * denom b_1) :
         by rewrite [mul.right_distrib, *mul.assoc, *mul.left_comm (denom b_2), *mul.comm (denom b_1), *mul.assoc, mul.left_comm (denom a_2)]
)
))

/- field operations -/
/-TODO have an ordering on the ints so we can give -/
/-
definition smul (a : ℤ) (b : prerat) (H : a > 0) : prerat :=
prerat.mk (a * num b) (int2nat a H * denom b)
-/


end prerat

/-

definition inv : prerat → prerat
| inv (prerat.mk nat.zero d dp)     := zero
| inv (prerat.mk (nat.succ n) d dp) := prerat.mk d (nat.succ n) !of_nat_succ_pos
| inv (prerat.mk -[1+n] d dp)       := prerat.mk (-d) (nat.succ n) !of_nat_succ_pos


theorem inv_zero {d : int} (dp : d > 0) : inv (mk nat.zero d dp) = zero :=
begin rewrite [↑inv, ▸*] end

theorem inv_zero' : inv zero = zero := inv_zero (of_nat_succ_pos nat.zero)

theorem inv_of_pos {n d : int} (np : n > 0) (dp : d > 0) : inv (mk n d dp) ≡ mk d n np :=
obtain (n' : nat) (Hn' : n = of_nat n'), from exists_eq_of_nat (le_of_lt np),
have (#nat n' > nat.zero), from lt_of_of_nat_lt_of_nat (Hn' ▸ np),
obtain (k : nat) (Hk : n' = nat.succ k), from nat.exists_eq_succ_of_lt this,
have d * n = d * nat.succ k, by rewrite [Hn', Hk],
Hn'⁻¹ ▸ (Hk⁻¹ ▸ this)

theorem inv_neg {n d : int} (np : n > 0) (dp : d > 0) : inv (mk (-n) d dp) ≡ mk (-d) n np :=
obtain (n' : nat) (Hn' : n = of_nat n'), from exists_eq_of_nat (le_of_lt np),
have (#nat n' > nat.zero), from lt_of_of_nat_lt_of_nat (Hn' ▸ np),
obtain (k : nat) (Hk : n' = nat.succ k), from nat.exists_eq_succ_of_lt this,
have -d * n = -d * nat.succ k, by rewrite [Hn', Hk],
have H3 : inv (mk -[1+k] d dp) ≡ mk (-d) n np, from this,
have H4 : -[1+k] = -n, from calc
  -[1+k] = -(nat.succ k) : rfl
      ... = -n            : by rewrite [Hk⁻¹, Hn'],
H4 ▸ H3

theorem inv_of_neg {n d : int} (nn : n < 0) (dp : d > 0) :
  inv (mk n d dp) ≡ mk (-d) (-n) (neg_pos_of_neg nn) :=
have inv (mk (-(-n)) d dp) ≡ mk (-d) (-n) (neg_pos_of_neg nn),
  from inv_neg (neg_pos_of_neg nn) dp,
!neg_neg ▸ this

theorem of_int.inj {a b : ℤ} : of_int a ≡ of_int b → a = b :=
by rewrite [↑of_int, ↑equiv, *mul_one]; intros; assumption

-/


/-
  the rationals
-/
namespace rat

definition rat_rel_trunc (a : prerat) (b : prerat) : hprop := trunctype.mk (trunc -1 (rat_rel a b)) _

definition rat := set_quotient rat_rel_trunc
notation `ℚ` := rat

open nat
definition of_int [coercion] (i : ℤ) : ℚ := set_quotient.class_of rat_rel_trunc (prerat.of_int i)
definition of_nat [coercion] (n : ℕ) : ℚ := n
definition of_num [coercion] [reducible] (n : num) : ℚ := n
definition lift0 (p : prerat) : ℚ := set_quotient.class_of rat_rel_trunc p

definition prerat_refl (a : prerat) : rat_rel_trunc a a := tr (rat_rel.Rmk a a (refl _))
definition lift1 {A : Type} [hs : is_hset A] (f : prerat → A) (coh : Π (p q : prerat), rat_rel_trunc p q -> f p = f q) (r : rat) : A :=
set_quotient.elim_on rat_rel_trunc r f coh

/-
lemma ext_c {A B C : Type}  {rel_a : A → A → hprop} {rel_b : B → B → hprop} (f : A -> B -> C) (c : Π (a1 a2 : A) (b1 b2 : B) , rel_a a1 a2 → rel_b b1 b2 → f a1 b1 = f a2 b2) : Π (a1 a2 : A), rel_a a1 a2 → f a1 = f a2 :=
λ (a1 a2 : A) (myrel : rel_a a1 a2), _ (λ (b : B), (c a1 a2 b b myrel sorry))
-/

set_option formatter.hide_full_terms false

definition lift2 {A B C : Type} [hs : is_hset C] {rel_a : A → A → hprop} {rel_b : B → B → hprop} (rel_a_refl : Π (a : A), rel_a a a) (f : A -> B -> C) (c : Π (a1 a2 : A) (b1 b2 : B) , rel_a a1 a2 → rel_b b1 b2 → f a1 b1 = f a2 b2) (q1 : set_quotient rel_a) (q2 : set_quotient rel_b) : C :=
set_quotient.elim_on
 rel_a
 q1
 (λ a, set_quotient.elim_on rel_b q2 (f a) (begin intros, apply c, exact (rel_a_refl a), assumption end))
 sorry
/-
 (λ (a a' : A) (H : rel_a a a'), ap (λ a1, set_quotient.elim_on rel_b q2 (f a1) (begin intros, apply c, exact (rel_a_refl a1), assumption end)) (ext_c f c a a' H))
-/

theorem rat_is_hset : is_hset ℚ := set_quotient.is_hset_set_quotient rat_rel_trunc

definition lift2rat (f : prerat -> prerat -> ℚ) (c : Π (a1 a2 b1 b2 : prerat), rat_rel_trunc a1 a2 → rat_rel_trunc b1 b2 → f a1 b1 = f a2 b2) := @lift2 prerat prerat ℚ (rat_is_hset) rat_rel_trunc rat_rel_trunc prerat_refl f c

definition add : ℚ → ℚ → ℚ :=
lift2rat
  (λ a b : prerat, lift0 (prerat.add a b))
  (begin
  intros,
  apply (set_quotient.eq_of_rel rat_rel_trunc),
  apply (trunc.elim_on a (λ a', trunc.elim_on a_1 (λ a_1', tr (prerat.add_rel_add a' a_1'))))
  end)

end rat
