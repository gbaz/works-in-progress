import types.int algebra.field hit.set_quotient hit.trunc
open eq sigma sigma.ops equiv is_equiv equiv.ops eq.ops int algebra nat set_quotient is_trunc trunc quotient


record prerat : Type := (num : ℤ) (denom : ℕ)

namespace prerat

inductive rat_rel : prerat → prerat → Type :=
 | Rmk : Π (a b : prerat), int.mul (num a) (denom b + int.of_num 1) = int.mul (num b) (denom a + int.of_num 1) → rat_rel a b


/- field operations -/

definition of_int (i : int) : prerat := prerat.mk i (of_num 0)

definition zero : prerat := of_int (of_num 0)

definition one : prerat := of_int (of_num 1)

definition add (a b : prerat) : prerat :=
prerat.mk (num a * (denom b + of_num 1) + num b * (denom a + of_num 1))
  (nat.add
    (nat.add
     (nat.mul (denom a) (denom b))
     (denom a))
    (denom b))

definition mul (a b : prerat) : prerat :=
prerat.mk (num a * num b)   (nat.add
    (nat.add
     (nat.mul (denom a) (denom b))
     (denom a))
    (denom b))
/-
(denom a + 1) * (denom b + 1) - 1
denom a * denom b + denom a + denom b
-/

-- why lord
-- ((nat.mul (denom a) (denom b)) + denom a + denom b)

definition neg (a : prerat) : prerat :=
prerat.mk (- num a) (denom a)

/-TODO have an ordering on the ints so we can give -/

/-
definition smul (a : ℤ) (b : prerat) (H : a > 0) : prerat :=
prerat.mk (a * num b) (int2nat a H * denom b)
-/


definition rat_rel_refl (a : ℤ) (b : ℕ) : rat_rel (mk a b) (mk a b) :=
rat_rel.Rmk (prerat.mk a b) (prerat.mk a b) (refl _)

theorem of_int_add (a b : ℤ) : rat_rel (of_int (#int a + b))  (add (of_int a) (of_int b)) :=
begin
esimp [of_int, add, nat.mul, nat.add, one, zero],
rewrite [int.zero_add, +int.mul_one],
fapply rat_rel_refl
end

theorem of_int_mul (a b : ℤ) : rat_rel (of_int (#int a * b))  (mul (of_int a) (of_int b)) :=
begin
esimp [of_int, add, nat.mul, mul],
rewrite [+nat.zero_add],
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
rewrite[zero_add, +mul_one],
intros,
exact p
end


--set_option pp.all true

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
esimp [of_num],
rewrite [zero_add, zero_mul, mul_one],
intros,
exact p
end


lemma halp {x y : nat} : x * y + x + y + (nat.of_num 1) = nat.mul (nat.add x (nat.of_num 1))  (nat.add y (nat.of_num 1)) :=
begin
rewrite [nat.mul.right_distrib, *nat.mul.left_distrib, *nat.mul_one, nat.one_mul]
end

set_option unifier.max_steps 100000


theorem add_rel_add {a1 b1 a2 b2 : prerat} (r1 : rat_rel a1 a2) (r2 : rat_rel b1 b2) : rat_rel (add a1 b1) (add a2 b2) :=
rat_rel.cases_on r1 (λ a_1 a_2 H1,
rat_rel.cases_on r2 (λ b_1 b_2 H2,
rat_rel.Rmk (add a_1 b_1) (add a_2 b_2)
(calc
num (add a_1 b_1) * of_nat (denom (add a_2 b_2) + 1)
     = num (add a_1 b_1) * of_nat (denom a_2 * denom b_2 + denom a_2 + denom b_2 + 1) : by trivial
 ... = num (add a_1 b_1) * of_nat ((denom a_2 + 1) * (denom b_2 + 1)) : halp
 ... = (num a_1 * (denom b_1 + 1) + num b_1 * (denom a_1 + 1)) * of_nat ((denom a_2 + 1) * (denom b_2 + 1)) : by trivial
--num (add a_2 b_2) * (denom (add a_1 b_1) + 1) : by rewrite [halp]
)
)
)

/-
begin
cases r1 with [a_1, a_2,H1],
cases r2 with [b_1, b_2,H2],
clear [a1,a2,b1,b2],
apply rat_rel.Rmk,
esimp [add],
rewrite [@halp (denom a_2) (denom b_2)]
--rewrite [*mul.right_distrib, *mul.left_distrib, *mul_one, int.mul.comm],
/-exact (
calc
(num a_1 * (denom b_1 + 1) + num b_1 * (denom a_1 + 1)) * (denom a_2 * denom b_2 + denom a_2 + denom b_2 + 1)
  = (num a_2 * (denom
          b_2 + 1) + num b_2 * (denom a_2 + 1)) * (denom a_1 * denom b_1 + denom a_1 + denom b_1 + 1) : by rewrite [mul.right_distrib]
)-/
end
-/

/-
theorem add_equiv_add {a1 b1 a2 b2 : prerat} (eqv1 : a1 ≡ a2) (eqv2 : b1 ≡ b2) :
  add a1 b1 ≡ add a2 b2 :=
calc
  (num a1 * denom b1 + num b1 * denom a1) * (denom a2 * denom b2)
      = num a1 * denom a2 * denom b1 * denom b2 + num b1 * denom b2 * denom a1 * denom a2 :
          by rewrite [mul.right_distrib, *mul.assoc, mul.left_comm (denom b1),
                      mul.comm (denom b2), *mul.assoc]
  ... = num a2 * denom a1 * denom b1 * denom b2 + num b2 * denom b1 * denom a1 * denom a2 :
          by rewrite [↑equiv at *, eqv1, eqv2]
  ... = (num a2 * denom b2 + num b2 * denom a2) * (denom a1 * denom b1) :
          by rewrite [mul.right_distrib, *mul.assoc, *mul.left_comm (denom b2),
                      *mul.comm (denom b1), *mul.assoc, mul.left_comm (denom a2)]
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

definition rat_rel_trunc (a : prerat) (b : prerat) : hprop := trunctype.mk (trunc -1 (prerat.rat_rel a b)) _

definition rat := set_quotient rat_rel_trunc
notation `ℚ` := rat

definition of_int [coercion] (i : ℤ) : ℚ := set_quotient.class_of rat_rel_trunc (prerat.of_int i)
definition of_nat [coercion] (n : ℕ) : ℚ := n
definition of_num [coercion] [reducible] (n : num) : ℚ := n
definition lift0 (p : prerat) : ℚ := set_quotient.class_of rat_rel_trunc p

definition prerat_refl (a : prerat) : rat_rel_trunc a a := tr (prerat.rat_rel.Rmk a a (refl _))
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

definition lift2rat (f : prerat -> prerat -> ℚ) (c : Π (a1 a2 b1 b2 : prerat), rat_rel_trunc a1 a2 → rat_rel_trunc b1 b2 → f a1 b1 = f a2 b2) := @lift2 prerat prerat ℚ (sorry : is_hset ℚ) rat_rel_trunc rat_rel_trunc prerat_refl f c


definition add : ℚ → ℚ → ℚ :=
lift2rat
  (λ a b : prerat, lift0 (prerat.add a b))
  sorry
/-
  (begin
  intros,
  apply (set_quotient.eq_of_rel rat_rel_trunc),
  esimp [prerat.add],
  end)
-/
--  (take a1 a2 b1 b2, assume H1 H2, quot.sound (prerat.add_equiv_add H1 H2))

/-

  protected definition lift₂ [reducible]
     (f : A → B → C)(c : ∀ a₁ a₂ b₁ b₂, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂)
     (q₁ : quot s₁) (q₂ : quot s₂) : C :=
  quot.lift
    (λ a₁, lift (λ a₂, f a₁ a₂) (λ a b H, c a₁ a a₁ b (setoid.refl a₁) H) q₂)
    (λ a b H, ind (λ a', proof c a a' b a' H (setoid.refl a') qed) q₂)
    q₁

definition add : ℚ → ℚ → ℚ :=
quot.lift₂
  (λ a b : prerat, ⟦prerat.add a b⟧)
  (take a1 a2 b1 b2, assume H1 H2, quot.sound (prerat.add_equiv_add H1 H2))


  constant lift      : Π {A B : Type} [s : setoid A] (f : A → B), (∀ a b, a ≈ b → f a = f b) → quot s → B

-/

/-
definition lift2 (f : prerat → prerat → prerat) (coh1 : Π (p q r : prerat), rat_rel_trunc p q →  f p r = f q r) (coh2 : Π (p q r : prerat), rat_rel_trunc p q → f r p = f r q) (r1 r2 : ℚ) : ℚ :=
@set_quotient.elim_on prerat rat_rel_trunc rat r1 sorry (λ x, @set_quotient.elim_on prerat rat_rel_trunc rat r2 sorry (λ y, lift_prerat (f x y))
(λ (a a' : prerat) (myrel: rat_rel_trunc a a'), ap lift_prerat (coh2 a a' x myrel))
)
(begin
intros,
esimp at *,
--rewrite [▸*, -coh1 !a !a' !H]
--rewrite [▸*],
--esimp [lift_prerat, set_quotient.elim_on, set_quotient.elim, set_quotient.rec, trunc.rec_on],
--rewrite [▸*],
end)
-/
/-
(λ (a a' : prerat) (myrel : rat_rel_trunc a a'),
  ap (λ z, @set_quotient.elim_on prerat rat_rel_trunc r2 sorry (λ (y : prerat), (lift_prerat (z y)))
  (λ (a1 a2 : prerat) (myrel : rat_rel_trunc a1 a2), ap lift_prerat (coh2 a1 a2 a myrel)))
  (coh1 a a' myrel))
-/
/-
Π ⦃a a' : prerat⦄,
    trunctype.carrier (rat_rel_trunc a a') →
    set_quotient.elim_on rat_rel_trunc r2 (λ (y : prerat), lift_prerat (f a y))
      (λ (a_1 a' : prerat) (myrel : trunctype.carrier (rat_rel_trunc a_1 a')), ap lift_prerat (coh2 a_1 a' a myrel)) = set_quotient.elim_on
      rat_rel_trunc
      r2
      (λ (y : prerat), lift_prerat (f a' y))
      (λ (a a'_1 : prerat) (myrel : trunctype.carrier (rat_rel_trunc a a'_1)), ap lift_prerat (coh2 a a'_1 a' myrel))


definition lift2' {A : Type} [hs: is_hset A] (f : prerat → ℚ → A) (coh : Π (p q : prerat), Π (p1 q1 : ℚ), (rat_rel_trunc p q → f p p1 = f q q1)) (r1 : rat) (r2 : rat) : A := lift1 (λ x, f x r2)
(begin
intros,
fapply coh,
assumption
end)
r1

definition lift_two {A : Type} [hs: is_hset A] (f : prerat → prerat → A) (coh : Π (p q : prerat), (rat_rel_trunc p q → f p = f q)) (r1 : rat) :  prerat → A := @lift1 (prerat → A) sorry f
(begin
intros,
fapply coh,
assumption
end)
r1

set_option formatter.hide_full_terms false

lemma halp {A : Type} [hs: is_hset A] (f : prerat → prerat → A) (coh : Π (p1 q1), rat_rel_trunc p1 q1 → f p1 = f q1) (r1 : rat) (coh2 : Π (r p1 q1: prerat), f r p1 = f r q1) (p q : prerat) (rel : rat_rel_trunc p q) : lift_two f coh r1 p = lift_two f coh r1 q :=
let foo := lift_two f coh r1 in
begin
fapply elim_eq_of_rel,
end


definition lift2 {A : Type} [hs: is_hset A] (f : prerat → prerat → A) (coh : Π (p1 q1), rat_rel_trunc p1 q1 → f p1 = f q1) (coh2 : Π (r p1 q1: prerat), f r p1 = f r q1) (r1 : rat) (r2 : rat)  : A :=
lift1 (lift_two f coh r1)
(
begin
intros,
fapply halp,
fapply coh2,
assumption
end
)
r2
-/
/-
(
begin
intros,
apply coh
end
)
r2
-/
/-
definition lift2 {A : Type} [hs: is_hset A] (f : prerat → prerat → A) (coh : Π (p1 q1 p2 q2: prerat), rat_rel_trunc p1 q1 → rat_rel_trunc p2 q2 → f p1 p2 = f q1 q2) (r1 : rat) (r2 : rat) : A :=
begin
fapply lift1,
rotate 2,
exact r1,
clear r1,
fapply lift1
end
-/
--set_quotient.elim_on rat_rel_trunc r1 (@lift1 (prerat → A) _ f r2) _
--@lift1 (ℚ → A) sorry (@lift1 f) _ r1 r2



/-
(λ x : prerat, set_quotient.elim_on rat_rel_trunc r2 (f x)
(begin
intros,
apply coh,
fapply prerat_refl,
assumption
end))
sorry
-/
/-
(begin
intros,
end)
-/

--definition add : ℚ → ℚ → ℚ :=
