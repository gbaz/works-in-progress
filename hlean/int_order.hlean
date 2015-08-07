import algebra.ordered_ring types.int algebra.order
open prod decidable sum eq sigma sigma.ops int algebra nat

namespace int

private definition nonneg (a : ℤ) : Type.{0} := int.cases_on a (λ n, unit) (λ n, empty)

definition le (a b : ℤ) : Type.{0} := nonneg (b - a)
definition lt (a b : ℤ) : Type.{0} := le (a + 1) b

definition int.has_le [instance] : has_le ℤ := has_le.mk le
definition int.has_lt [instance] : has_lt ℤ := has_lt.mk le

local attribute nonneg [reducible]

private definition decidable_nonneg [instance] (a : ℤ) : decidable (nonneg a) := int.cases_on a _ _
definition decidable_le [instance] (a b : ℤ) : decidable (a ≤ b) := decidable_nonneg _
definition decidable_lt [instance] (a b : ℤ) : decidable (a < b) := decidable_nonneg _

private theorem nonneg.elim {a : ℤ} : nonneg a → Σ(n : ℕ), a = n :=
int.cases_on a (λ n H, sigma.mk n rfl) (λ n, empty.elim)


private theorem nonneg_or_nonneg_neg (a : ℤ) : nonneg a ⊎ nonneg (-a) :=
int.cases_on a (λ n, sum.inl (nonneg n)) (λ n, sum.inl (nonneg (-n)))
end int
/-

private theorem nonneg_or_nonneg_neg (a : ℤ) : nonneg a ∨ nonneg (-a) :=
int.cases_on a (take n, or.inl trivial) (take n, or.inr trivial)

theorem le.intro {a b : ℤ} {n : ℕ} (H : a + n = b) : a ≤ b :=
have n = b - a, from eq_add_neg_of_add_eq (!add.comm ▸ H),
show nonneg (b - a), from this ▸ trivial

theorem le.elim {a b : ℤ} (H : a ≤ b) : ∃n : ℕ, a + n = b :=
obtain (n : ℕ) (H1 : b - a = n), from nonneg.elim H,
exists.intro n (!add.comm ▸ iff.mpr !add_eq_iff_eq_add_neg (H1⁻¹))

infix [priority int.prio] - := int.sub
infix [priority int.prio] <= := int.le
infix [priority int.prio] ≤  := int.le
infix [priority int.prio] <  := int.lt
-/
