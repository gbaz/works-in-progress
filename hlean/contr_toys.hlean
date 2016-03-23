import types.nat types.sigma hit.trunc

open nat sigma is_trunc trunc eq prod

definition isFive : ℕ -> Type.{0} := λ x, prod (5 ≤ x) (x ≤ 5)

definition fiveIsFive : sigma isFive := sigma.mk 5 (prod.mk (le.refl 5) (le.refl 5))

definition isFive.elim {n : ℕ} (x : isFive n) : 5 = n := prod.rec
begin
intros,
exfalso,
discard x
end
x


check prod.rec
print classes
print fields algebra.linear_ordered_semiring

/-
definition isFive.elim {n : ℕ} (x : isFive n) : 5 = n := prod.rec le.antisymm x

definition isFiveIsContr : is_contr (sigma isFive) :=
is_contr.mk fiveIsFive
(λ x, sigma_eq
    (sigma.rec_on x (λ n p, isFive.elim p))
    (sigma.rec_on x (λ n p, pathover_of_tr_eq (prod_eq (is_hprop.elim _ _) (is_hprop.elim _ _)))))

definition isFiveIsTr : is_hprop (sigma isFive) := @is_trunc_of_is_contr _ _ (isFiveIsContr)

definition isFiveTr : trunc -1 (sigma isFive) := tr fiveIsFive

definition elimFromTrunc : ℕ := pr1 (@trunc.elim _ _ _ isFiveIsTr (λ x, x) isFiveTr)

eval elimFromTrunc
-/
