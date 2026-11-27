import Mathlib.Tactic

namespace PrimePowerMixing

/-- Summing a product over ordered pairs of distinct slots removes the diagonal.
    This identity also applies when distinct slots carry the same phase. -/
theorem offDiagonal_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z w : ι → ℂ) :
    (∑ i, ∑ j, (if i = j then 0 else z i * w j)) =
      (∑ i, z i) * (∑ j, w j) - ∑ i, z i * w i := by
  classical
  have h (i : ι) :
      (∑ j, (if i = j then 0 else z i * w j)) + z i * w i = ∑ j, z i * w j := by
    calc
      _ = (∑ j, (if i = j then 0 else z i * w j)) +
          ∑ j, (if i = j then z i * w j else 0) := by simp
      _ = _ := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        split <;> simp_all
  rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => (h i).trans (Finset.mul_sum ..).symm

/-- For unit phases with zero sum, the average over different slots is
    -1/(K-1). Conjugation is written as 'star'. -/
theorem withoutReplacement {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → ℂ) (hK : 1 < Fintype.card ι) (hz : ∑ i, z i = 0)
    (hu : ∀ i, z i * star (z i) = 1) :
    (∑ i, ∑ j, (if i = j then 0 else z i * star (z j))) /
        ((Fintype.card ι : ℂ) * (Fintype.card ι - 1)) =
      -1 / (Fintype.card ι - 1) := by
  have hk : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast (by omega : Fintype.card ι ≠ 0)
  have hk' : (Fintype.card ι : ℂ) ≠ 1 := by exact_mod_cast (by omega : Fintype.card ι ≠ 1)
  rw [offDiagonal_sum, hz, zero_mul]
  simp only [hu, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, zero_sub]
  field_simp [hk, sub_ne_zero.mpr hk']

/-- Two block laws and a zero-moment component realize the prescribed real
    two-point moments with strictly positive probabilities. The input h is
    the magnitude of the across-block anticorrelation of the second law. -/
theorem momentWeights (p s h : ℝ) (hp : 1 < p) (hs : 1 < s)
    (hslack : 1 < (s-1)*h) :
    ∃ a b u : ℝ, 0 < a ∧ 0 < b ∧ 0 < u ∧ a + b + u = 1 ∧
      a * (-(1 / (p-1))) + b = -(1 / (p*s-1)) ∧
      b * (-h) = -(1 / (p*s-1)) := by
  have hh : 0 < h := by by_contra! hn; nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ s-1) hn]
  have hN : 0 < p*s-1 := by nlinarith [mul_pos (by linarith : 0 < p-1) (by linarith : 0 < s-1)]
  let d := h * (p*s-1)
  have hd : 0 < d := mul_pos hh hN
  let a := (p-1)*(1+h)/d
  let b := 1/d
  refine ⟨a,b,1-a-b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact div_pos (mul_pos (by linarith) (by linarith)) hd
  · exact one_div_pos.mpr hd
  · dsimp [a,b]
    have hsum : (p-1)*(1+h) + 1 < d := by
      dsimp [d]
      nlinarith [mul_pos (by linarith : 0 < p) (sub_pos.mpr hslack)]
    have := (div_lt_one hd).mpr hsum
    rw [add_div] at this
    linarith
  · ring
  · dsimp [a,b,d]
    field_simp [ne_of_gt hh, ne_of_gt hN, sub_ne_zero.mpr hp.ne']
    ring
  · dsimp [b,d]
    field_simp [ne_of_gt hh, ne_of_gt hN]

end PrimePowerMixing
