import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace PrimePowerMixing

/-- Squared modulus of an amplitude with real spectral coefficients. -/
noncomputable def readout {ι : Type*} [Fintype ι] (v angle : ι → ℝ) : ℝ :=
  (∑ k, v k * Real.cos (angle k)) ^ 2 + (∑ k, v k * Real.sin (angle k)) ^ 2

theorem readout_eq_pairSum {ι : Type*} [Fintype ι] (v angle : ι → ℝ) :
    readout v angle = ∑ k, ∑ l, v k * v l * Real.cos (angle k - angle l) := by
  unfold readout
  simp only [pow_two, Finset.sum_mul_sum, Real.cos_sub, mul_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Averaging a readout replaces each cosine by the corresponding averaged
    moment. The formula works for arbitrary finite real spectral data. -/
theorem average_readout_eq_moments {ι τ : Type*} [Fintype ι] [Fintype τ]
    (v : ι → ℝ) (w : τ → ℝ) (angle : τ → ι → ℝ) :
    ∑ t, w t * readout v (angle t) =
      ∑ k, ∑ l, v k * v l * (∑ t, w t * Real.cos (angle t k - angle t l)) := by
  simp only [readout_eq_pairSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- If the two site identities in the sine eigenbasis hold, the prescribed
    mode moments force the uniform site probability. The second identity is the
    sum over ordered equal-parity pairs, including the diagonal. -/
theorem uniform_of_parity_moments {ι τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype τ]
    (N R : ℝ) (hN : 0 < N) (parity : ι → Bool) (v : ι → ℝ) (w : τ → ℝ)
    (angle : τ → ι → ℝ)
    (hDiag : ∑ k, v k ^ 2 = (2 + R) / (2 * (N + 1)))
    (hSame : (∑ k, ∑ l, if parity k = parity l then v k * v l else 0) = R / 2)
    (hMom : ∀ k l, (∑ t, w t * Real.cos (angle t k - angle t l)) =
      if k = l then 1 else if parity k = parity l then -(1/N) else 0) :
    ∑ t, w t * readout v (angle t) = 1/N := by
  classical
  rw [average_readout_eq_moments]
  simp_rw [hMom]
  have hTerms (k l : ι) :
      v k * v l * (if k = l then 1 else if parity k = parity l then -(1/N) else 0) =
        (1 + 1/N) * (if k = l then v k ^ 2 else 0) -
          (1/N) * (if parity k = parity l then v k * v l else 0) := by
    by_cases h : k = l
    · subst l
      simp
      ring
    · by_cases hp : parity k = parity l
      · simp [h, hp]
        ring
      · simp [h, hp]
  simp_rw [hTerms, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hDiag, hSame]
  field_simp [show N + 1 ≠ 0 by linarith, ne_of_gt hN]
  ring

end PrimePowerMixing
