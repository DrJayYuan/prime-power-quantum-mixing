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

/-- The eigenenergy of mode k of the n-site nearest-neighbor chain.
    The physical mode index is k+1. -/
noncomputable def modeEnergy (n : ℕ) (k : Fin n) : ℝ :=
  2 * Real.cos (Real.pi * (k.val + 1) / (n + 1))

/-- The (u,v) entry of the rank-one sine-mode projector. -/
noncomputable def sineProjector (n : ℕ) (u v k : Fin n) : ℝ :=
  2 / (n + 1) *
    Real.sin (Real.pi * (u.val + 1) * (k.val + 1) / (n + 1)) *
    Real.sin (Real.pi * (v.val + 1) * (k.val + 1) / (n + 1))

/-- Site transition probability in the chain's sine spectral representation. -/
noncomputable def pathProbability (n : ℕ) (u v : Fin n) (t : ℕ) : ℝ :=
  readout (sineProjector n u v) (fun k => t * modeEnergy n k)

/-- The natural-time theorem's conclusion in the sine spectral representation. -/
def UniformReadout (n : ℕ) : Prop :=
  ∃ (s : ℕ) (time : Fin s → ℕ) (weight : Fin s → ℝ),
    s ≤ n^2 / 4 + 1 ∧
    (∀ j, 0 < weight j) ∧ (∑ j, weight j) = 1 ∧
    ∀ u v : Fin n, (∑ j, weight j * pathProbability n u v (time j)) = 1 / (n : ℝ)

/-- A parity label on zero-based mode indices. Equality of the labels is
    equivalent to equal parity of the physical indices. -/
def modeParity {n : ℕ} (k : Fin n) : Bool := k.val % 2 == 0

/-- A concrete version of the spectral reduction for the path. The two
    sine-basis identities are stated as hypotheses so the remaining input
    is explicit. -/
theorem uniformReadout_of_schedule {n : ℕ} (hn : 0 < n) {s : ℕ}
    (time : Fin s → ℕ) (weight : Fin s → ℝ)
    (hsize : s ≤ n^2 / 4 + 1) (hw₀ : ∀ j, 0 < weight j) (hw₁ : ∑ j, weight j = 1)
    (hDiag : ∀ u v : Fin n, (∑ k, sineProjector n u v k ^ 2) =
      (2 + ((if u = v then 1 else 0) + (if u.val + v.val + 1 = n then 1 else 0) : ℝ)) /
        (2 * (n + 1)))
    (hSame : ∀ u v : Fin n, (∑ k, ∑ l, if modeParity k = modeParity l then
        sineProjector n u v k * sineProjector n u v l else 0) =
      ((if u = v then 1 else 0) + (if u.val + v.val + 1 = n then 1 else 0) : ℝ) / 2)
    (hMom : ∀ k l : Fin n, (∑ t, weight t *
        Real.cos ((time t : ℝ) * (modeEnergy n k - modeEnergy n l))) =
      if k = l then 1 else if modeParity k = modeParity l then -(1/(n : ℝ)) else 0) :
    UniformReadout n := by
  refine ⟨s,time,weight,hsize,hw₀,hw₁,fun u v => ?_⟩
  unfold pathProbability
  apply uniform_of_parity_moments (n : ℝ)
    ((if u = v then 1 else 0) + (if u.val + v.val + 1 = n then 1 else 0))
    (by exact_mod_cast hn) modeParity
  · exact hDiag u v
  · exact hSame u v
  · intro k l
    simpa only [mul_sub] using hMom k l

end PrimePowerMixing
