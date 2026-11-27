import PrimePowerMixing.Relations

open Polynomial

namespace PrimePowerMixing.EightSites

private noncomputable def modePoly (j : ℕ) : ℚ[X] := X ^ j + X ^ (9 - j)

/-- The even-mode energies of the eight-site path in root-of-unity
    coordinates, for j = 1, 2, 3, 4. -/
def energy (ζ : ℂ) (j : ℕ) : ℂ := ζ ^ j + ζ ^ (9 - j)

private theorem eval_modePoly (ζ : ℂ) (j : ℕ) :
    aeval ζ (modePoly j) = energy ζ j := by
  simp [modePoly, energy]

/-- The full block is {1,2,4} and 3 is free. Every rational relation on the
    even-mode energies is a scalar multiple of the single block relation. -/
theorem energyRelation {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 9) (a b c d : ℚ) :
    (a : ℂ) * energy ζ 1 + (b : ℂ) * energy ζ 2 +
      (c : ℂ) * energy ζ 3 + (d : ℂ) * energy ζ 4 = 0 ↔
      a = b ∧ b = d ∧ c = 0 := by
  let P : ℚ[X] := C a * modePoly 1 + C b * modePoly 2 + C c * modePoly 3 + C d * modePoly 4
  have hP : P.natDegree < 9 := by
    unfold P modePoly
    norm_num
    compute_degree
    omega
  have heval : aeval ζ P = (a : ℂ) * energy ζ 1 + (b : ℂ) * energy ζ 2 +
      (c : ℂ) * energy ζ 3 + (d : ℂ) * energy ζ 4 := by
    simp [P, eval_modePoly]
  have hcoeff (k : ℕ) :
      P.coeff k = a * ((if 1 = k then 1 else 0) + (if 8 = k then 1 else 0)) +
        b * ((if 2 = k then 1 else 0) + (if 7 = k then 1 else 0)) +
        c * ((if 3 = k then 1 else 0) + (if 6 = k then 1 else 0)) +
        d * ((if 4 = k then 1 else 0) + (if 5 = k then 1 else 0)) := by
    norm_num [P, modePoly, coeff_X_pow, coeff_X, eq_comm]
  constructor
  · intro h
    have hv : aeval ζ P = 0 := heval.trans h
    have H {r b : ℕ} (hr : r < 3) (hb : b < 3) :
        P.coeff (r+3*b) = P.coeff r :=
      vanishing_coefficients (p := 3) (n := 1) (by decide) hζ P hP hv hb hr
    have h41 := H (r := 1) (b := 1) (by decide) (by decide)
    have h52 := H (r := 2) (b := 1) (by decide) (by decide)
    have h30 := H (r := 0) (b := 1) (by decide) (by decide)
    norm_num [hcoeff] at h41 h52 h30
    exact ⟨h41.symm.trans h52, h52.symm, h30⟩
  · rintro ⟨rfl, rfl, rfl⟩
    have hpoly : P = cyclotomic 9 ℚ * (C a * (X + X ^ 2)) := by
      have hc := cyclotomic_prime_pow_eq_geom_sum (R := ℚ) (p := 3) (n := 1) (by decide)
      rw [show cyclotomic 9 ℚ = _ from hc]
      norm_num [P, modePoly, Finset.sum_range_succ]
      ring
    have hroot : aeval ζ (cyclotomic 9 ℚ) = 0 := by
      rw [hζ.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat (by decide))]
      exact minpoly.aeval ℚ ζ
    rw [← heval, hpoly, map_mul, hroot, zero_mul]

end PrimePowerMixing.EightSites
