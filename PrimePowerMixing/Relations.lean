import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic

open Polynomial Finset

namespace PrimePowerMixing

/-- A polynomial of degree below the block width tiles disjoint coefficient
    intervals when multiplied by the prime-power geometric sum. -/
theorem blockCoefficient (Q : ℚ[X]) {s p b r : ℕ} (hQ : Q.natDegree < s)
    (hb : b < p) (hr : r < s) :
    ((∑ k ∈ range p, (X : ℚ[X]) ^ (s*k)) * Q).coeff (r+s*b) = Q.coeff r := by
  rw [Finset.sum_mul, finset_sum_coeff, Finset.sum_eq_single b]
  · exact coeff_X_pow_mul Q (s*b) r
  · intro j _ hj
    rw [coeff_X_pow_mul']
    rcases lt_or_gt_of_ne hj with h | h
    · have hn : s*(j+1) ≤ s*b := Nat.mul_le_mul_left s h
      rw [Nat.mul_add, Nat.mul_one] at hn
      rw [if_pos (by omega)]
      exact coeff_eq_zero_of_natDegree_lt (by omega)
    · have hn : s*(b+1) ≤ s*j := Nat.mul_le_mul_left s h
      rw [Nat.mul_add, Nat.mul_one] at hn
      rw [if_neg (by omega)]
  · simp [hb]

/-- At a primitive prime-power root, a vanishing rational polynomial of
    degree less than the order has identical coefficient rows of width p^n.
    Applying this to the symmetric relation polynomial in the manuscript
    gives the equality of coefficients on each residue block. -/
theorem vanishing_coefficients {p n : ℕ} (hp : p.Prime) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (p^(n+1))) (P : ℚ[X])
    (hP : P.natDegree < p^(n+1)) (hv : aeval ζ P = 0)
    {b r : ℕ} (hb : b < p) (hr : r < p^n) :
    P.coeff (r+p^n*b) = P.coeff r := by
  have hpos : 0 < p^(n+1) := pow_pos hp.pos _
  haveI : NeZero ((p^(n+1) : ℕ) : ℚ) := ⟨by exact_mod_cast hpos.ne'⟩
  obtain ⟨Q,hQ⟩ : cyclotomic (p^(n+1)) ℚ ∣ P := by
    rw [hζ.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat hpos)]
    exact minpoly.dvd _ _ hv
  by_cases hzero : Q = 0
  · simp [hQ,hzero]
  have hwidth : Q.natDegree < p^n := by
    rw [hQ, natDegree_mul (cyclotomic_ne_zero _ _) hzero, natDegree_cyclotomic,
      Nat.totient_prime_pow hp (Nat.succ_pos n)] at hP
    simp only [Nat.add_one_sub_one] at hP
    rw [pow_succ] at hP
    have hrec : p^n * (p-1) + p^n = p^n * p := by
      rw [← Nat.mul_succ]
      exact congrArg (p^n * ·) (Nat.sub_add_cancel hp.one_le)
    omega
  rw [hQ, cyclotomic_prime_pow_eq_geom_sum hp]
  simp_rw [← pow_mul]
  rw [blockCoefficient Q hwidth hb hr]
  simpa using (blockCoefficient Q hwidth hp.pos hr).symm

/-- The coefficient-block criterion is sufficient as well as necessary.
    The quotient is the polynomial given by the first block of coefficients. -/
theorem vanishing_iff_blocks {p n : ℕ} (hp : p.Prime) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (p^(n+1))) (P : ℚ[X])
    (hP : P.natDegree < p^(n+1)) :
    aeval ζ P = 0 ↔
      ∀ b < p, ∀ r < p^n, P.coeff (r+p^n*b) = P.coeff r := by
  constructor
  · intro h b hb r hr
    exact vanishing_coefficients hp hζ P hP h hb hr
  · intro hblocks
    let s := p^n
    let Q : ℚ[X] := ∑ r ∈ range s, monomial r (P.coeff r)
    have hs : 0 < s := pow_pos hp.pos _
    have hQdeg : Q.natDegree < s := by
      unfold Q
      refine (natDegree_sum_le_of_forall_le _ _ (n := s-1) ?_).trans_lt (by omega)
      intro i hi
      have hil := mem_range.mp hi
      exact (natDegree_monomial_le _).trans (by omega)
    have hQcoeff (r : ℕ) (hr : r < s) : Q.coeff r = P.coeff r := by
      simp [Q, finset_sum_coeff, coeff_monomial, hr]
    let Z := cyclotomic (p^(n+1)) ℚ
    have hZ : Z.natDegree = s*(p-1) := by
      simp [Z, s, natDegree_cyclotomic, Nat.totient_prime_pow hp (Nat.succ_pos n)]
    have hq : p^(n+1) = s*(p-1)+s := by
      unfold s
      rw [pow_succ, ← Nat.mul_succ]
      exact congrArg (p^n * ·) (Nat.sub_add_cancel hp.one_le).symm
    have hprod : (Z*Q).natDegree < p^(n+1) := by
      calc
        _ ≤ Z.natDegree + Q.natDegree := natDegree_mul_le
        _ < p^(n+1) := by rw [hZ, hq]; omega
    have hEq : P = Z*Q := by
      ext k
      by_cases hk : k < p^(n+1)
      · have hb : k/s < p := (Nat.div_lt_iff_lt_mul hs).mpr (by
          simpa [s, pow_succ, Nat.mul_comm] using hk)
        have hr := Nat.mod_lt k hs
        rw [← Nat.mod_add_div k s, hblocks _ hb _ hr]
        dsimp [Z]
        rw [cyclotomic_prime_pow_eq_geom_sum hp]
        simp_rw [← pow_mul]
        rw [blockCoefficient Q hQdeg hb hr, hQcoeff _ hr]
      · rw [coeff_eq_zero_of_natDegree_lt (hP.trans_le (by omega)),
          coeff_eq_zero_of_natDegree_lt (hprod.trans_le (by omega))]
    have hpos : 0 < p^(n+1) := pow_pos hp.pos _
    haveI : NeZero ((p^(n+1) : ℕ) : ℚ) := ⟨by exact_mod_cast hpos.ne'⟩
    have hz : aeval ζ Z = 0 := by
      dsimp [Z]
      rw [hζ.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat hpos)]
      exact minpoly.aeval ℚ ζ
    rw [hEq, map_mul, hz, zero_mul]

end PrimePowerMixing
