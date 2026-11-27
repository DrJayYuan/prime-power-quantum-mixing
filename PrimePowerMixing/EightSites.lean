import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace PrimePowerMixing.EightSites

/-- Seventy-two equiprobable outcomes. Columns are the even modes in order
    2,4,6,8. Entries are exponents of exp(iπ/3). Modes 2,4,8 form one block. -/
def phase (t : Fin 72) (j : Fin 4) : Nat :=
  let a := t.val
  if a < 36 then
    let offset := a % 3
    let step := 1 + a / 3 % 2
    let single := a / 6 % 3
    2 * (match j.val with
      | 0 => offset
      | 1 => (offset + step) % 3
      | 2 => single
      | _ => (offset + 2*step) % 3)
  else if a < 45 then
    let common := 2 * (a % 3)
    (common + (if j.val = 2 then 3 else 0)) % 6
  else
    let u := a % 3
    let v := a / 3 % 3
    2 * (match j.val with
      | 0 => u
      | 1 => v
      | 2 => a / 9 % 3
      | _ => (6-u-v) % 3)

/-- Twice the real part of the kth sixth root of unity. -/
def twiceCos (k : Nat) : Int :=
  match k % 6 with
  | 0 => 2
  | 1 | 5 => 1
  | 2 | 4 => -1
  | _ => -2

theorem blockConstraint : ∀ t : Fin 72,
    (phase t 0 + phase t 1 + phase t 3) % 6 = 0 := by decide +kernel

/-- Site modes are numbered 1 through 8; Lean indices start at zero.
    Mirror-related modes have opposite phase. -/
def modePhase (t : Fin 72) (k : Fin 8) : Nat :=
  let j : Fin 4 := ⟨if k.val % 2 = 1 then k.val / 2 else (7-k.val) / 2, by
    have := k.isLt
    split <;> omega⟩
  if k.val % 2 = 1 then phase t j else (6 - phase t j) % 6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Summing twice the cosine over 72 outcomes gives 144 on the diagonal,
    -18 at distinct equal-parity modes and zero otherwise. -/
theorem exactMoments : ∀ k l : Fin 8,
    (∑ t : Fin 72, twiceCos (modePhase t k + 6 - modePhase t l)) =
      (if k = l then 144 else if k.val % 2 = l.val % 2 then -18 else 0) := by
  decide +kernel

private theorem cosTable (r : Fin 6) :
    (twiceCos r : ℝ) = 2 * Real.cos ((r : ℝ) * (Real.pi / 3)) := by
  have h₂ : Real.cos (2 * (Real.pi / 3)) = -(1/2 : ℝ) := by
    rw [Real.cos_two_mul, Real.cos_pi_div_three]
    norm_num
  have h₄ : Real.cos (4 * (Real.pi / 3)) = -(1/2 : ℝ) := by
    rw [show 4 * (Real.pi / 3) = Real.pi + Real.pi/3 by ring,
      add_comm, Real.cos_add_pi, Real.cos_pi_div_three]
  have h₅ : Real.cos (5 * (Real.pi / 3)) = 1/2 := by
    rw [show 5 * (Real.pi / 3) = 2*Real.pi - Real.pi/3 by ring,
      Real.cos_two_pi_sub, Real.cos_pi_div_three]
  fin_cases r <;> norm_num [twiceCos, Real.cos_pi_div_three, h₂, h₄, h₅,
    show 3 * (Real.pi / 3) = Real.pi by ring]

theorem twiceCos_correct (n : Nat) :
    (twiceCos n : ℝ) = 2 * Real.cos ((n : ℝ) * (Real.pi / 3)) := by
  let r : Fin 6 := ⟨n % 6, Nat.mod_lt _ (by decide)⟩
  have h : (n : ℝ) = (r.val : ℝ) + 6 * ((n / 6 : Nat) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div n 6).symm
  have hr : twiceCos n = twiceCos r.val := by simp [r, twiceCos]
  rw [hr, cosTable r]
  conv_rhs => rw [h]
  rw [show ((r.val : ℝ) + 6 * ((n / 6 : Nat) : ℝ)) * (Real.pi / 3) =
    r.val * (Real.pi / 3) + (n / 6 : Nat) * (2 * Real.pi) by ring,
    Real.cos_add_nat_mul_two_pi]

private theorem modePhase_lt : ∀ (t : Fin 72) (k : Fin 8), modePhase t k < 6 := by
  decide +kernel

/-- The ensemble realizes the actual real cosine moments, with normalization
    by its 72 equiprobable outcomes. -/
theorem cosineMoments (k l : Fin 8) :
    (∑ t : Fin 72, Real.cos (((modePhase t k : ℝ) - modePhase t l) * (Real.pi/3))) / 72 =
      (if k = l then 1 else if k.val % 2 = l.val % 2 then -(1/8 : ℝ) else 0) := by
  have hcos (t : Fin 72) :
      (twiceCos (modePhase t k + 6 - modePhase t l) : ℝ) =
        2 * Real.cos (((modePhase t k : ℝ) - modePhase t l) * (Real.pi / 3)) := by
    rw [twiceCos_correct, Nat.cast_sub (by have := modePhase_lt t l; omega)]
    push_cast
    congr 1
    rw [show ((modePhase t k : ℝ) + 6 - modePhase t l) * (Real.pi / 3) =
      ((modePhase t k : ℝ) - modePhase t l) * (Real.pi / 3) + 2 * Real.pi by ring,
      Real.cos_add_two_pi]
  have he := congrArg (fun z : Int => (z : ℝ)) (exactMoments k l)
  push_cast at he
  simp only [hcos, ← Finset.mul_sum] at he
  split_ifs at * <;> norm_num at * <;> linarith

end PrimePowerMixing.EightSites
