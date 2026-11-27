import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

namespace PrimePowerMixing

/-- In finite-dimensional affine-hull coordinates, an interior point of the
    convex hull of limiting moments is realized by finitely many actual times.
    The hypotheses are the full-dimensionality, phase-approximation, and
    interior conditions in those coordinates. -/
theorem finiteSchedule {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (orbit : ℕ → E) (limits : Set E) (x : E)
    (hdim : affineSpan ℝ (convexHull ℝ (Set.range orbit)) = ⊤)
    (hdense : limits ⊆ closure (Set.range orbit))
    (hx : x ∈ interior (convexHull ℝ limits)) :
    ∃ (k : ℕ) (time : Fin k → ℕ) (weight : Fin k → ℝ),
      k ≤ Module.finrank ℝ E + 1 ∧
      (∀ i, 0 < weight i) ∧ ∑ i, weight i = 1 ∧
      ∑ i, weight i • orbit (time i) = x := by
  let C := convexHull ℝ (Set.range orbit)
  have hC : Convex ℝ C := convex_convexHull ..
  have hne : (interior C).Nonempty := hC.interior_nonempty_iff_affineSpan_eq_top.mpr hdim
  have hc : convexHull ℝ limits ⊆ closure C :=
    convexHull_min (hdense.trans (closure_mono (subset_convexHull ..))) hC.closure
  have hx' : x ∈ C := by
    have hi := interior_mono hc hx
    rw [hC.interior_closure_eq_interior_of_nonempty_interior hne] at hi
    exact interior_subset hi
  obtain ⟨ι, _, z, w, hz, ha, hw, hsum, hweighted⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx'
  have htime (i : ι) : ∃ t, orbit t = z i := hz (Set.mem_range_self i)
  choose t ht using htime
  let e := Fintype.equivFin ι
  have hcard := ha.card_le_finrank_succ.trans
    (Nat.add_le_add_right (Submodule.finrank_le (vectorSpan ℝ (Set.range z))) 1)
  refine ⟨Fintype.card ι, t ∘ e.symm, w ∘ e.symm, hcard,
    fun i => hw (e.symm i), ?_, ?_⟩
  · exact (e.symm.sum_comp w).trans hsum
  · simpa only [Function.comp_apply, ht] using
      (e.symm.sum_comp (fun i => w i • z i)).trans hweighted

end PrimePowerMixing
