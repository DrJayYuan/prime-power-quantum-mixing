import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace PrimePowerMixing

open MeasureTheory

/-- The barycenter of a continuous, integrable moment map under a
    full-support probability measure is interior in full-dimensional
    coordinates. The affine-span hypothesis corresponds to choosing
    coordinates in the affine hull of the moment vectors. -/
theorem barycenter_interior {T E : Type} [TopologicalSpace T] [MeasurableSpace T]
    [BorelSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (μ : Measure T) [IsProbabilityMeasure μ] [Measure.IsOpenPosMeasure μ]
    (f : T → E) (hf : Continuous f) (hi : Integrable f μ)
    (hspan : affineSpan ℝ (Set.range f) = ⊤) :
    (∫ t, f t ∂μ) ∈ interior (convexHull ℝ (Set.range f)) := by
  let K := convexHull ℝ (Set.range f)
  let x := ∫ t, f t ∂μ
  change x ∈ interior K
  have hK : Convex ℝ K := convex_convexHull ..
  have hne : (interior K).Nonempty := interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr hspan
  by_contra hx
  obtain ⟨L, hL⟩ := geometric_hahn_banach_open_point hK.interior isOpen_interior hx
  have hle (t : T) : L (f t) ≤ L x := by
    have ht : f t ∈ closure (interior K) := by
      rw [hK.closure_interior_eq_closure_of_nonempty_interior hne]
      exact subset_closure (subset_convexHull ℝ (Set.range f) (Set.mem_range_self t))
    exact closure_minimal (fun y hy => (hL y hy).le)
      (isClosed_Iic.preimage L.continuous) ht
  have hlt : ∃ t, L (f t) < L x := by
    by_contra! hn
    obtain ⟨y, hy⟩ := hne
    have hsub : Set.range f ⊆ L.toLinearMap ⁻¹' Set.Ici (L x) := by
      rintro _ ⟨t, rfl⟩
      exact hn t
    exact (hL y hy).not_ge
      (convexHull_min hsub ((convex_Ici _).linear_preimage L.toLinearMap) (interior_subset hy))
  obtain ⟨t, ht⟩ := hlt
  have hcont : Continuous fun t => L x - L (f t) :=
    continuous_const.sub (L.continuous.comp hf)
  have hLi : Integrable (fun t => L (f t)) μ := L.integrable_comp hi
  have hint : Integrable (fun t => L x - L (f t)) μ := (integrable_const _).sub hLi
  have hpos := integral_pos_of_integrable_nonneg_nonzero hcont hint
    (fun t => sub_nonneg.mpr (hle t)) (sub_pos.mpr ht).ne'
  rw [integral_sub (integrable_const _) hLi, integral_const,
    ContinuousLinearMap.integral_comp_comm L hi] at hpos
  simp [x] at hpos

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

/-- A full-support distribution on limiting phases can be replaced by an
    exact finite law over integer orbit times, preserving the entire moment
    vector. Coordinates are taken in the affine hull of the phase image. -/
theorem exactSchedule_of_fullSupport {T E : Type} [TopologicalSpace T] [MeasurableSpace T]
    [BorelSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (μ : Measure T) [IsProbabilityMeasure μ] [Measure.IsOpenPosMeasure μ]
    (f : T → E) (hf : Continuous f) (hi : Integrable f μ)
    (hspan : affineSpan ℝ (Set.range f) = ⊤) (orbit : ℕ → E)
    (hdense : Set.range f ⊆ closure (Set.range orbit)) :
    ∃ (k : ℕ) (time : Fin k → ℕ) (weight : Fin k → ℝ),
      k ≤ Module.finrank ℝ E + 1 ∧
      (∀ i, 0 < weight i) ∧ ∑ i, weight i = 1 ∧
      ∑ i, weight i • orbit (time i) = ∫ t, f t ∂μ := by
  have hspan_orbit : affineSpan ℝ (convexHull ℝ (Set.range orbit)) = ⊤ := by
    rw [affineSpan_convexHull]
    apply top_unique
    rw [← hspan]
    exact affineSpan_le.mpr
      (hdense.trans (closure_minimal (subset_affineSpan _ _)
        (affineSpan ℝ (Set.range orbit)).closed_of_finiteDimensional))
  exact finiteSchedule orbit (Set.range f) (∫ t, f t ∂μ) hspan_orbit hdense
    (barycenter_interior μ f hf hi hspan)

end PrimePowerMixing
