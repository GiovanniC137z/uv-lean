import UV.AdvanceSpectrumVariation

/-! Pure-pole restriction for the actual bounded cross spectral
measures, and for their ordinary Stieltjes transform. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace UV.RevisionSpectrum

variable {E : Type*} [Norm E] {diamond : UV.SectorPlane.Plane E}

/-- Stieltjes transform of the cross measure using its derived common
density. Its local integrals recover every bounded restriction. -/
def SetwiseSpectralCompletion.crossStieltjes (C : SetwiseSpectralCompletion diamond)
    (x : ℝ) : ℂ :=
  ∫ s, (stieltjesWeight x s : ℂ) * C.crossDensity s ∂C.trace

theorem SetwiseSpectralCompletion.crossStieltjes_integrable
    (C : SetwiseSpectralCompletion diamond) {x y : ℝ} (hx : 0<x) (hy : 0<y)
    (hi₁ : Integrable (stieltjesWeight y) C.first)
    (hi₂ : Integrable (stieltjesWeight y) C.second) :
    Integrable (fun s => (stieltjesWeight x s : ℂ) * C.crossDensity s) C.trace := by
  have hi := (C.stieltjes_budget hx hy hi₁ hi₂).1
  have hmeas : Measurable (fun s => (stieltjesWeight x s : ℂ) * C.crossDensity s) := by
    unfold stieltjesWeight
    exact (Complex.continuous_ofReal.measurable.comp
      ((measurable_const.add measurable_id).inv)).mul C.crossDensity_measurable
  have heq : (fun s => stieltjesWeight x s * ‖C.crossDensity s‖) =ᵐ[C.trace]
      fun s => ‖(stieltjesWeight x s : ℂ) * C.crossDensity s‖ :=
    C.trace_nonnegative.mono fun s hs => by
      dsimp only
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (stieltjesWeight_pos hx hs).le]
  exact (integrable_norm_iff hmeas.aestronglyMeasurable).1 (hi.congr heq)

/-- A pure pole in the first diagonal eliminates every cross restriction
off that pole, directly at the setwise measure level. -/
theorem SetwiseSpectralCompletion.cross_restrict_at_pure_pole
    (C : SetwiseSpectralCompletion diamond) {m Z : ℝ}
    (hpole : C.first = ENNReal.ofReal Z • Measure.dirac m) (n : ℕ) :
    (C.cross n).restrict ({m} : Set ℝ) = C.cross n := by
  ext1 B hB
  classical
  have hs : MeasurableSet (B \ ({m} : Set ℝ)) := hB.diff (measurableSet_singleton m)
  have hzero : (C.first.restrict (spectralWindow n)).real (B \ ({m} : Set ℝ)) = 0 := by
    rw [measureReal_restrict_apply hs, hpole, measureReal_def, Measure.smul_apply]
    have hc : MeasurableSet ((B \ {m}) ∩ spectralWindow n) := hs.inter measurableSet_Icc
    rw [Measure.dirac_apply' _ hc]
    simp
  have hz := C.setwise_positive n (B \ ({m} : Set ℝ)) hs
  change ‖C.cross n (B \ {m})‖^2 ≤ (C.first.restrict (spectralWindow n)).real (B \ {m}) *
    (C.second.restrict (spectralWindow n)).real (B \ {m}) at hz
  rw [hzero, zero_mul] at hz
  have hz' : C.cross n (B \ {m}) = 0 := norm_eq_zero.mp
    (by nlinarith [norm_nonneg (C.cross n (B \ {m}))])
  have hu : Disjoint (B \ ({m} : Set ℝ)) (B ∩ {m}) :=
    disjoint_sdiff_right.symm.mono_right inter_subset_right
  have heq := (C.cross n).of_union hu hs (hB.inter (measurableSet_singleton m))
  have hUnion : B \ ({m} : Set ℝ) ∪ (B ∩ {m}) = B := by
    ext s
    by_cases hm : s = m <;> simp [hm]
  rw [hUnion, hz', zero_add] at heq
  rw [VectorMeasure.restrict_apply _ (measurableSet_singleton m) hB, ← heq]

theorem SetwiseSpectralCompletion.pure_pole_cross_stieltjes
    (C : SetwiseSpectralCompletion diamond) {m Z y : ℝ} (hZ : 0 < Z)
    (hpole : C.first = ENNReal.ofReal Z • Measure.dirac m)
    (hy : 0 < y) (hi₁ : Integrable (stieltjesWeight y) C.first) :
    ∃ c : ℂ, ∀ x : ℝ, C.crossStieltjes x = c / (↑x + ↑m) := by
  classical
  letI := C.first_locallyFinite
  letI := C.second_locallyFinite
  letI := C.trace_locallyFinite
  have hInt : Integrable (fun s => stieltjesWeight y s*C.firstDensity s) C.trace := by
    simpa only [SetwiseSpectralCompletion.firstDensity, mul_comm, smul_eq_mul] using
      (integrable_rnDeriv_smul_iff (f := stieltjesWeight y) C.first_ac_trace).2 hi₁
  apply pure_pole_cross (μ := C.trace) (s := id) (a := C.firstDensity) (Z := Z)
    (b := C.secondDensity) (c := C.crossDensity) hy measurable_id C.trace_nonnegative
    (C.density_positive.mono fun _ h => h.1)
    (C.density_positive.mono fun _ h => h.2.2) hInt
  intro B hB
  simp only [preimage_id_eq, id_eq]
  have he : (∫ s in B, stieltjesWeight y s*C.firstDensity s ∂C.trace) =
      ∫ s in B, stieltjesWeight y s ∂C.first := by
    simpa only [SetwiseSpectralCompletion.firstDensity, id_eq, smul_eq_mul, mul_comm] using
      (setIntegral_rnDeriv_smul (f := stieltjesWeight y) C.first_ac_trace hB)
  rw [he, hpole, Measure.restrict_smul, integral_smul_measure, setIntegral_dirac,
    ENNReal.toReal_ofReal hZ.le]
  by_cases hm : m ∈ B <;> simp [hm, smul_eq_mul]

end UV.RevisionSpectrum
