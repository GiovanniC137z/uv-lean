import UV.AdvanceSpectrumSetwiseDensity
import Mathlib.MeasureTheory.Function.Floor

/-! Patch the finite Radon–Nikodym densities into the common local
spectral density of the completed fixed-plane measure. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace UV.RevisionSpectrum

variable {E : Type*} [Norm E] {diamond : UV.SectorPlane.Plane E}

def spectralWindow (n : ℕ) : Set ℝ := Icc 0 (n : ℝ)

def SetwiseSpectralCompletion.trace (C : SetwiseSpectralCompletion diamond) : Measure ℝ :=
  C.first + C.second

def SetwiseSpectralCompletion.localTrace (C : SetwiseSpectralCompletion diamond) (n : ℕ) :
    Measure ℝ := C.trace.restrict (spectralWindow n)

def SetwiseSpectralCompletion.firstDensity (C : SetwiseSpectralCompletion diamond) (s : ℝ) : ℝ :=
  (C.first.rnDeriv C.trace s).toReal

def SetwiseSpectralCompletion.secondDensity (C : SetwiseSpectralCompletion diamond) (s : ℝ) : ℝ :=
  (C.second.rnDeriv C.trace s).toReal

def SetwiseSpectralCompletion.localCrossDensity (C : SetwiseSpectralCompletion diamond)
    (n : ℕ) : ℝ → ℂ := (C.cross n).rnDeriv (C.localTrace n)

def SetwiseSpectralCompletion.crossDensity (C : SetwiseSpectralCompletion diamond) (s : ℝ) : ℂ :=
  C.localCrossDensity ⌈s⌉₊ s

theorem SetwiseSpectralCompletion.trace_nonnegative (C : SetwiseSpectralCompletion diamond) :
    ∀ᵐ s ∂C.trace, 0 ≤ s :=
  ae_add_measure_iff.2 ⟨C.first_nonnegative, C.second_nonnegative⟩

theorem SetwiseSpectralCompletion.trace_locallyFinite (C : SetwiseSpectralCompletion diamond) :
    IsLocallyFiniteMeasure C.trace := by
  letI := C.first_locallyFinite
  letI := C.second_locallyFinite
  refine ⟨fun x => ?_⟩
  obtain ⟨S, hS, hopenS, hfinS⟩ := C.first.exists_isOpen_measure_lt_top x
  obtain ⟨T, hT, hopenT, hfinT⟩ := C.second.exists_isOpen_measure_lt_top x
  refine ⟨S ∩ T, (hopenS.inter hopenT).mem_nhds ⟨hS,hT⟩, ?_⟩
  rw [SetwiseSpectralCompletion.trace, Measure.add_apply]
  exact ENNReal.add_lt_top.2 ⟨(measure_mono inter_subset_left).trans_lt hfinS,
    (measure_mono inter_subset_right).trans_lt hfinT⟩

theorem SetwiseSpectralCompletion.localTrace_finite
    (C : SetwiseSpectralCompletion diamond) (n : ℕ) : IsFiniteMeasure (C.localTrace n) := by
  letI := C.trace_locallyFinite
  refine ⟨?_⟩
  rw [SetwiseSpectralCompletion.localTrace, Measure.restrict_apply_univ]
  exact isCompact_Icc.measure_lt_top

theorem spectralWindow_mono : Monotone spectralWindow := by
  intro m n hmn s hs
  exact ⟨hs.1,hs.2.trans (by exact_mod_cast hmn)⟩

theorem SetwiseSpectralCompletion.cross_agrees_on_window (C : SetwiseSpectralCompletion diamond)
    {m n : ℕ} (hmn : m ≤ n) {B : Set ℝ} (hB : MeasurableSet B)
    (hsub : B ⊆ spectralWindow m) : C.cross n B = C.cross m B := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hm ih =>
    have hi := congrArg (fun ν : ComplexMeasure ℝ => ν B) (C.cross_compatible n)
    dsimp only at hi
    rw [VectorMeasure.restrict_eq_self _ measurableSet_Icc hB (hsub.trans (spectralWindow_mono hm))] at hi
    exact hi.trans ih

theorem SetwiseSpectralCompletion.localCrossDensity_integrable (C : SetwiseSpectralCompletion diamond)
    (n : ℕ) : Integrable (C.localCrossDensity n) (C.localTrace n) :=
  (C.cross n).integrable_rnDeriv (C.localTrace n)

theorem SetwiseSpectralCompletion.localCrossDensity_integral (C : SetwiseSpectralCompletion diamond)
    (n : ℕ) {B : Set ℝ} (hB : MeasurableSet B) :
    (∫ s in B, C.localCrossDensity n s ∂C.localTrace n) = C.cross n B := by
  letI := C.localTrace_finite n
  have h := finite_setwise_cross_absolutelyContinuous (C.cross n) (C.setwise_positive n)
  have hμ : C.localTrace n = C.first.restrict (spectralWindow n) +
      C.second.restrict (spectralWindow n) := Measure.restrict_add _ _ _
  change C.cross n ≪ᵥ (C.first.restrict (spectralWindow n) +
    C.second.restrict (spectralWindow n)).toENNRealVectorMeasure at h
  rw [← hμ] at h
  rw [← withDensityᵥ_apply (C.localCrossDensity_integrable n) hB]
  exact congrArg (fun ν : ComplexMeasure ℝ => ν B) (finite_complex_withDensity_rnDeriv_eq h)

theorem SetwiseSpectralCompletion.localCrossDensity_compatible
    (C : SetwiseSpectralCompletion diamond) {m n : ℕ} (hmn : m ≤ n) :
    C.localCrossDensity n =ᵐ[C.localTrace m] C.localCrossDensity m := by
  have hsub := spectralWindow_mono hmn
  have hI : Integrable (C.localCrossDensity n) (C.localTrace m) :=
    (C.localCrossDensity_integrable n).mono_measure (Measure.restrict_mono hsub le_rfl)
  refine Integrable.ae_eq_of_forall_setIntegral_eq _ _ hI (C.localCrossDensity_integrable m) ?_
  intro B hB _
  have hC : MeasurableSet (B ∩ spectralWindow m) := hB.inter measurableSet_Icc
  have hμ₁ : (C.localTrace m).restrict B = (C.localTrace n).restrict (B ∩ spectralWindow m) := by
    unfold SetwiseSpectralCompletion.localTrace
    rw [Measure.restrict_restrict hB, Measure.restrict_restrict hC, inter_assoc,
      inter_eq_left.2 hsub]
  have hμ₂ : (C.localTrace m).restrict B = (C.localTrace m).restrict (B ∩ spectralWindow m) := by
    unfold SetwiseSpectralCompletion.localTrace
    rw [Measure.restrict_restrict hB, Measure.restrict_restrict hC, inter_assoc, inter_self]
  calc
    _ = ∫ s in B ∩ spectralWindow m, C.localCrossDensity n s ∂C.localTrace n := by rw [hμ₁]
    _ = C.cross n (B ∩ spectralWindow m) := C.localCrossDensity_integral n hC
    _ = C.cross m (B ∩ spectralWindow m) := C.cross_agrees_on_window hmn hC inter_subset_right
    _ = ∫ s in B ∩ spectralWindow m, C.localCrossDensity m s ∂C.localTrace m :=
      (C.localCrossDensity_integral m hC).symm
    _ = _ := by rw [← hμ₂]

theorem SetwiseSpectralCompletion.localCrossDensity_measurable
    (C : SetwiseSpectralCompletion diamond) (n : ℕ) : Measurable (C.localCrossDensity n) := by
  have hre := SignedMeasure.measurable_rnDeriv (C.cross n).re (C.localTrace n)
  have him := SignedMeasure.measurable_rnDeriv (C.cross n).im (C.localTrace n)
  have he : C.localCrossDensity n = fun s =>
    (((C.cross n).re.rnDeriv (C.localTrace n) s) : ℂ) +
      (((C.cross n).im.rnDeriv (C.localTrace n) s) : ℂ)*Complex.I := by
    funext s
    exact (Complex.re_add_im (C.localCrossDensity n s)).symm
  rw [he]
  exact (Complex.continuous_ofReal.measurable.comp hre).add
    ((Complex.continuous_ofReal.measurable.comp him).mul_const Complex.I)

theorem SetwiseSpectralCompletion.crossDensity_measurable
    (C : SetwiseSpectralCompletion diamond) : Measurable C.crossDensity := by
  intro B hB
  have he : C.crossDensity ⁻¹' B =
      ⋃ n, ((Nat.ceil : ℝ → ℕ) ⁻¹' {n}) ∩ C.localCrossDensity n ⁻¹' B := by
    ext s
    simp only [mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff]
    constructor
    · exact fun h => ⟨⌈s⌉₊,rfl,h⟩
    · rintro ⟨n,rfl,h⟩
      exact h
  rw [he]
  exact MeasurableSet.iUnion (fun n =>
    (Nat.measurable_ceil (measurableSet_singleton n)).inter
      (C.localCrossDensity_measurable n hB))

theorem SetwiseSpectralCompletion.crossDensity_eq_local (C : SetwiseSpectralCompletion diamond)
    (n : ℕ) : C.crossDensity =ᵐ[C.localTrace n] C.localCrossDensity n := by
  have hcompat (m : ℕ) :
      ∀ᵐ s ∂C.trace, s ∈ spectralWindow m → m ≤ n →
        C.localCrossDensity n s = C.localCrossDensity m s := by
    by_cases hm : m ≤ n
    · have hc := C.localCrossDensity_compatible hm
      have hh : ∀ᵐ s ∂C.trace, s ∈ spectralWindow m →
          C.localCrossDensity n s = C.localCrossDensity m s :=
        (ae_restrict_iff' (measurableSet_Icc (a := 0) (b := (m : ℝ)))).1 hc
      exact hh.mono fun s hs ht _ => hs ht
    · exact ae_of_all _ (fun _ _ h => (hm h).elim)
  have hall := ae_all_iff.2 hcompat
  have hh : ∀ᵐ s ∂C.localTrace n, s ∈ spectralWindow n :=
    ae_restrict_mem measurableSet_Icc
  filter_upwards [ae_restrict_of_ae hall, hh] with s hs hsn
  exact (hs ⌈s⌉₊ ⟨hsn.1, Nat.le_ceil s⟩ (Nat.ceil_le.2 hsn.2)).symm

theorem SetwiseSpectralCompletion.crossDensity_integral_local
    (C : SetwiseSpectralCompletion diamond) (n : ℕ) {B : Set ℝ} (hB : MeasurableSet B) :
    (∫ s in B, C.crossDensity s ∂C.localTrace n) = C.cross n B := by
  rw [integral_congr_ae (ae_restrict_of_ae (C.crossDensity_eq_local n))]
  exact C.localCrossDensity_integral n hB

theorem SetwiseSpectralCompletion.first_ac_trace (C : SetwiseSpectralCompletion diamond) :
    C.first ≪ C.trace := (Measure.le_add_right le_rfl).absolutelyContinuous

theorem SetwiseSpectralCompletion.second_ac_trace (C : SetwiseSpectralCompletion diamond) :
    C.second ≪ C.trace := (Measure.le_add_left le_rfl).absolutelyContinuous

theorem SetwiseSpectralCompletion.firstDensity_integral_local
    (C : SetwiseSpectralCompletion diamond) (n : ℕ) {B : Set ℝ} (hB : MeasurableSet B) :
    (∫ s in B, C.firstDensity s ∂C.localTrace n) =
      (C.first.restrict (spectralWindow n)).real B := by
  letI := C.first_locallyFinite
  letI := C.trace_locallyFinite
  unfold SetwiseSpectralCompletion.localTrace SetwiseSpectralCompletion.firstDensity
  rw [Measure.restrict_restrict hB, measureReal_restrict_apply hB]
  exact Measure.setIntegral_toReal_rnDeriv C.first_ac_trace (B ∩ spectralWindow n)

theorem SetwiseSpectralCompletion.secondDensity_integral_local
    (C : SetwiseSpectralCompletion diamond) (n : ℕ) {B : Set ℝ} (hB : MeasurableSet B) :
    (∫ s in B, C.secondDensity s ∂C.localTrace n) =
      (C.second.restrict (spectralWindow n)).real B := by
  letI := C.second_locallyFinite
  letI := C.trace_locallyFinite
  unfold SetwiseSpectralCompletion.localTrace SetwiseSpectralCompletion.secondDensity
  rw [Measure.restrict_restrict hB, measureReal_restrict_apply hB]
  exact Measure.setIntegral_toReal_rnDeriv C.second_ac_trace (B ∩ spectralWindow n)

theorem SetwiseSpectralCompletion.density_positive
    (C : SetwiseSpectralCompletion diamond) :
    ∀ᵐ s ∂C.trace, 0 ≤ C.firstDensity s ∧ 0 ≤ C.secondDensity s ∧
      ‖C.crossDensity s‖^2 ≤ C.firstDensity s*C.secondDensity s := by
  letI := C.first_locallyFinite
  letI := C.second_locallyFinite
  letI := C.trace_locallyFinite
  have hi₁ (n : ℕ) : Integrable C.firstDensity (C.localTrace n) :=
    Measure.integrableOn_toReal_rnDeriv (μ := C.first) (ν := C.trace)
      (isCompact_Icc.measure_lt_top (μ := C.first)).ne
  have hi₂ (n : ℕ) : Integrable C.secondDensity (C.localTrace n) :=
    Measure.integrableOn_toReal_rnDeriv (μ := C.second) (ν := C.trace)
      (isCompact_Icc.measure_lt_top (μ := C.second)).ne
  have hlocal (n : ℕ) : ∀ᵐ s ∂C.localTrace n,
      0 ≤ C.firstDensity s ∧ 0 ≤ C.secondDensity s ∧
      ‖C.crossDensity s‖^2 ≤ C.firstDensity s*C.secondDensity s := by
    have hic := (C.localCrossDensity_integrable n).congr (C.crossDensity_eq_local n).symm
    refine setwise_density_det_nonnegative (hi₁ n) (hi₂ n) hic
      (ae_of_all _ fun _ => ENNReal.toReal_nonneg) (ae_of_all _ fun _ => ENNReal.toReal_nonneg) ?_
    intro B hB
    rw [C.firstDensity_integral_local n hB, C.secondDensity_integral_local n hB,
      C.crossDensity_integral_local n hB]
    exact C.setwise_positive n B hB
  have hlocal' (n : ℕ) : ∀ᵐ s ∂C.trace, s ∈ spectralWindow n →
      0 ≤ C.firstDensity s ∧ 0 ≤ C.secondDensity s ∧
      ‖C.crossDensity s‖^2 ≤ C.firstDensity s*C.secondDensity s :=
    (ae_restrict_iff' measurableSet_Icc).1 (hlocal n)
  filter_upwards [ae_all_iff.2 hlocal', C.trace_nonnegative] with s hs hs₀
  exact hs ⌈s⌉₊ ⟨hs₀, Nat.le_ceil s⟩

theorem SetwiseSpectralCompletion.stieltjes_budget
    (C : SetwiseSpectralCompletion diamond) {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hi₁ : Integrable (stieltjesWeight y) C.first)
    (hi₂ : Integrable (stieltjesWeight y) C.second) :
    Integrable (fun s => stieltjesWeight x s * ‖C.crossDensity s‖) C.trace ∧
    (stieltjes C.trace id (fun s => ‖C.crossDensity s‖) x)^2 ≤
      diagonalStieltjes C.first x * diagonalStieltjes C.second x ∧
    2 * stieltjes C.trace id (fun s => ‖C.crossDensity s‖) x ≤
      diagonalStieltjes C.first x + diagonalStieltjes C.second x := by
  letI := C.first_locallyFinite
  letI := C.second_locallyFinite
  letI := C.trace_locallyFinite
  have ha₀ := diagonal_stieltjes_weighted_integrable C.first_nonnegative hx hy hi₁
  have hb₀ := diagonal_stieltjes_weighted_integrable C.second_nonnegative hx hy hi₂
  have ha : Integrable (fun s => stieltjesWeight x s * C.firstDensity s) C.trace := by
    simpa only [SetwiseSpectralCompletion.firstDensity, smul_eq_mul, mul_comm] using
      (integrable_rnDeriv_smul_iff (f := stieltjesWeight x) C.first_ac_trace).2 ha₀
  have hb : Integrable (fun s => stieltjesWeight x s * C.secondDensity s) C.trace := by
    simpa only [SetwiseSpectralCompletion.secondDensity, smul_eq_mul, mul_comm] using
      (integrable_rnDeriv_smul_iff (f := stieltjesWeight x) C.second_ac_trace).2 hb₀
  have ea : stieltjes C.trace id C.firstDensity x = diagonalStieltjes C.first x := by
    simpa only [stieltjes, id_eq, diagonalStieltjes, smul_eq_mul, mul_comm,
      SetwiseSpectralCompletion.firstDensity] using
      (integral_rnDeriv_smul (f := stieltjesWeight x) C.first_ac_trace)
  have eb : stieltjes C.trace id C.secondDensity x = diagonalStieltjes C.second x := by
    simpa only [stieltjes, id_eq, diagonalStieltjes, smul_eq_mul, mul_comm,
      SetwiseSpectralCompletion.secondDensity] using
      (integral_rnDeriv_smul (f := stieltjesWeight x) C.second_ac_trace)
  rw [← ea, ← eb]
  exact positive_stieltjes_budget (s := id) hx measurable_id C.trace_nonnegative ha hb
    C.crossDensity_measurable.aestronglyMeasurable C.density_positive

end UV.RevisionSpectrum
