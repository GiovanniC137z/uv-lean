import UV.ContinueRelativeChargeBreit
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-! The transverse carrier cosine mark of the relative chord.
The calculation uses the real Fourier carrier coordinate. -/

noncomputable section

open Filter
open scoped Topology RealInnerProductSpace Matrix.Norms.Elementwise

namespace UV.SectorPlane

def spectralMarkSpatialUnit (j : Fin 3) : UnitVector Spatial :=
  ⟨EuclideanSpace.single j 1, by simp⟩

theorem Plane.spectral_mark_transverse {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (diamond : Plane E) (j : Fin 3) (p : ℝ) :
    let a := WithLp.toLp 2 ((0 : E), (spectralMarkSpatialUnit j : Spatial))
    let q := WithLp.toLp 2 (p • (diamond.poleUnit : E), (0 : Spatial))
    ‖a‖ = 1 ∧ ⟪a, q⟫ = 0 ∧ ‖q‖ = |p| := by
  dsimp
  constructor
  · rw [WithLp.prod_norm_eq_of_L2]
    simp [(spectralMarkSpatialUnit j).property]
  · constructor
    · simp
    · rw [WithLp.prod_norm_eq_of_L2]
      simp [norm_smul, diamond.poleUnit.property, Real.norm_eq_abs, Real.sqrt_sq_eq_abs]

def spectralMarkGamma (j : Fin 3) : DiracMatrix := euclideanGamma j.succ

theorem spectral_mark_gamma_sq (j : Fin 3) : spectralMarkGamma j * spectralMarkGamma j = 1 := by
  have h := euclideanGamma_clifford j.succ j.succ
  rw [if_pos rfl] at h
  apply (smul_right_injective DiracMatrix (by norm_num : (2 : ℂ) ≠ 0))
  simpa [spectralMarkGamma, two_smul] using h

def spectralMarkSpatialCurve (ω : ℝ) (j : Fin 3) (z : ℂ) : ChordMomentum :=
  ((ω : ℂ), fun i => if i = j then z else 0)

def spectralMarkSlash (k : ChordMomentum) : DiracMatrix :=
  k.1 • chordGammaParallel + ∑ j : Fin 3, k.2 j • spectralMarkGamma j

theorem spectral_mark_square (ω : ℝ) (j : Fin 3) (z : ℂ) :
    chordSquare (spectralMarkSpatialCurve ω j z) = (ω : ℂ)^2 + z^2 := by
  simp [chordSquare, spectralMarkSpatialCurve, apply_ite (fun w : ℂ => w ^ 2)]

theorem spectral_mark_slash_symbol (σ ω : ℝ) (j : Fin 3) (z : ℂ) :
    spectralMarkSlash (chordSymbol σ (spectralMarkSpatialCurve ω j z)) =
      Complex.exp (-(σ : ℂ)^2 * ((ω : ℂ)^2 + z^2)) •
        ((ω : ℂ) • chordGammaParallel + z • spectralMarkGamma j) := by
  unfold spectralMarkSlash chordSymbol chordGaussian
  rw [spectral_mark_square, smul_add]
  simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, spectralMarkSpatialCurve,
    smul_eq_mul, mul_ite, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, smul_smul]

/-- Spatial derivative of the exact Gaussian vertex at real axial
frequency and vanishing spatial momentum. -/
theorem spectral_mark_symbol_hasDerivAt (σ ω : ℝ) (j : Fin 3) :
    HasDerivAt (fun z => spectralMarkSlash (chordSymbol σ (spectralMarkSpatialCurve ω j z)))
      ((Real.exp (-σ^2 * ω^2) : ℂ) • spectralMarkGamma j) 0 := by
  simp_rw [spectral_mark_slash_symbol]
  have hq := (((hasDerivAt_id (0 : ℂ)).pow 2).const_add ((ω : ℂ)^2)).const_mul (-(σ : ℂ)^2)
  have hg := hq.cexp
  have hv := ((hasDerivAt_id (0 : ℂ)).smul_const (spectralMarkGamma j)).const_add
    ((ω : ℂ) • chordGammaParallel)
  simpa [Pi.pow_apply, ← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
    ← Complex.ofReal_exp] using hg.fun_smul hv

def spectralMarkWeight (σ ω p : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, Real.exp (-σ^2 * (ω + u*p)^2)

theorem spectral_mark_weight_pos (σ ω p : ℝ) : 0 < spectralMarkWeight σ ω p := by
  apply intervalIntegral.integral_pos zero_lt_one
  · exact Continuous.continuousOn (by fun_prop)
  · intro u _
    exact (Real.exp_pos _).le
  · exact ⟨0, ⟨le_rfl, zero_le_one⟩, Real.exp_pos _⟩

theorem spectral_mark_integrated_derivative (σ ω p : ℝ) (j : Fin 3) :
    (∫ u in (0 : ℝ)..1, deriv (fun z =>
      spectralMarkSlash (chordSymbol σ (spectralMarkSpatialCurve (ω + u*p) j z))) 0) =
      (spectralMarkWeight σ ω p : ℂ) • spectralMarkGamma j := by
  simp_rw [(spectral_mark_symbol_hasDerivAt σ _ j).deriv]
  rw [intervalIntegral.integral_smul_const, intervalIntegral.integral_ofReal, spectralMarkWeight]

theorem spectral_real_cosine_split (θ : ℝ) :
    (Real.cos θ : ℂ) = (Complex.exp ((θ : ℂ) * Complex.I) +
      Complex.exp (-((θ : ℂ) * Complex.I))) / 2 := by
  rw [Complex.ofReal_cos, Complex.cos, neg_mul]

/-- The positive-frequency branch of the real cosine contributes the
factor 1/2. The bracket is the straight-chord parameter integral. -/
def spectralCosineMark (e r σ ω p : ℝ) (j : Fin 3) : DiracMatrix :=
  (Complex.I * ((e * Real.exp (-r * |p|) * spectralMarkWeight σ ω p / 2 : ℝ) : ℂ)) •
    spectralMarkGamma j

theorem spectral_cosine_mark_eq_integrated (e r σ ω p : ℝ) (j : Fin 3) :
    spectralCosineMark e r σ ω p j =
      ((Complex.I * ((e * Real.exp (-r * |p|) : ℝ) : ℂ)) / 2) •
        (∫ u in (0 : ℝ)..1, deriv (fun z =>
          spectralMarkSlash (chordSymbol σ (spectralMarkSpatialCurve (ω + u*p) j z))) 0) := by
  rw [spectral_mark_integrated_derivative, spectralCosineMark, smul_smul]
  congr 1
  push_cast
  ring

theorem spectral_cosine_sidebands_distinct (ω p : ℝ) (hp : p ≠ 0) : ω+p ≠ ω-p := by
  intro h
  apply hp
  linarith

private theorem spectral_cosine_coefficient_ne_zero (e r σ ω p : ℝ) (he : e ≠ 0) :
    Complex.I * ((e * Real.exp (-r * |p|) * spectralMarkWeight σ ω p / 2 : ℝ) : ℂ) ≠ 0 := by
  have hsc : (e * Real.exp (-r * |p|) * spectralMarkWeight σ ω p / 2 : ℝ) ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero he (Real.exp_pos _).ne')
      (spectral_mark_weight_pos σ ω p).ne') (by norm_num)
  exact mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hsc)

theorem spectral_cosine_mark_ne_zero (e r σ ω p : ℝ) (he : e ≠ 0) (j : Fin 3) :
    spectralCosineMark e r σ ω p j ≠ 0 := by
  have hγ : spectralMarkGamma j ≠ 0 := by
    intro h
    have h' := spectral_mark_gamma_sq j
    rw [h, zero_mul] at h'
    exact zero_ne_one h'
  exact smul_ne_zero (spectral_cosine_coefficient_ne_zero e r σ ω p he) hγ

open scoped Matrix in
/-- The nonzero derivative survives application to every nonzero
incoming spinor through the exact free multiplier. -/
theorem spectral_cosine_mark_free_mulVec_ne_zero (e r σ ω p : ℝ) (he : e ≠ 0)
    {m : ℝ} (hm : 0 < m) (j : Fin 3) (v : Fin 4 → ℂ) (hv : v ≠ 0) :
    (spectralCosineMark e r σ ω p j *
      freeDiracPropagator m (EuclideanSpace.single 0 ω)) *ᵥ v ≠ 0 := by
  let k : DiracMomentum := EuclideanSpace.single 0 ω
  let R := freeDiracPropagator m k
  have hR : R *ᵥ v ≠ 0 := by
    intro h
    have hc := congrArg (fun z => freeDiracSymbol m k *ᵥ z) h
    change freeDiracSymbol m k *ᵥ (freeDiracPropagator m k *ᵥ v) =
      freeDiracSymbol m k *ᵥ 0 at hc
    rw [Matrix.mulVec_zero, Matrix.mulVec_mulVec, freeDiracSymbol_mul_propagator hm,
      Matrix.one_mulVec] at hc
    exact hv hc
  have hg : spectralMarkGamma j *ᵥ (R *ᵥ v) ≠ 0 := by
    intro h
    have hc := congrArg (fun z => spectralMarkGamma j *ᵥ z) h
    dsimp only at hc
    rw [Matrix.mulVec_zero, Matrix.mulVec_mulVec, spectral_mark_gamma_sq,
      Matrix.one_mulVec] at hc
    exact hR hc
  change (spectralCosineMark e r σ ω p j * R) *ᵥ v ≠ 0
  rw [← Matrix.mulVec_mulVec, spectralCosineMark, Matrix.smul_mulVec]
  exact smul_ne_zero (spectral_cosine_coefficient_ne_zero e r σ ω p he) hg

/-- A nonzero first variation of the Fourier component rules out
equality throughout a punctured neighborhood in the real amplitude. -/
theorem spectral_cosine_mark_local_change (e r σ ω p : ℝ) (he : e ≠ 0) (j : Fin 3)
    (Y : ℝ → DiracMatrix) (hY : HasDerivAt Y (spectralCosineMark e r σ ω p j) 0) :
    ∀ᶠ t in 𝓝[≠] 0, Y t ≠ Y 0 :=
  hY.eventually_ne (spectral_cosine_mark_ne_zero e r σ ω p he j)

open scoped Matrix in
theorem spectral_cosine_spin_local_change (e r σ ω p : ℝ) (he : e ≠ 0)
    {m : ℝ} (hm : 0 < m) (j : Fin 3) (v : Fin 4 → ℂ) (hv : v ≠ 0)
    (F : ℝ → Fin 4 → ℂ) (hF : HasDerivAt F
      ((spectralCosineMark e r σ ω p j * freeDiracPropagator m (EuclideanSpace.single 0 ω)) *ᵥ v) 0) :
    ∀ᶠ t in 𝓝[≠] 0, F t ≠ F 0 :=
  hF.eventually_ne (spectral_cosine_mark_free_mulVec_ne_zero e r σ ω p he hm j v hv)

end UV.SectorPlane
