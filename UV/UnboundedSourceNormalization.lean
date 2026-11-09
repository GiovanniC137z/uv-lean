import UV.UnboundedSourceCore
import UV.UnboundedSourceGraphCore

/-! Exact free-source identities on the dense common spectral core of
genuinely unbounded L2 multipliers. The normalizer is self-adjoint on its
full maximal domain, and every displayed core product is constructed. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace UV

inductive SourceFactor
  | kinetic | damping | covariance | damped | half | normalizer

def sourceFactorFunction : SourceFactor → (ℝ × ℝ → ℝ)
  | .kinetic => fun p => p.2
  | .damping => fun p => p.1
  | .covariance => fun p => p.2⁻¹
  | .damped => fun p => p.1/p.2
  | .half => fun p => Real.sqrt p.1
  | .normalizer => fun p => (Real.sqrt p.1)⁻¹

theorem sourceFactorFunction_measurable (j : SourceFactor) : Measurable (sourceFactorFunction j) := by
  cases j <;> unfold sourceFactorFunction <;> fun_prop

theorem sourceFactorFunction_continuousOn (j : SourceFactor) :
    ContinuousOn (sourceFactorFunction j) (Ioi 0 ×ˢ Ioi 0) := by
  have hk : ContinuousOn (fun p : ℝ × ℝ => p.2⁻¹) (Ioi 0 ×ˢ Ioi 0) :=
    continuous_snd.continuousOn.inv₀ (fun _ hp => ne_of_gt hp.2)
  have hs : ContinuousOn (fun p : ℝ × ℝ => Real.sqrt p.1) (Ioi 0 ×ˢ Ioi 0) :=
    Real.continuous_sqrt.comp_continuousOn continuous_fst.continuousOn
  cases j
  · exact continuous_snd.continuousOn
  · exact continuous_fst.continuousOn
  · exact hk
  · simpa only [sourceFactorFunction, div_eq_mul_inv] using continuous_fst.continuousOn.mul hk
  · exact hs
  · exact hs.inv₀ (fun _ hp => ne_of_gt (Real.sqrt_pos.mpr hp.1))

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
  {F K : X → ℝ} (hF : Measurable F) (hK : Measurable K)

def sourceFactorSymbol (j : SourceFactor) (x : X) : ℝ := sourceFactorFunction j (F x,K x)

include hF hK in
theorem sourceFactorSymbol_measurable (j : SourceFactor) :
    Measurable (sourceFactorSymbol (F := F) (K := K) j) :=
  (sourceFactorFunction_measurable j).comp (hF.prodMk hK)

include hF hK in
theorem sourceFactorSymbol_admissible (j : SourceFactor) :
    sourceCoreAdmissible F K (fun x => (sourceFactorSymbol (F := F) (K := K) j x : ℂ)) :=
  sourceCoreAdmissible_of_real_continuousOn hF hK
    (sourceFactorFunction_measurable j) (sourceFactorFunction_continuousOn j)

def sourceCoreFactor (j : SourceFactor) : sourceJointCore μ F K →ₗ[ℂ] sourceJointCore μ F K :=
  sourceCoreMul μ (sourceFactorSymbol_admissible hF hK j)

theorem sourceCoreFactor_coe (j : SourceFactor) (f : sourceJointCore μ F K) :
    ((sourceCoreFactor μ hF hK j f : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ]
      fun x => (sourceFactorSymbol (F := F) (K := K) j x : ℂ)*f.val x :=
  sourceCoreMul_coe μ (sourceFactorSymbol_admissible hF hK j) f

/-- The Hermitian symmetry used at a smeared source endpoint is derived
from the actual maximal multiplier; it is not supplied as covariance data. -/
theorem sourceCoreFactor_inner_symm (j : SourceFactor) (f g : sourceJointCore μ F K) :
    inner ℂ (sourceCoreFactor μ hF hK j f : Lp ℂ 2 μ) (g : Lp ℂ 2 μ) =
      inner ℂ (f : Lp ℂ 2 μ) (sourceCoreFactor μ hF hK j g : Lp ℂ 2 μ) :=
  sourceL2Multiplier_real_symmetric μ (sourceFactorSymbol (F := F) (K := K) j)
    ⟨f.val,sourceJointCore_mem_multiplier μ (sourceFactorSymbol_admissible hF hK j) f.property⟩
    ⟨g.val,sourceJointCore_mem_multiplier μ (sourceFactorSymbol_admissible hF hK j) g.property⟩

include hF hK in
/-- The stated common reducing union is an actual graph core for every
kinetic, covariance and endpoint operator used by the source proposition. -/
theorem sourceFactor_common_graphCore (hposF : ∀ᵐ x ∂μ, 0 < F x)
    (hposK : ∀ᵐ x ∂μ, 0 < K x) (j : SourceFactor) :
    LinearPMap.HasCore
      (sourceL2Multiplier μ (fun x => (sourceFactorSymbol (F := F) (K := K) j x : ℂ)))
      (sourceJointCore μ F K) :=
  sourceJointCore_hasCore μ hF hK hposF hposK
    (sourceFactorSymbol_measurable hF hK j) (sourceFactorSymbol_admissible hF hK j)

include hF in
/-- The inverse square-root normalizer is self-adjoint on its full spectral
domain even when F tends to zero and the normalizer is unbounded. -/
theorem source_unbounded_normalizer_selfAdjoint :
    IsSelfAdjoint (sourceL2Multiplier μ
      (fun x => ((Real.sqrt (F x))⁻¹ : ℂ))) := by
  simpa only [Complex.ofReal_inv] using
    sourceL2Multiplier_real_selfAdjoint μ (fun x => (Real.sqrt (F x))⁻¹) hF.sqrt.inv

/-- Exact undamped source covariance for the actual common-core operators. -/
theorem source_unbounded_normalized_covariance (hposF : ∀ᵐ x ∂μ, 0 < F x)
    (f : sourceJointCore μ F K) :
    sourceCoreFactor μ hF hK .normalizer
      (sourceCoreFactor μ hF hK .damped (sourceCoreFactor μ hF hK .normalizer f)) =
      sourceCoreFactor μ hF hK .covariance f := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [sourceCoreFactor_coe μ hF hK .normalizer
      (sourceCoreFactor μ hF hK .damped (sourceCoreFactor μ hF hK .normalizer f)),
    sourceCoreFactor_coe μ hF hK .damped (sourceCoreFactor μ hF hK .normalizer f),
    sourceCoreFactor_coe μ hF hK .normalizer f,
    sourceCoreFactor_coe μ hF hK .covariance f, hposF] with x ht hd hi hc hx
  rw [ht,hc,hd,hi]
  have he : (((Real.sqrt (F x))⁻¹ : ℂ)*(F x/K x : ℝ)*
      ((Real.sqrt (F x))⁻¹ : ℂ)) = ((K x)⁻¹ : ℂ) := by
    exact_mod_cast (free_source_spectral_factors hx (K x)).1
  simp only [sourceFactorSymbol, sourceFactorFunction, Complex.ofReal_inv]
  change ((Real.sqrt (F x))⁻¹ : ℂ)*((F x/K x : ℝ)*
    (((Real.sqrt (F x))⁻¹ : ℂ)*f.val x)) = ((K x)⁻¹ : ℂ)*f.val x
  calc
    _ = (((Real.sqrt (F x))⁻¹ : ℂ)*(F x/K x : ℝ)*
      ((Real.sqrt (F x))⁻¹ : ℂ))*f.val x := by ring
    _ = _ := by rw [he]

/-- The actual mixed contraction retains the half-factor on the common core. -/
theorem source_unbounded_mixed_covariance (hposF : ∀ᵐ x ∂μ, 0 < F x)
    (f : sourceJointCore μ F K) :
    sourceCoreFactor μ hF hK .normalizer (sourceCoreFactor μ hF hK .damped f) =
      sourceCoreFactor μ hF hK .half (sourceCoreFactor μ hF hK .covariance f) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [sourceCoreFactor_coe μ hF hK .normalizer (sourceCoreFactor μ hF hK .damped f),
    sourceCoreFactor_coe μ hF hK .damped f,
    sourceCoreFactor_coe μ hF hK .half (sourceCoreFactor μ hF hK .covariance f),
    sourceCoreFactor_coe μ hF hK .covariance f, hposF] with x ht hd hh hc hx
  rw [ht,hh,hd,hc]
  have he : (((Real.sqrt (F x))⁻¹ : ℂ)*(F x/K x : ℝ)) =
      (Real.sqrt (F x) : ℂ)*((K x)⁻¹ : ℂ) := by
    have h := (free_source_spectral_factors hx (K x)).2.1
    simp only [div_eq_mul_inv] at h
    exact_mod_cast h
  simp only [sourceFactorSymbol, sourceFactorFunction, Complex.ofReal_inv]
  change ((Real.sqrt (F x))⁻¹ : ℂ)*((F x/K x : ℝ)*f.val x) =
    (Real.sqrt (F x) : ℂ)*(((K x)⁻¹ : ℂ)*f.val x)
  simpa only [mul_assoc] using congrArg (fun z : ℂ => z*f.val x) he

/-- Ordinary amputation of the constructed mixed contraction leaves F^1/2. -/
theorem source_unbounded_mixed_amputation (hposF : ∀ᵐ x ∂μ, 0 < F x)
    (hposK : ∀ᵐ x ∂μ, 0 < K x) (f : sourceJointCore μ F K) :
    sourceCoreFactor μ hF hK .normalizer
      (sourceCoreFactor μ hF hK .damped (sourceCoreFactor μ hF hK .kinetic f)) =
      sourceCoreFactor μ hF hK .half f := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [sourceCoreFactor_coe μ hF hK .normalizer
      (sourceCoreFactor μ hF hK .damped (sourceCoreFactor μ hF hK .kinetic f)),
    sourceCoreFactor_coe μ hF hK .damped (sourceCoreFactor μ hF hK .kinetic f),
    sourceCoreFactor_coe μ hF hK .kinetic f,
    sourceCoreFactor_coe μ hF hK .half f, hposF,hposK] with x ht hd hk hh hx hy
  rw [ht,hh,hd,hk]
  have he : (((Real.sqrt (F x))⁻¹ : ℂ)*(F x/K x : ℝ)*(K x : ℂ)) =
      (Real.sqrt (F x) : ℂ) := by
    exact_mod_cast mixed_source_amputation hx hy.ne'
  simp only [sourceFactorSymbol, sourceFactorFunction, Complex.ofReal_inv]
  change ((Real.sqrt (F x))⁻¹ : ℂ)*((F x/K x : ℝ)*((K x : ℂ)*f.val x)) =
    (Real.sqrt (F x) : ℂ)*f.val x
  simpa only [mul_assoc] using congrArg (fun z : ℂ => z*f.val x) he

/-- Actual Hermitian smeared-field covariance equality on the common core.
All vectors and contractions are L2 elements by construction. -/
theorem source_unbounded_smeared_covariance (hposF : ∀ᵐ x ∂μ, 0 < F x)
    (f g : sourceJointCore μ F K) :
    inner ℂ (sourceCoreFactor μ hF hK .normalizer f : Lp ℂ 2 μ)
      (sourceCoreFactor μ hF hK .damped (sourceCoreFactor μ hF hK .normalizer g) : Lp ℂ 2 μ) =
      inner ℂ (f : Lp ℂ 2 μ) (sourceCoreFactor μ hF hK .covariance g : Lp ℂ 2 μ) := by
  rw [sourceCoreFactor_inner_symm μ hF hK .normalizer,
    source_unbounded_normalized_covariance μ hF hK hposF]

/-- The source result on an arbitrary-measure joint spectral representation:
the common cut union is dense, the generally unbounded normalizer is
self-adjoint on its maximal domain, and the exact operator and smeared
covariance identities are conclusions. -/
theorem source_unbounded_free_source_normalization
    (hposF : ∀ᵐ x ∂μ, 0 < F x) (hposK : ∀ᵐ x ∂μ, 0 < K x) :
    Dense (sourceJointCore μ F K : Set (Lp ℂ 2 μ)) ∧
      IsSelfAdjoint (sourceL2Multiplier μ (fun x => ((Real.sqrt (F x))⁻¹ : ℂ))) ∧
      ∀ f : sourceJointCore μ F K,
        sourceCoreFactor μ hF hK .normalizer
          (sourceCoreFactor μ hF hK .damped (sourceCoreFactor μ hF hK .normalizer f)) =
          sourceCoreFactor μ hF hK .covariance f ∧
        sourceCoreFactor μ hF hK .normalizer (sourceCoreFactor μ hF hK .damped f) =
          sourceCoreFactor μ hF hK .half (sourceCoreFactor μ hF hK .covariance f) ∧
        sourceCoreFactor μ hF hK .normalizer
          (sourceCoreFactor μ hF hK .damped (sourceCoreFactor μ hF hK .kinetic f)) =
          sourceCoreFactor μ hF hK .half f ∧
        ∀ g : sourceJointCore μ F K,
          inner ℂ (sourceCoreFactor μ hF hK .normalizer f : Lp ℂ 2 μ)
            (sourceCoreFactor μ hF hK .damped (sourceCoreFactor μ hF hK .normalizer g) : Lp ℂ 2 μ) =
            inner ℂ (f : Lp ℂ 2 μ) (sourceCoreFactor μ hF hK .covariance g : Lp ℂ 2 μ) :=
  ⟨sourceJointCore_dense μ hF hK hposF hposK,
    source_unbounded_normalizer_selfAdjoint μ hF, fun f =>
      ⟨source_unbounded_normalized_covariance μ hF hK hposF f,
        source_unbounded_mixed_covariance μ hF hK hposF f,
        source_unbounded_mixed_amputation μ hF hK hposF hposK f,
        source_unbounded_smeared_covariance μ hF hK hposF f⟩⟩

end UV
