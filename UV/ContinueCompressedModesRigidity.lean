import UV.ContinueCompressedModesVertex
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension

/-! The regular scalar electric vertex forces a constant scalar weight.
The Ward identity and the soft limit are imposed on a single
normal mode. Differentiability of the weight follows from the C²
inverse propagator; the mixed partials are derived. -/

noncomputable section

open Filter Set UV.SectorPlane
open scoped Matrix.Norms.L2Operator Topology

namespace UV

/-- The undamped charge-one Clifford vertex as a real continuous linear map. -/
def compressedCliffordVertex : OSFourSpace →L[ℝ] DiracMatrix :=
  LinearMap.toContinuousLinearMap {
    toFun := fun v => Complex.I • diracSlash v
    map_add' := fun x y => by rw [diracSlash_add,smul_add]
    map_smul' := fun r v => by
      rw [diracSlash_real_smul,smul_comm]
      ext i j
      exact Complex.real_smul.symm }

theorem compressed_clifford_norm (v : OSFourSpace) : ‖compressedCliffordVertex v‖ = ‖v‖ := by
  change ‖Complex.I • diracSlash v‖ = ‖v‖
  rw [norm_smul,Complex.norm_I,one_mul,wilson_slash_opnorm]

theorem compressed_clifford_injective : Function.Injective compressedCliffordVertex := by
  intro x y h
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [←compressed_clifford_norm,map_sub,h,sub_self,norm_zero]

/-- Ward contraction and the regular soft limit determine the derivative of D. -/
theorem compressed_regular_ward_fderiv (D : OSFourSpace → DiracMatrix) (g : OSFourSpace → ℝ)
    (Γ : OSFourSpace → OSFourSpace → OSFourSpace →L[ℝ] DiracMatrix) (hD : Differentiable ℝ D)
    (hWard : ∀ p Q, Q ≠ 0 → Γ p Q Q = D (p+Q)-D p)
    (hsoft : ∀ p v, Tendsto (fun Q => Γ p Q v) (𝓝[≠] 0) (𝓝 (g p • compressedCliffordVertex v))) (p : OSFourSpace) :
    fderiv ℝ D p = g p • compressedCliffordVertex := by
  ext v : 1
  by_cases hv : v = 0
  · simp [hv]
  have hray : Tendsto (fun r : ℝ => r • v) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [id_eq,zero_smul] using
        ((continuous_id.smul continuous_const : Continuous (fun r : ℝ => r • v)).tendsto (0:ℝ)).mono_left
          (nhdsWithin_le_nhds (s := ({0}:Set ℝ)ᶜ))
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact smul_ne_zero hr hv
  have hlim := ((hD p).hasFDerivAt.hasLineDerivAt v).tendsto_slope_zero
  have hw := (hsoft p v).comp hray
  apply tendsto_nhds_unique hlim (hw.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with r hr
  change Γ p (r • v) v = r⁻¹ • (D (p+r • v)-D p)
  rw [←hWard p (r • v) (smul_ne_zero hr hv),map_smul,inv_smul_smul₀ hr]

/-- Exact C² mixed partial symmetry forces every derivative of g to vanish.
The two coordinate unit vectors are distinguished only to witness Clifford
independence. -/
theorem compressed_scalar_vertex_rigidity (D : OSFourSpace → DiracMatrix) (g : OSFourSpace → ℝ)
    (hD : ContDiff ℝ 2 D) (hJac : ∀ p, fderiv ℝ D p = g p • compressedCliffordVertex) :
    (∀ p, fderiv ℝ g p = 0) ∧ ∀ p, g p = g 0 := by
  let A := compressedCliffordVertex
  let e := (osAxis 0).val
  have hn : ‖A e‖ = 1 := (compressed_clifford_norm e).trans (osAxis 0).property
  obtain ⟨φ,_,hφ⟩ := exists_dual_vector ℝ (A e) (norm_pos_iff.mp (by rw [hn]; norm_num))
  have hφ1 : φ (A e) = 1 := hφ.trans (by exact_mod_cast hn)
  have hg : Differentiable ℝ g := by
    have heq : g = fun p => φ (fderiv ℝ D p e) := by
      funext p
      rw [hJac,ContinuousLinearMap.smul_apply,map_smul,hφ1,smul_eq_mul,mul_one]
    rw [heq]
    exact φ.differentiable.comp (((hD.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)).clm_apply (differentiable_const e))
  have hzero : ∀ p, fderiv ℝ g p = 0 := by
    intro p
    have hsym := hD.contDiffAt.isSymmSndFDerivAt (x := p) (by simp)
    have hJF : fderiv ℝ D = fun x => g x • A := funext hJac
    have hmix (u v : OSFourSpace) : (fderiv ℝ g p u) • v = (fderiv ℝ g p v) • u := by
      apply compressed_clifford_injective
      rw [map_smul,map_smul]
      have h := hsym u v
      rw [hJF,fderiv_smul_const (hg p) A] at h
      exact h
    have h0 := congrArg (fun x : OSFourSpace => x (1:Fin 4)) (hmix e (osAxis 1).val)
    have hder : fderiv ℝ g p e = 0 := by
      simpa [e,osAxis,PiLp.smul_apply,EuclideanSpace.single_apply] using h0
    ext v
    have hv := hmix v e
    rw [hder,zero_smul] at hv
    have hvn := congrArg norm hv
    simpa [norm_smul,show ‖e‖ = 1 from (osAxis 0).property] using hvn
  refine ⟨hzero,?_⟩
  have heq := eq_of_fderiv_eq hg (differentiable_const (c := g 0)) (fun p => by simp [hzero]) 0 rfl
  exact congrFun heq

theorem compressed_regular_ward_constant (D : OSFourSpace → DiracMatrix) (g : OSFourSpace → ℝ)
    (Γ : OSFourSpace → OSFourSpace → OSFourSpace →L[ℝ] DiracMatrix)
    (hD : ContDiff ℝ 2 D) (hWard : ∀ p Q, Q ≠ 0 → Γ p Q Q = D (p+Q)-D p)
    (hsoft : ∀ p v, Tendsto (fun Q => Γ p Q v) (𝓝[≠] 0) (𝓝 (g p • compressedCliffordVertex v))) :
    (∀ p, fderiv ℝ g p = 0) ∧ ∀ p, g p = g 0 :=
  compressed_scalar_vertex_rigidity D g hD
    (compressed_regular_ward_fderiv D g Γ (hD.differentiable (by norm_num)) hWard hsoft)

end UV
