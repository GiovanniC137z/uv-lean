import UV.ContinueWilsonTransverseLimit
import UV.ContinueWilsonHardPhoton

/-! The transverse Maxwell normalization and the finite superposition of
connected Wilson two-point diagrams with no internal photon bridge. -/

noncomputable section

open MeasureTheory Filter UV.SectorPlane
open scoped Topology RealInnerProductSpace

namespace UV

theorem wilson_maxwell_unit_tree (k : OSFourSpace) (v : UnitVector OSFourSpace)
    (hv : ⟪k,v.val⟫ = 0) : wilsonTransverseEntry v v k = 1 := by
  have h : v.val ∈ (ℝ ∙ k)ᗮ := Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hv
  rw [wilsonTransverseEntry,Submodule.starProjection_eq_self_iff.mpr h,real_inner_self_eq_norm_sq,v.property]
  norm_num

/-- The input is a finite connected contracted graph with two external
marks. The deletion witnesses use the actual remaining oriented edges. -/
structure WilsonTwoPointDiagram where
  vertices : ℕ
  edges : ℕ
  src : Fin edges → Option (Fin vertices)
  dst : Fin edges → Option (Fin vertices)
  graph : SimpleGraph (Option (Fin vertices))
  connected : graph.Connected
  covers : NetworkOrientationCovers graph src dst
  basis : WilsonIncidenceBasis (groundedNetworkIncidence src dst).row
  first : Option (Fin vertices)
  second : Option (Fin vertices)
  deletion : basis.tree → SimpleGraph (Option (Fin vertices))
  deletion_connected : ∀ j, (deletion j).Connected
  deletion_covers : ∀ j : basis.tree, NetworkOrientationCovers (deletion j)
    (fun e : {e : Fin edges // e ≠ j.val} => src e) (fun e => dst e)

variable {ι : Type*} [Fintype ι]

def WilsonTwoPointDiagram.amplitude (d : WilsonTwoPointDiagram) (L lam : ℝ)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (k : OSFourSpace) (v w : UnitVector OSFourSpace) : ℂ :=
  (wilsonGraphOfIncidence d.src d.dst d.basis d.first d.second).summedAmplitude L lam T
    (fun x j => d.basis.offset (fun i => wilsonExternalPair d.first d.second x (some i)) j) d.basis.coefficient k v w

def WilsonTwoPointDiagram.coefficient (d : WilsonTwoPointDiagram) (L lam : ℝ)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (u v : UnitVector OSFourSpace) : ℂ :=
  (wilsonGraphOfIncidence d.src d.dst d.basis d.first d.second).summedCoefficient L lam T
    (fun x j => d.basis.offset (fun i => wilsonExternalPair d.first d.second x (some i)) j) d.basis.coefficient u v v

/-- Evaluate in the oriented chart of the labelled sector plane, transporting
the momentum and both unit directions together. -/
theorem SectorPlane.Plane.wilson_summed_amplitude_chart {E : Type*} [NormedAddCommGroup E] (diamond : Plane E)
    (d : WilsonTwoPointDiagram) {L : ℝ} (hL : 0 < L) (lam : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (k : OSFourSpace) (v w : UnitVector OSFourSpace) :
    d.amplitude L lam T (diamond.osOrientedChart k) (wilsonRotateUnit diamond.osOrientedChart v)
      (wilsonRotateUnit diamond.osOrientedChart w) = d.amplitude L lam T k v w :=
  WilsonCurrentGraph.summedAmplitude_rotate _ hL lam T diamond.osOrientedChart _
    (d.basis.offset_pair_rotate d.src d.dst d.first d.second _) _ k v w

/-- A transverse unit polarization can be chosen for every
four-momentum. Reflection transports the standard transverse axis. -/
theorem wilson_transverse_polarizations_exist :
    ∃ e : OSFourSpace → UnitVector OSFourSpace, ∀ k, ⟪k,(e k).val⟫ = 0 := by
  have h (k : OSFourSpace) : ∃ v : UnitVector OSFourSpace, ⟪k,v.val⟫ = 0 := by
    by_cases hk : k = 0
    · exact ⟨osAxis 1,by simp [hk]⟩
    let u : UnitVector OSFourSpace := ⟨‖k‖⁻¹ • k,by simp [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),hk]⟩
    let S := (ℝ ∙ ((osAxis 0).val-u.val))ᗮ.reflection
    have hS : S (osAxis 0).val = u.val := Submodule.reflection_sub ((osAxis 0).property.trans u.property.symm)
    have huv : ⟪u.val,S (osAxis 1).val⟫ = 0 := by
      rw [←hS,S.inner_map_map]
      simp [osAxis,EuclideanSpace.inner_single_left,EuclideanSpace.single_apply]
    have hku : ‖k‖ • u.val = k := by
      change ‖k‖ • ‖k‖⁻¹ • k = k
      rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hk),one_smul]
    refine ⟨wilsonRotateUnit S (osAxis 1),?_⟩
    change ⟪k,S (osAxis 1).val⟫ = 0
    rw [←hku,real_inner_smul_left,huv,mul_zero]
  exact ⟨fun k => (h k).choose,fun k => (h k).choose_spec⟩

/-- The absolutely convergent integral for the coefficient is independent
of the reference orthogonal unit pair used to write it. -/
theorem WilsonTwoPointDiagram.coefficient_eq (d : WilsonTwoPointDiagram) {L lam : ℝ}
    (hL : 0 < L) (hlam : 0 ≤ lam) (hl : 2*lam < 1) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (u v u' v' : UnitVector OSFourSpace) (huv : ⟪u.val,v.val⟫ = 0) (huv' : ⟪u'.val,v'.val⟫ = 0) :
    d.coefficient L lam T u v = d.coefficient L lam T u' v' := by
  obtain ⟨e,he⟩ := wilson_transverse_polarizations_exist
  have H := wilson_incidence_transverse_limit d.src d.dst d.basis hL hlam hl T d.deletion
    d.deletion_connected d.deletion_covers d.first d.second
  exact tendsto_nhds_unique (H u v huv e (fun k _ => he k)).1 (H u' v' huv' e (fun k _ => he k)).1

/-- Add the ordinary Maxwell tree once and sum any finite collection of
encoded diagrams with fixed complex coefficients, such as symmetry factors. -/
theorem wilson_finite_transverse_coefficient {I : Type*} [Fintype I] (d : I → WilsonTwoPointDiagram)
    (c : I → ℂ) {L lam : ℝ} (hL : 0 < L) (hlam : 0 ≤ lam) (hl : 2*lam < 1)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (u v : UnitVector OSFourSpace) (huv : ⟪u.val,v.val⟫ = 0)
    (e : OSFourSpace → UnitVector OSFourSpace) (he : ∀ k ≠ 0, ⟪k,(e k).val⟫ = 0) :
    let F := fun k : OSFourSpace => ((‖k‖^2 * wilsonTransverseEntry (e k) (e k) k : ℝ) : ℂ) +
      ∑ i, c i * (d i).amplitude L lam T k (e k) (e k)
    Tendsto (fun k : OSFourSpace => F k / (‖k‖^2 : ℝ)) (𝓝[≠] 0)
      (𝓝 (1 + ∑ i, c i * (d i).coefficient L lam T u v)) ∧ Tendsto F (𝓝[≠] 0) (𝓝 0) := by
  dsimp only
  have hg (i : I) := wilson_incidence_transverse_limit (d i).src (d i).dst (d i).basis hL hlam hl T
    (d i).deletion (d i).deletion_connected (d i).deletion_covers (d i).first (d i).second u v huv e he
  have hs := tendsto_finset_sum Finset.univ (fun i _ => (tendsto_const_nhds (x := c i)).mul (hg i).1)
  have h : Tendsto (fun k : OSFourSpace => 1 + ∑ i, c i *
      ((d i).amplitude L lam T k (e k) (e k) / (‖k‖^2 : ℝ))) (𝓝[≠] 0)
      (𝓝 (1 + ∑ i, c i * (d i).coefficient L lam T u v)) := tendsto_const_nhds.add hs
  have hq := h.congr' (f₂ := fun k : OSFourSpace =>
    (((‖k‖^2 * wilsonTransverseEntry (e k) (e k) k : ℝ) : ℂ) + ∑ i, c i * (d i).amplitude L lam T k (e k) (e k)) / (‖k‖^2 : ℝ)) (by
      filter_upwards [self_mem_nhdsWithin] with k hk
      have hn : ((‖k‖^2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hk))
      rw [wilson_maxwell_unit_tree _ _ (he k hk),mul_one,add_div,div_self hn,Finset.sum_div]
      simp only [div_eq_mul_inv,mul_assoc])
  refine ⟨hq,?_⟩
  have hz : Tendsto (fun k : OSFourSpace => ((‖k‖^2 : ℝ) : ℂ)) (𝓝[≠] 0) (𝓝 0) := by
    have hcont : Continuous (fun k : OSFourSpace => ((‖k‖^2 : ℝ) : ℂ)) := by fun_prop
    simpa only [norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,Complex.ofReal_zero] using
      (hcont.continuousAt (x := (0:OSFourSpace))).tendsto.mono_left
        (nhdsWithin_le_nhds (s := {0}ᶜ))
  have hzq := hz.mul hq
  rw [zero_mul] at hzq
  apply hzq.congr'
  filter_upwards [self_mem_nhdsWithin] with k hk
  have hn : ((‖k‖^2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hk))
  change _ * (_ / _) = _
  field_simp [hn]
end UV
