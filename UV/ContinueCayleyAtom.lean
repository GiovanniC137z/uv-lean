import UV.ContinueCayleyState

/-! The Cayley point at infinity carries no compact spectral mass for the
Cayley transform of an actual densely defined self-adjoint operator. -/

noncomputable section
open MeasureTheory Set Filter ContinuousLinearMap
open scoped Topology ENNReal InnerProductSpace
namespace UV.SectorPlane

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem closing_cayley_dense_difference (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) :
    DenseRange (1 - closingCayley K hK : H →L[ℂ] H) := by
  apply hK.dense_domain.mono
  intro x hx
  let y : K.domain := ⟨x,hx⟩
  let a := (2:ℂ)*Complex.I
  refine ⟨a⁻¹ • (K y + Complex.I • (y:H)), ?_⟩
  rw [map_smul,(closing_cayley_graph_pair K hK y).1]
  change a⁻¹ • a • x = x
  rw [smul_smul, inv_mul_cancel₀ (by norm_num [a]), one_smul]

private def closingAtomCut {X : Type*} [TopologicalSpace X] (N : C(X,ℂ)) {t : ℝ} (ht : 0 < t) : C(X,ℂ) :=
  ⟨fun u => ((t/(t + ‖N u‖) : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (continuous_const.div (continuous_const.add N.continuous.norm)
      (fun u => ne_of_gt (add_pos_of_pos_of_nonneg ht (norm_nonneg (N u)))))⟩

private theorem closing_atom_cut_bounds {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (N : C(X,ℂ)) {t : ℝ} (ht : 0 < t) :
    ‖closingAtomCut N ht‖ ≤ 1 ∧ ‖closingAtomCut N ht * N‖ ≤ t := by
  have hp (x : X) : 0 < t + ‖N x‖ := add_pos_of_pos_of_nonneg ht (norm_nonneg _)
  have he (x : X) : ‖closingAtomCut N ht x‖ = t/(t+‖N x‖) :=
    by change ‖((t/(t+‖N x‖) : ℝ) : ℂ)‖ = _; rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (div_pos ht (hp x))]
  constructor
  · apply (ContinuousMap.norm_le _ zero_le_one).mpr
    intro x
    rw [he,div_le_one (hp x)]
    linarith [norm_nonneg (N x)]
  · apply (ContinuousMap.norm_le _ ht.le).mpr
    intro x
    rw [ContinuousMap.mul_apply,norm_mul,he,div_mul_eq_mul_div,div_le_iff₀ (hp x)]
    nlinarith [sq_nonneg t]

/-- A compact state of the Cayley unitary of an arbitrary self-adjoint
generator has zero mass at the exceptional point, even if that point
belongs to the continuous spectrum. -/
theorem closing_cayley_state_no_atom (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) (v : H) :
    closingCompactState (cfcHom (R := ℂ) (closing_cayley_normal K hK)) v
      {u : spectrum ℂ (closingCayley K hK) | (u : ℂ) = 1} = 0 := by
  let U := closingCayley K hK
  let π := cfcHom (R := ℂ) (closing_cayley_normal K hK)
  let μ := closingCompactState π v
  let A := {u : spectrum ℂ U | (u : ℂ) = 1}
  have hm : MeasurableSet A := isClosed_eq continuous_subtype_val continuous_const |>.measurableSet
  let N : C(spectrum ℂ U, ℂ) := 1-(ContinuousMap.id ℂ).restrict _
  have hN : π N = 1-U := by simp [N,π,U,map_sub,map_one,cfcHom_id]
  have hlimit (ε : ℝ) (hε : 0 < ε) : μ.real A ≤ ‖v‖ * ε := by
    obtain ⟨w,hw⟩ := (closing_cayley_dense_difference K hK).exists_dist_lt v (half_pos hε)
    have hw' : ‖v-(1-U) w‖ < ε/2 := by simpa only [dist_eq_norm] using hw
    let t := ε/(2*(1+‖w‖))
    have ht : 0 < t := by dsimp [t]; positivity
    let f := closingAtomCut N ht
    obtain ⟨hsmall,hthin⟩ := closing_atom_cut_bounds N ht
    have hnorm (g : C(spectrum ℂ U,ℂ)) : ‖π g‖ = ‖g‖ := norm_cfcHom U g (closing_cayley_normal K hK)
    have happ : ‖π f v‖ ≤ ε := by
      have hx : π f v = (π f) (v-(1-U) w) + (π (f*N)) w := by
        rw [map_mul,ContinuousLinearMap.mul_apply,hN,map_sub,sub_add_cancel]
      rw [hx]
      calc
        _ ≤ ‖π f (v-(1-U) w)‖ + ‖π (f*N) w‖ := norm_add_le _ _
        _ ≤ ‖π f‖ * ‖v-(1-U) w‖ + ‖π (f*N)‖ * ‖w‖ :=
          add_le_add ((π f).le_opNorm _) ((π (f*N)).le_opNorm _)
        _ ≤ 1 * (ε/2) + t * ‖w‖ := by
          rw [hnorm,hnorm]
          exact add_le_add (mul_le_mul hsmall hw'.le (norm_nonneg _) zero_le_one)
            (mul_le_mul_of_nonneg_right hthin (norm_nonneg _))
        _ ≤ ε := by
          have ht' : t*(2*(1+‖w‖)) = ε := div_mul_cancel₀ _ (by positivity)
          nlinarith
    have hi : Integrable (fun u => f u) μ :=
      f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hEq := congrArg Complex.re (closing_compact_state_integral π v f)
    have hl : μ.real A ≤ (⟪v,π f v⟫_ℂ).re := by
      rw [←hEq,←RCLike.re_eq_complex_re,←integral_re hi,←integral_indicator_one hm]
      apply integral_mono ((integrable_const (1:ℝ)).indicator hm) hi.re
      intro u
      by_cases hu : u ∈ A
      · rw [indicator_of_mem hu]
        have hz : N u = 0 := sub_eq_zero.mpr (show (1:ℂ) = u from Eq.symm hu)
        change 1 ≤ t/(t+‖N u‖)
        rw [hz,norm_zero,add_zero,div_self ht.ne']
      · rw [indicator_of_notMem hu]
        change 0 ≤ t/(t+‖N u‖)
        positivity
    exact hl.trans ((re_inner_le_norm (𝕜 := ℂ) v (π f v)).trans (mul_le_mul_of_nonneg_left happ (norm_nonneg _)))
  change μ A = 0
  have hzero : μ.real A = 0 := by
    by_contra hne
    have hpos : 0 < μ.real A := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hne)
    have hd : 0 < ‖v‖+1 := by positivity
    have h := hlimit (μ.real A/(‖v‖+1)) (div_pos hpos hd)
    have h' : μ.real A * (‖v‖+1) ≤ ‖v‖ * μ.real A := by
      rwa [mul_div_assoc', le_div_iff₀ hd] at h
    nlinarith
  exact (ENNReal.toReal_eq_zero_iff _).mp hzero |>.resolve_right (measure_ne_top _ _)

end UV.SectorPlane
