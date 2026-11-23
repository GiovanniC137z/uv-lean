import UV.ContinueNormalCircleWord
import Mathlib.MeasureTheory.Function.Floor

/-! Unfold the independent integer lifts of a closed periodic word.
The half-open unit cube partitions the real increments without duplicating
any boundary points, including the empty cube for a single insertion. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter UV.SectorPlane
open scoped Matrix.Norms.L2Operator

namespace UV

def normalUnitCell (n : ℕ) := Set.pi univ (fun _ : Fin n => Ico (0:ℝ) 1)

private def normalCubeCell {n : ℕ} (h : Fin n → ℤ) : Set (Fin n → ℝ) :=
  (fun x : Fin n → ℝ => fun i => ⌊x i⌋) ⁻¹' {h}

private theorem normal_cube_cell_measurable {n : ℕ} (h : Fin n → ℤ) : MeasurableSet (normalCubeCell h) := by
  unfold normalCubeCell
  exact (measurable_pi_lambda _ (fun i => Int.measurable_floor.comp (measurable_pi_apply i))) (measurableSet_singleton _)

private theorem normal_cube_cell_membership {n : ℕ} (x : Fin n → ℝ) (h : Fin n → ℤ) :
    (fun i => x i+(h i:ℝ)) ∈ normalCubeCell h ↔ x ∈ normalUnitCell n := by
  change (fun i => ⌊x i+(h i:ℝ)⌋) = h ↔ ∀ i ∈ (univ : Set (Fin n)), x i ∈ Ico 0 1
  simp only [funext_iff,Int.floor_add_intCast,add_eq_right,Int.floor_eq_zero_iff,mem_univ,true_implies]

theorem normal_cube_cell_sum {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : (Fin n → ℝ) → E} (hf : Integrable f) :
    HasSum (fun h : Fin n → ℤ => ∫ x in normalUnitCell n, f (fun i => x i+(h i:ℝ))) (∫ x, f x) := by
  classical
  have hfull : ⋃ h : Fin n → ℤ, normalCubeCell h = univ := by
    exact eq_univ_of_forall fun x => mem_iUnion.mpr ⟨fun i => ⌊x i⌋,rfl⟩
  have hd : Pairwise (fun h k : Fin n → ℤ => Disjoint (normalCubeCell h) (normalCubeCell k)) := by
    intro h k hne
    exact Set.disjoint_left.mpr fun _ hh hk => hne (hh.symm.trans hk)
  have hsum := hasSum_integral_iUnion (fun h : Fin n → ℤ => normal_cube_cell_measurable h) hd hf.integrableOn
  rw [hfull,setIntegral_univ] at hsum
  apply hsum.congr_fun
  intro h
  let y : Fin n → ℝ := fun i => (h i:ℝ)
  have he : (fun x : Fin n → ℝ => x+y) ⁻¹' normalCubeCell h = normalUnitCell n := by
    ext x; exact normal_cube_cell_membership x h
  have htr := (measurePreserving_add_right volume y).setIntegral_preimage_emb (Homeomorph.addRight y).measurableEmbedding f (normalCubeCell h)
  rw [he] at htr
  exact htr

theorem normal_cube_tsum_integral {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : (Fin n → ℝ) → E} (hf : Integrable f) :
    (∫ x in normalUnitCell n, ∑' h : Fin n → ℤ, f (fun i => x i+(h i:ℝ))) = ∫ x, f x := by
  have hi (h : Fin n → ℤ) : IntegrableOn (fun x : Fin n → ℝ => f (fun i => x i+(h i:ℝ))) (normalUnitCell n) :=
    ((measurePreserving_add_right volume (fun i => (h i:ℝ))).integrable_comp_of_integrable hf).integrableOn
  exact (hasSum_integral_of_summable_integral_norm hi (normal_cube_cell_sum hf.norm).summable).unique (normal_cube_cell_sum hf)

/-- Unfold physical increments after summing their lifts. Each independent
circle coordinate contributes its physical Jacobian L. -/
theorem normal_scaled_cube_tsum_integral {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {L : ℝ} (hL : 0 < L) {f : (Fin n → ℝ) → E} (hf : Integrable f) :
    L^n • (∫ t in normalUnitCell n, ∑' h : Fin n → ℤ, f (fun j => L*(t j+(h j:ℝ)))) = ∫ x, f x := by
  have hi := (integrable_comp_smul_iff (volume : Measure (Fin n → ℝ)) f hL.ne').mpr hf
  change L^n • (∫ t in normalUnitCell n, ∑' h : Fin n → ℤ, f (L • (fun j => t j+(h j:ℝ)))) = ∫ x, f x
  rw [normal_cube_tsum_integral hi,Measure.integral_comp_smul_of_nonneg volume f L (hR := hL.le),Module.finrank_pi,smul_smul]
  simp [hL.ne']

theorem normal_winding_fixed_transfer_bound {n : ℕ} {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (θ : ℝ) (w : ℤ)
    (u : Fin (n+1) → UnitVector OSFourSpace) (p : Fin (n+1) → OSFourSpace) :
    Integrable (normalWindingTrace m L θ w u p) ∧ (∫ x, ‖normalWindingTrace m L θ w u p x‖) ≤
      (L*4*(2:ℝ)^(n+1)*Real.exp (-(m/2)*|(w:ℝ)*L|))*(4/m)^n := by
  let d := normalOpenIncrements (r := n) ((w:ℝ)*L)
  let A := fun x i => normalDiracCover normalCoverGamma5 m (p i) (d x i)*diracSlash (u i).val
  let M := L*4*(2:ℝ)^(n+1)*Real.exp (-(m/2)*|(w:ℝ)*L|)
  let g := fun x : ℝ => Real.exp (-(m/2)*|x|)
  have hg := normal_open_laplace_mass hm
  have hprod : Integrable (fun x : Fin n → ℝ => ∏ i, g (x i)) := Integrable.fintype_prod (fun _ : Fin n => hg.1)
  have hi := hprod.const_mul M
  have hF := normal_winding_trace_measurable m L θ w u (p := fun _ : Fin n → ℝ => p) (fun _ => measurable_const) (x := id) (fun j => measurable_pi_apply j)
  suffices hle : ∀ x, ‖normalWindingTrace m L θ w u p x‖ ≤ M*∏ i, g (x i) by
    have hiF := hi.mono' hF.aestronglyMeasurable (Eventually.of_forall hle)
    refine ⟨hiF,(integral_mono hiF.norm hi hle).trans_eq ?_⟩
    rw [integral_const_mul,integral_fintype_prod_volume_eq_pow g]
    simp only [M,g,Fintype.card_fin,hg.2]
  intro x
  have hA (i) : ‖A x i‖ ≤ 2*Real.exp (-m*|d x i|) := by
    apply (norm_mul_le _ _).trans
    rw [wilson_slash_opnorm,(u i).property,mul_one]
    apply (normal_dirac_cover_bound _ normal_cover_gamma_norm hm _ _).trans
    have hle := mul_le_mul_of_nonneg_right (normal_cover_energy_bounds hm (p i)).1 (abs_nonneg (d x i))
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
  have hword : ‖normalOrderedWord (A x)‖ ≤ 2^(n+1)*∏ i, Real.exp (-m*|d x i|) := by
    apply (List.norm_prod_le _).trans
    rw [List.map_ofFn,List.prod_ofFn]
    simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
      Finset.prod_le_prod (s := Finset.univ) (fun _ _ => norm_nonneg _) (fun i _ => hA i)
  have ht := (wilson_trace_le_opnorm (normalOrderedWord (A x))).trans (mul_le_mul_of_nonneg_left hword (by norm_num))
  rw [normalWindingTrace,norm_mul,normal_loop_phase_norm hL]
  apply (mul_le_mul_of_nonneg_left ht hL.le).trans
  rw [←Real.exp_sum,←Finset.mul_sum]
  have he := normal_open_increment_envelope hm ((w:ℝ)*L) x
  have hh := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ L*4*(2:ℝ)^(n+1))
  simpa only [M,d,mul_assoc] using hh

theorem normal_winding_fixed_transfer {n : ℕ} {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (θ : ℝ) (w : ℤ)
    (u : Fin (n+1) → UnitVector OSFourSpace) (p : Fin (n+1) → OSFourSpace) :
    Integrable (normalWindingTrace m L θ w u p) :=
  (normal_winding_fixed_transfer_bound hm hL θ w u p).1

/-- The circle coordinates have physical measure dz=L dt. Unfolding one
specified winding on the normalized cube gives exactly its cover integral,
including the center factor L in the trace. -/
theorem normal_periodic_winding_integral {n : ℕ} {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (θ : ℝ) (w : ℤ)
    (u : Fin (n+1) → UnitVector OSFourSpace) (p : Fin (n+1) → OSFourSpace) :
    L^n • (∫ t in normalUnitCell n, ∑' h : Fin n → ℤ, normalWindingTrace m L (-θ) w u p (fun j => L*(t j+(h j:ℝ)))) =
      ∫ x, normalWindingTrace m L (-θ) w u p x :=
  normal_scaled_cube_tsum_integral hL (normal_winding_fixed_transfer hm hL (-θ) w u p)

end UV
