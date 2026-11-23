import UV.ContinueNormalCoverPath

/-! Absolute normal-displacement integrals of the ordered open Dirac chain,
including each unit-polarized vertex. No normal winding is excluded. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter UV.SectorPlane
open scoped Matrix.Norms.L2Operator

namespace UV

variable {r : ℕ}

def normalOpenVertex (u : Fin r → UnitVector OSFourSpace) (j : Fin (r+1)) : DiracMatrix :=
  Fin.lastCases 1 (fun i => diracSlash (u i).val) j

theorem normal_open_vertex_norm (u : Fin r → UnitVector OSFourSpace) (j : Fin (r+1)) :
    ‖normalOpenVertex u j‖ = 1 := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [normalOpenVertex]
  · simpa only [normalOpenVertex,Fin.lastCases_castSucc,wilson_slash_opnorm] using (u i).property

def normalOpenDiracWord (J : DiracMatrix) (m D : ℝ) (u : Fin r → UnitVector OSFourSpace)
    (p : Fin (r+1) → OSFourSpace) (x : Fin r → ℝ) : DiracMatrix :=
  (List.ofFn (fun j => normalDiracCover J m (p j) (normalOpenIncrements D x j)*normalOpenVertex u j)).prod

theorem normal_open_dirac_majorant (J : DiracMatrix) (hJ : ‖J‖ = 1) {m : ℝ} (hm : 0 < m) (D : ℝ)
    (u : Fin r → UnitVector OSFourSpace) (p : Fin (r+1) → OSFourSpace) (x : Fin r → ℝ) :
    ‖normalOpenDiracWord J m D u p x‖ ≤ (2^(r+1)*Real.exp (-(m/2)*|D|))*∏ j, Real.exp (-(m/2)*|x j|) := by
  let d := normalOpenIncrements D x
  let A := fun j => normalDiracCover J m (p j) (d j)*normalOpenVertex u j
  have h (j) : ‖A j‖ ≤ 2*Real.exp (-m*|d j|) := by
    apply (norm_mul_le _ _).trans
    rw [normal_open_vertex_norm,mul_one]
    apply (normal_dirac_cover_bound J hJ hm (p j) (d j)).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg (normal_cover_energy_bounds hm (p j)).1) (abs_nonneg _)
  calc
    ‖normalOpenDiracWord J m D u p x‖ ≤ ((List.ofFn A).map norm).prod := (List.ofFn A).norm_prod_le
    _ = ∏ j, ‖A j‖ := by rw [List.map_ofFn,List.prod_ofFn]; rfl
    _ ≤ ∏ j, 2*Real.exp (-m*|d j|) := Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => h j)
    _ = 2^(r+1)*Real.exp (-m*∑ j, |d j|) := by
      rw [Finset.prod_mul_distrib,←Real.exp_sum,←Finset.mul_sum]
      simp
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (normal_open_increment_envelope hm D x) (by positivity)

local instance normalDiracMeasurableSpace : MeasurableSpace DiracMatrix := borel _
local instance normalDiracBorelSpace : BorelSpace DiracMatrix := ⟨rfl⟩

theorem normal_cover_args_measurable {Z : Type*} [MeasurableSpace Z] (J : DiracMatrix) (m : ℝ)
    {p : Z → OSFourSpace} (hp : Measurable p) {d : Z → ℝ} (hd : Measurable d) :
    Measurable (fun z => normalDiracCover J m (p z) (d z)) := by
  have hs : Measurable Real.sign := by
    unfold Real.sign
    exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
      (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const measurable_const)
  have hE : Measurable (fun z => normalCoverEnergy m (p z)) := by unfold normalCoverEnergy; fun_prop
  have hN : Continuous (freeDiracNumerator m) := by
    unfold freeDiracNumerator diracSlash
    apply Continuous.add _ continuous_const
    apply continuous_const.smul
    apply continuous_finset_sum
    intro j _
    exact (Complex.continuous_ofReal.comp (EuclideanSpace.proj j).continuous).smul continuous_const
  have hNm := hN.measurable.comp hp
  unfold normalDiracCover
  fun_prop

theorem normal_open_word_args_measurable {Z : Type*} [MeasurableSpace Z] (J : DiracMatrix) (m D : ℝ)
    (u : Fin r → UnitVector OSFourSpace) {p : Z → Fin (r+1) → OSFourSpace} (hp : ∀ j, Measurable (p · j))
    {x : Z → Fin r → ℝ} (hx : ∀ j, Measurable (x · j)) :
    Measurable (fun z => normalOpenDiracWord J m D u (p z) (x z)) := by
  have hd (j : Fin (r+1)) : Measurable (fun z => normalOpenIncrements D (x z) j) := by
    refine Fin.cases ?_ (fun i => ?_) j
    · exact measurable_const.sub (Finset.measurable_sum _ (fun i _ => hx i))
    · exact hx i
  let A := fun j z => normalDiracCover J m (p z j) (normalOpenIncrements D (x z) j)*normalOpenVertex u j
  have hA (j) : Measurable (A j) := (normal_cover_args_measurable J m (hp j) (hd j)).mul_const _
  have hl (l : List (Fin (r+1))) : Measurable (fun z => (l.map (fun j => A j z)).prod) := by
    induction l with
    | nil => exact measurable_const
    | cons j l ih => exact (hA j).mul ih
  simpa only [normalOpenDiracWord,List.map_ofFn,Function.comp_def,A] using hl (List.ofFn (fun i : Fin (r+1) => i))

theorem normal_open_word_measurable (J : DiracMatrix) (m D : ℝ) (u : Fin r → UnitVector OSFourSpace)
    (p : Fin (r+1) → OSFourSpace) : Measurable (normalOpenDiracWord J m D u p) :=
  normal_open_word_args_measurable J m D u (p := fun _ => p) (fun _ => measurable_const) (x := id) measurable_pi_apply

theorem normal_open_dirac_integral (J : DiracMatrix) (hJ : ‖J‖ = 1) {m : ℝ} (hm : 0 < m) (D : ℝ)
    (u : Fin r → UnitVector OSFourSpace) (p : Fin (r+1) → OSFourSpace) :
    Integrable (normalOpenDiracWord J m D u p) ∧ (∫ x, ‖normalOpenDiracWord J m D u p x‖) ≤
      2^(r+1)*Real.exp (-(m/2)*|D|)*(4/m)^r := by
  let g := fun t : ℝ => Real.exp (-(m/2)*|t|)
  have hg := normal_open_laplace_mass hm
  have H : Integrable (fun x : Fin r → ℝ => ∏ j, g (x j)) := Integrable.fintype_prod (fun _ : Fin r => hg.1)
  have hi := H.const_mul (2^(r+1)*Real.exp (-(m/2)*|D|))
  have hb := normal_open_dirac_majorant J hJ hm D u p
  have hF := hi.mono' (normal_open_word_measurable J m D u p).aestronglyMeasurable (Eventually.of_forall hb)
  refine ⟨hF,(integral_mono hF.norm hi hb).trans_eq ?_⟩
  rw [integral_const_mul,integral_fintype_prod_volume_eq_pow g]
  simp only [Fintype.card_fin,g,hg.2]

/-- Uniform over both endpoints in one period and all routed carrier
momenta, including the case of no vertex or coincident endpoints. -/
theorem normal_open_all_windings (J : DiracMatrix) (hJ : ‖J‖ = 1) {m L : ℝ} (hm : 0 < m) (hL : 0 < L)
    (z z' : ℝ) (hz : z ∈ Icc 0 L) (hz' : z' ∈ Icc 0 L) (u : Fin r → UnitVector OSFourSpace)
    (p : ℤ → Fin (r+1) → OSFourSpace) :
    let term := fun w : ℤ => ∫ x, ‖normalOpenDiracWord J m (z'-z+(w:ℝ)*L) u (p w) x‖
    let g := fun w : ℤ => Real.exp (m*L/2)*Real.exp (-(m*L/2)*|(w:ℝ)|)
    Summable term ∧ (∑' w, term w) ≤ (2^(r+1)*(4/m)^r)*∑' w, g w := by
  have hδ : |z'-z| ≤ L := abs_le.mpr ⟨by linarith [hz.2,hz'.1],by linarith [hz.1,hz'.2]⟩
  obtain ⟨hg,hw⟩ := normal_winding_majorant hm hL
  let C := (2:ℝ)^(r+1)*(4/m)^r
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hs := hg.mul_left C
  have hb (w : ℤ) := (normal_open_dirac_integral J hJ hm (z'-z+(w:ℝ)*L) u (p w)).2
  have hle (w : ℤ) : (∫ x, ‖normalOpenDiracWord J m (z'-z+(w:ℝ)*L) u (p w) x‖) ≤
      C*(Real.exp (m*L/2)*Real.exp (-(m*L/2)*|(w:ℝ)|)) := by
    apply (hb w).trans
    rw [mul_right_comm]
    exact mul_le_mul_of_nonneg_left (hw _ hδ w) hC
  have hf := Summable.of_nonneg_of_le (fun w => integral_nonneg fun _ => norm_nonneg _) hle hs
  exact ⟨hf,(hf.tsum_le_tsum hle hs).trans_eq (tsum_mul_left ..)⟩

end UV
