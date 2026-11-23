import UV.ContinueNormalLatticeCells

/-! Protected charged-loop estimates on any full reciprocal four-lattice.
All lattice modes participate and the normal-cover frequency is continuous. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set UV.SectorPlane
open scoped ENNReal

namespace UV

theorem normal_lattice_exponential_shifts (b : NormalReciprocalBasis) {a : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : OSFourSpace, let g := fun k : OSFourSpace => Real.exp (-a*‖k+s‖)
      Integrable g (normalLatticeMeasure b) ∧ (∫ k, g k ∂normalLatticeMeasure b) ≤ B := by
  obtain ⟨R,hR⟩ := (ZSpan.fundamentalDomain_isBounded b).exists_norm_le
  let C := Real.exp (a*R)
  let A := normalCellFactor b C
  obtain ⟨B,hB,hsh⟩ := normal_volume_exponential_shifts ha
  refine ⟨A.toReal*B,mul_nonneg ENNReal.toReal_nonneg hB,fun s => ?_⟩
  let g := fun k : OSFourSpace => Real.exp (-a*‖k+s‖)
  have hg : Measurable g := by dsimp [g]; fun_prop
  have hc (k : NormalReciprocalLattice b) (x) (hx : x ∈ ZSpan.fundamentalDomain b) :
      g k ≤ C * g ((k:OSFourSpace)+x) := by
    dsimp only [g,C]
    rw [←Real.exp_add,Real.exp_le_exp]
    have hn : ‖(k:OSFourSpace)+x+s‖ ≤ ‖(k:OSFourSpace)+s‖+R := by
      rw [add_right_comm (k:OSFourSpace) x s]
      exact (norm_add_le _ _).trans (add_le_add_left (hR x hx) _)
    linarith [mul_le_mul_of_nonneg_left hn ha.le]
  have h := normal_integral_from_cell_bound (normalLatticeMeasure b) volume hg (fun _ => (Real.exp_pos _).le)
    (hsh s).1 A (normal_cell_factor_finite b C) (normal_lattice_cell_lintegral b C _ (ENNReal.measurable_ofReal.comp hg)
    (fun k x hx => by rw [←ENNReal.ofReal_mul (Real.exp_pos _).le]; exact ENNReal.ofReal_le_ofReal (hc k x hx)))
  exact ⟨h.1,h.2.trans (mul_le_mul_of_nonneg_left (hsh s).2 ENNReal.toReal_nonneg)⟩

/-- Moving within a reciprocal cell of radius R changes the five-dimensional
massive inverse power by at most (1+R/m)^r, uniformly in ξ and the transfer. -/
theorem normal_weight_cell_comparison {m R : ℝ} (hm : 0 < m) (hR : 0 ≤ R) (p x : OSFourSpace)
    (hx : ‖x‖ ≤ R) (ξ : ℝ) (r : ℕ) :
    normalLoopWeight m (p,ξ)^r ≤ (1+R/m)^r * normalLoopWeight m (p+x,ξ)^r := by
  let d := Real.sqrt (normalFiveDenom m p ξ)
  let d' := Real.sqrt (normalFiveDenom m (p+x) ξ)
  have hD : 0 < normalFiveDenom m p ξ := by dsimp [normalFiveDenom]; positivity
  have hD' : 0 < normalFiveDenom m (p+x) ξ := by dsimp [normalFiveDenom]; positivity
  have hd : 0 < d := Real.sqrt_pos.mpr hD
  have hd' : 0 < d' := Real.sqrt_pos.mpr hD'
  have hsq : d^2 = m^2+‖p‖^2+ξ^2 := Real.sq_sqrt hD.le
  have hsq' : d'^2 = m^2+‖p+x‖^2+ξ^2 := Real.sq_sqrt hD'.le
  have hmd : m ≤ d := by nlinarith [sq_nonneg ‖p‖,sq_nonneg ξ]
  have hpd : ‖p‖ ≤ d := by nlinarith [sq_nonneg m,sq_nonneg ξ,norm_nonneg p]
  have hnx : ‖p+x‖ ≤ ‖p‖+R := (norm_add_le _ _).trans (add_le_add_left hx _)
  have hcell : d' ≤ d+R := by
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) hnx 2,mul_le_mul_of_nonneg_right hpd hR]
  have hscale : d' ≤ (1+R/m)*d := by
    have h := mul_le_mul_of_nonneg_left hmd (div_nonneg hR hm.le)
    rw [div_mul_cancel₀ _ hm.ne'] at h
    linarith
  have hInv : d⁻¹ ≤ (1+R/m)*d'⁻¹ := by
    rw [←div_eq_mul_inv,le_div_iff₀ hd',inv_mul_eq_div,div_le_iff₀ hd]
    exact hscale
  simpa only [mul_pow] using pow_le_pow_left₀ (inv_nonneg.mpr hd.le) hInv r

theorem normal_lattice_power_shifts (b : NormalReciprocalBasis) {m : ℝ} (hm : 0 < m) {r : ℕ} (hr : 5 < r) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : OSFourSpace, let g := fun t : NormalLoopFrequency => normalLoopWeight m (t.1+s,t.2)^r
      Integrable g ((normalLatticeMeasure b).prod volume) ∧ (∫ t, g t ∂(normalLatticeMeasure b).prod volume) ≤ B := by
  obtain ⟨R,hR⟩ := (ZSpan.fundamentalDomain_isBounded b).exists_norm_le
  let R' := max R 0
  have hR' : 0 ≤ R' := le_max_right _ _
  let C := (1+R'/m)^r
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let A := normalCellFactor b C
  let B := ∫ t : NormalLoopFrequency, normalLoopWeight m t^r
  have hB : 0 ≤ B := integral_nonneg fun t => pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) r
  refine ⟨A.toReal*B,mul_nonneg ENNReal.toReal_nonneg hB,fun s => ?_⟩
  let g := fun t : NormalLoopFrequency => normalLoopWeight m (t.1+s,t.2)^r
  have hg : Measurable g := by dsimp [g,normalLoopWeight,normalFiveDenom]; fun_prop
  have hn (t) : 0 ≤ g t := pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) r
  have hc (k : NormalReciprocalLattice b) (x) (hx : x ∈ ZSpan.fundamentalDomain b) (ξ : ℝ) :
      g (k,ξ) ≤ C * g ((k:OSFourSpace)+x,ξ) := by
    simpa only [g,C,add_right_comm (k:OSFourSpace) x s] using normal_weight_cell_comparison hm hR' ((k:OSFourSpace)+s) x
      ((hR x hx).trans (le_max_left _ _)) ξ r
  have h := normal_integral_from_cell_bound ((normalLatticeMeasure b).prod volume) volume hg hn
    (normal_weight_power_shift hm hr s).1 A (normal_cell_factor_finite b C)
    (normal_lattice_frequency_lintegral b C _ (ENNReal.measurable_ofReal.comp hg) (fun k x hx ξ => by
      simp only [Function.comp_apply]
      rw [←ENNReal.ofReal_mul hC]; exact ENNReal.ofReal_le_ofReal (hc k x hx ξ)))
  exact ⟨h.1,h.2.trans_eq (congrArg (A.toReal*·) (normal_weight_power_shift hm hr s).2)⟩

theorem normal_lattice_nonzero_windings (b : NormalReciprocalBasis) {n : ℕ} {m L : ℝ} (hm : 0 < m) (hL : 0 < L)
    (θ : ℝ) (u : Fin (n+1) → UnitVector OSFourSpace) (s : ℤ → Fin (n+1) → OSFourSpace) :
    let μ := (volume : Measure (Fin n → ℝ)).prod (normalLatticeMeasure b)
    let F := fun (w : ℤ) (t : (Fin n → ℝ) × OSFourSpace) => normalWindingTrace m L θ w u (fun j => t.2+s w j) t.1
    (∀ w ≠ 0, Integrable (F w) μ) ∧ Summable (fun w : ℤ => if w = 0 then 0 else ∫ t, ‖F w t‖ ∂μ) := by
  obtain ⟨B,hB,hsh⟩ := normal_lattice_exponential_shifts b (a := L/(2*((n:ℝ)+1))) (by positivity)
  have hh (w : ℤ) (hw : w ≠ 0) := normal_winding_trace_integral hm hL θ w hw u (s w) (normalLatticeMeasure b) B hsh
  refine ⟨fun w hw => (hh w hw).1,?_⟩
  apply Summable.of_nonneg_of_le (fun w => by split_ifs <;> first | exact le_rfl | exact integral_nonneg fun _ => norm_nonneg _)
    _ ((normal_winding_rate_summable hm hL).mul_left (normalWindingBudget n m L B))
  intro w
  split_ifs with hw
  · dsimp only [normalWindingBudget,normalWindingRate]; positivity
  · exact (hh w hw).2

theorem normal_lattice_zero_winding_six (b : NormalReciprocalBasis) {r : ℕ} {m L : ℝ}
    (hm : 0 < m) (hL : 0 < L) (hr : 5 < r) (u : Fin r → UnitVector OSFourSpace) :
    ∃ B : ℝ, ∀ s : Fin r → OSFourSpace,
      let F := fun t : NormalLoopFrequency => normalZeroTrace m L u (fun j => t.1+s j) t.2
      let μ := (normalLatticeMeasure b).prod volume
      Integrable F μ ∧ (∫ t, ‖F t‖ ∂μ) ≤ B := by
  obtain ⟨B,_,hB⟩ := normal_lattice_power_shifts b hm hr
  exact ⟨_,fun s => normal_zero_trace_integral hm hL hr u s _ B hB⟩

end UV
