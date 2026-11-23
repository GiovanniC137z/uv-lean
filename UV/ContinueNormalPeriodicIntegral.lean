import UV.ContinueNormalCircleOpen
import UV.ContinueNormalZeroIdentification

/-! Absolute Fubini for the full periodic charged word at fixed carrier
momenta. Both the independent integer lifts and total winding are summed
before the normal coordinates are integrated. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set UV.SectorPlane
open scoped Matrix.Norms.L2Operator

namespace UV

theorem normal_cube_family_integral {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℤ → (Fin n → ℝ) → E) (hi : ∀ w, Integrable (f w)) (hs : Summable (fun w => ∫ x, ‖f w x‖)) :
    (∫ t in normalUnitCell n, ∑' z : ℤ × (Fin n → ℤ), f z.1 (fun j => t j+(z.2 j:ℝ))) = ∑' w, ∫ x, f w x := by
  let A := fun (z : ℤ × (Fin n → ℤ)) (t : Fin n → ℝ) => f z.1 (fun j => t j+(z.2 j:ℝ))
  have ha (z) : IntegrableOn (A z) (normalUnitCell n) :=
    ((measurePreserving_add_right volume (fun j => (z.2 j:ℝ))).integrable_comp_of_integrable (hi z.1)).integrableOn
  have hN : Summable (fun z => ∫ t in normalUnitCell n, ‖A z t‖) := by
    apply (summable_prod_of_nonneg (fun _ => integral_nonneg fun _ => norm_nonneg _)).2
    refine ⟨fun w => (normal_cube_cell_sum (hi w).norm).summable,?_⟩
    simpa only [A,fun w => (normal_cube_cell_sum (hi w).norm).tsum_eq] using hs
  have hV : Summable (fun z => ∫ t in normalUnitCell n, A z t) := hN.of_norm_bounded (fun _ => norm_integral_le_integral_norm _)
  refine (integral_tsum_of_summable_integral_norm ha hN).symm.trans (hV.tsum_prod.trans ?_)
  exact tsum_congr fun w => (normal_cube_cell_sum (hi w)).tsum_eq

theorem normal_scaled_cube_family_integral {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {L : ℝ} (hL : 0 < L) (f : ℤ → (Fin n → ℝ) → E) (hi : ∀ w, Integrable (f w)) (hs : Summable (fun w => ∫ x, ‖f w x‖)) :
    L^n • (∫ t in normalUnitCell n, ∑' z : ℤ × (Fin n → ℤ), f z.1 (fun j => L*(t j+(z.2 j:ℝ)))) = ∑' w, ∫ x, f w x := by
  let g := fun w x => f w (L • x)
  have hg (w) : Integrable (g w) := (integrable_comp_smul_iff volume (f w) hL.ne').mpr (hi w)
  have hsg : Summable (fun w => ∫ x, ‖g w x‖) := by
    have he (w) : (∫ x, ‖g w x‖) = (L^n)⁻¹ * ∫ x, ‖f w x‖ := by
      simpa only [g,Module.finrank_pi,Fintype.card_fin,smul_eq_mul] using
        Measure.integral_comp_smul_of_nonneg volume (fun x => ‖f w x‖) L (hR := hL.le)
    simpa only [he] using hs.mul_left ((L^n)⁻¹)
  change L^n • (∫ t in normalUnitCell n, ∑' z : ℤ × (Fin n → ℤ), g z.1 (fun j => t j+(z.2 j:ℝ))) = _
  have hsG : Summable (fun w => ∫ x, g w x) := hsg.of_norm_bounded (fun _ => norm_integral_le_integral_norm _)
  rw [normal_cube_family_integral g hg hsg,←hsG.tsum_const_smul]
  apply tsum_congr
  intro w
  rw [show (∫ x, g w x) = _ from Measure.integral_comp_smul_of_nonneg volume (f w) L (hR := hL.le),Module.finrank_pi,smul_smul]
  simp [hL.ne']

/-- At fixed four-momenta the complete periodic trace can be integrated
term by term even for a single insertion. -/
theorem normal_circle_trace_integral {n : ℕ} {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (θ : ℝ)
    (u : Fin (n+1) → UnitVector OSFourSpace) (p : Fin (n+1) → OSFourSpace) :
    L^n • (∫ t in normalUnitCell n, normalCircleTrace m L θ u p t) =
      ∑' w : ℤ, ∫ x, normalWindingTrace m L (-θ) w u p x := by
  let f := fun w => normalWindingTrace m L (-θ) w u p
  have hi w := normal_winding_fixed_transfer_bound hm hL (-θ) w u p
  have hs : Summable (fun w => ∫ x, ‖f w x‖) := by
    obtain ⟨hb,hg⟩ := normal_winding_majorant hm hL
    let C := L*4*(2:ℝ)^(n+1)*(4/m)^n
    apply Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) _ (hb.mul_left C)
    intro w
    apply (hi w).2.trans
    have h := hg 0 (by simpa using hL.le) w
    rw [zero_add] at h
    rw [mul_right_comm]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  have he (t) : normalCircleTrace m L θ u p t = ∑' z : ℤ × (Fin n → ℤ), f z.1 (fun j => L*(t j+(z.2 j:ℝ))) := by
    obtain ⟨h,h'⟩ := normal_circle_trace_windings hm hL θ u p t
    exact h'.trans h.of_norm.tsum_prod.symm
  simp_rw [he]
  exact normal_scaled_cube_family_integral hL f (fun w => (hi w).1) hs

/-- No winding restriction is imposed, including at equal endpoints. -/
theorem normal_circle_open_integral {r : ℕ} {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (θ z z' : ℝ)
    (hz : z ∈ Icc 0 L) (hz' : z' ∈ Icc 0 L) (u : Fin r → UnitVector OSFourSpace) (p : Fin (r+1) → OSFourSpace) :
    let δ := (z'-z)/L
    L^r • (∫ t in normalUnitCell r, normalCircleOpenWord m L θ δ u p t) =
      ∑' w : ℤ, normalAngularPhase θ (δ+(w:ℝ)) • ∫ x, normalOpenDiracWord normalCoverGamma5 m (z'-z+(w:ℝ)*L) u p x := by
  let δ := (z'-z)/L
  let f := fun w => normalOpenWindingWord m L θ δ w u p
  have hD (w : ℤ) : L*(δ+(w:ℝ)) = z'-z+(w:ℝ)*L := by dsimp [δ]; field_simp
  have hi (w) : Integrable (f w) :=
    (normal_open_dirac_integral normalCoverGamma5 normal_cover_gamma_norm hm _ u p).1.smul (c := normalAngularPhase θ (δ+(w:ℝ)))
  have hnorm (w x) : ‖f w x‖ = ‖normalOpenDiracWord normalCoverGamma5 m (z'-z+(w:ℝ)*L) u p x‖ := by
    simp only [f,normalOpenWindingWord,norm_smul,normal_angular_phase_norm,one_mul,hD]
  have hs : Summable (fun w => ∫ x, ‖f w x‖) := by
    simp_rw [hnorm]
    exact (normal_open_all_windings normalCoverGamma5 normal_cover_gamma_norm hm hL z z' hz hz' u (fun _ => p)).1
  have he (t) : normalCircleOpenWord m L θ δ u p t = ∑' z : ℤ × (Fin r → ℤ), f z.1 (fun j => L*(t j+(z.2 j:ℝ))) := by
    obtain ⟨h,h'⟩ := normal_circle_open_windings hm hL θ δ u p t
    exact h'.trans h.of_norm.tsum_prod.symm
  change L^r • (∫ t in normalUnitCell r, normalCircleOpenWord m L θ δ u p t) = _
  simp_rw [he]
  rw [normal_scaled_cube_family_integral hL f hi hs]
  exact tsum_congr fun w => by simp only [f,normalOpenWindingWord,hD,integral_smul,δ]

end UV
