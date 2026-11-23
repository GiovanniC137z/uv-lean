import UV.ContinueNormalCircleCells

/-! The periodic first-order open Dirac chain at two specified normal
endpoints. Its ordered factors are expanded by total winding, retaining
every unit polarization and the endpoint holonomy phase. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure UV.SectorPlane
open scoped Matrix.Norms.L2Operator

namespace UV

def normalCircleOpenWord {r : ℕ} (m L θ δ : ℝ) (u : Fin r → UnitVector OSFourSpace)
    (p : Fin (r+1) → OSFourSpace) (t : Fin r → ℝ) : DiracMatrix :=
  normalOrderedWord (fun i => normalCircleKernel m L θ (p i) (normalOpenIncrements δ t i) * normalOpenVertex u i)

def normalOpenWindingWord {r : ℕ} (m L θ δ : ℝ) (w : ℤ) (u : Fin r → UnitVector OSFourSpace)
    (p : Fin (r+1) → OSFourSpace) (x : Fin r → ℝ) : DiracMatrix :=
  normalAngularPhase θ (δ+(w:ℝ)) • normalOpenDiracWord normalCoverGamma5 m (L*(δ+(w:ℝ))) u p x

set_option maxHeartbeats 650000 in
theorem normal_circle_open_windings {r : ℕ} {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (θ δ : ℝ)
    (u : Fin r → UnitVector OSFourSpace) (p : Fin (r+1) → OSFourSpace) (t : Fin r → ℝ) :
    let F := fun z : ℤ × (Fin r → ℤ) => normalOpenWindingWord m L θ δ z.1 u p (fun j => L*(t j+(z.2 j:ℝ)))
    Summable (fun z => ‖F z‖) ∧ normalCircleOpenWord m L θ δ u p t = ∑' w : ℤ, ∑' h : Fin r → ℤ, F (w,h) := by
  let d := normalOpenIncrements δ t
  let A := fun (i : Fin (r+1)) (j : ℤ) => normalCircleTerm m L θ (p i) (d i) j * normalOpenVertex u i
  have hA (i) : Summable (fun j => ‖A i j‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (normal_circle_term_summable hm hL θ (p i) (d i))
    intro j
    simpa only [normal_open_vertex_norm,mul_one] using norm_mul_le (normalCircleTerm m L θ (p i) (d i) j) (normalOpenVertex u i)
  let P := fun k : Fin (r+1) → ℤ => normalOrderedWord (fun i => A i (k i))
  let e := normalWindingAllocation r
  have hP := normal_ordered_word_summable A hA
  have hS : Summable (fun z => ‖P (e z)‖) := e.summable_iff.mpr hP
  have halloc (z : ℤ × (Fin r → ℤ)) : P (e z) =
      normalOpenWindingWord m L θ δ z.1 u p (fun j => L*(t j+(z.2 j:ℝ))) := by
    rcases z with ⟨w,h⟩
    dsimp only [P,A,d,e,normalCircleTerm]
    simp only [smul_mul_assoc,normal_allocated_increments_offset,normal_ordered_word_smul,normal_allocated_phase_offset]
    rfl
  refine ⟨by simpa only [halloc] using hS,?_⟩
  refine Eq.trans (b := ∑' k, P k) ?_ ((e.tsum_eq P).symm.trans (hS.of_norm.tsum_prod.trans ?_))
  swap
  · exact tsum_congr fun w => tsum_congr fun j => halloc (w,j)
  have hj (i) : normalCircleKernel m L θ (p i) (d i)*normalOpenVertex u i = ∑' j, A i j :=
    ((normal_circle_term_summable hm hL θ (p i) (d i)).of_norm.tsum_mul_right _).symm
  change normalOrderedWord (fun i => normalCircleKernel m L θ (p i) (d i)*normalOpenVertex u i) = _
  simp_rw [hj]
  exact normal_ordered_word_tsum A hA

/-- With physical endpoints the displacement is z'−z+wL, including
coincident endpoints. An open chain has no integrated circle center. -/
theorem normal_periodic_open_integral {r : ℕ} {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (θ z z' : ℝ) (w : ℤ)
    (u : Fin r → UnitVector OSFourSpace) (p : Fin (r+1) → OSFourSpace) :
    let δ := (z'-z)/L
    L^r • (∫ t in normalUnitCell r, ∑' h : Fin r → ℤ, normalOpenWindingWord m L θ δ w u p (fun j => L*(t j+(h j:ℝ)))) =
      normalAngularPhase θ (δ+(w:ℝ)) • ∫ x, normalOpenDiracWord normalCoverGamma5 m (z'-z+(w:ℝ)*L) u p x := by
  dsimp only
  let δ := (z'-z)/L
  have hD : L*(δ+(w:ℝ)) = z'-z+(w:ℝ)*L := by dsimp [δ]; field_simp
  have hf := (normal_open_dirac_integral normalCoverGamma5 normal_cover_gamma_norm hm (L*(δ+(w:ℝ))) u p).1
  have hi : Integrable (normalOpenWindingWord m L θ δ w u p) := hf.smul (c := normalAngularPhase θ (δ+(w:ℝ)))
  refine (normal_scaled_cube_tsum_integral hL hi).trans ?_
  simp only [normalOpenWindingWord,hD,integral_smul,δ]

end UV
