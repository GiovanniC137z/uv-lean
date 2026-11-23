import UV.ContinueWilsonRoutedPhoton
import UV.ContinueOSOrientedProbe
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Affine dependent momenta on one Euclidean sector chart. A nonzero
chord coefficient makes the zero-transfer set Lebesgue null. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter UV.SectorPlane
open scoped Topology

namespace UV

variable {C : Type*} [Fintype C]

def wilsonRouteLinear (a : C → ℝ) : (C → OSFourSpace) →ₗ[ℝ] OSFourSpace :=
  ∑ i, a i • (LinearMap.proj i : (C → OSFourSpace) →ₗ[ℝ] OSFourSpace)

theorem wilson_route_linear_apply (a : C → ℝ) (q : C → OSFourSpace) :
    wilsonRouteLinear a q = ∑ i, a i • q i := by
  simp [wilsonRouteLinear,LinearMap.sum_apply]

def wilsonAffineTransfer (b : OSFourSpace) (a : C → ℝ) (q : C → OSFourSpace) : OSFourSpace :=
  b + wilsonRouteLinear a q

theorem wilson_affine_transfer_continuous (b : OSFourSpace) (a : C → ℝ) :
    Continuous (wilsonAffineTransfer b a) := continuous_const.add (wilsonRouteLinear a).continuous_of_finiteDimensional

theorem wilson_affine_transfer_null (b : OSFourSpace) {a : C → ℝ} (ha : ∃ j, a j ≠ 0) :
    ∀ᵐ q ∂Measure.pi (fun _ : C => (volume : Measure OSFourSpace)), wilsonAffineTransfer b a q ≠ 0 := by
  classical
  obtain ⟨j,hj⟩ := ha
  let F := wilsonRouteLinear a
  let S := (affineSpan ℝ ({-b} : Set OSFourSpace)).comap F.toAffineMap
  have hmem (q : C → OSFourSpace) : q ∈ S ↔ F q = -b := by
    exact AffineSubspace.mem_affineSpan_singleton ℝ _
  have hS : S ≠ ⊤ := by
    intro he
    have hall (q : C → OSFourSpace) : F q = -b := (hmem q).mp (he ▸ AffineSubspace.mem_top ℝ _ _)
    have hb : -b = 0 := (hall 0).symm.trans (map_zero F)
    let v := (osAxis 0).val
    have hv : v ≠ 0 := fun hz => by
      have hu : ‖v‖ = 1 := (osAxis 0).property
      simp [hz] at hu
    have h := (hall (Pi.single j v)).trans hb
    change wilsonRouteLinear a (Pi.single j v) = 0 at h
    rw [wilson_route_linear_apply,Finset.sum_eq_single j] at h
    · rw [Pi.single_eq_same] at h
      exact (smul_ne_zero hj hv) h
    · intro k _ hkj
      simp [Pi.single_eq_of_ne hkj]
    · simp
  have heq : {q | ¬ wilsonAffineTransfer b a q ≠ 0} = (S : Set (C → OSFourSpace)) := by
    ext q
    simp only [mem_setOf_eq,not_not,SetLike.mem_coe,hmem,wilsonAffineTransfer,F,add_eq_zero_iff_neg_eq]
    exact eq_comm
  rw [ae_iff,heq]
  exact addHaar_affineSubspace volume S hS

/-- Transport rotates the offset and every independent momentum together
and retains the sector's unit directions. -/
theorem SectorPlane.Plane.wilson_route_chart {E : Type*} [NormedAddCommGroup E] (diamond : Plane E)
    (b : OSFourSpace) (a : C → ℝ) (q : C → OSFourSpace) :
    diamond.osOrientedChart (wilsonAffineTransfer b a q) =
      wilsonAffineTransfer (diamond.osOrientedChart b) a (fun j => diamond.osOrientedChart (q j)) := by
  simp [wilsonAffineTransfer,wilson_route_linear_apply]

end UV
