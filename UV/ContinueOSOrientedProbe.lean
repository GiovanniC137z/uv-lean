import UV.ContinueOSResolvent
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! Oriented half-space tests on a locked sector-plane. The zeroth coordinate
is the signed centred GT length. Reflection fixes the three spatial axes. -/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap Topology FourierTransform

namespace UV

theorem osTimeReflect_norm (x : OSFourSpace) : ‖osTimeReflect x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i = 0
  · subst i
    simp [osTimeReflect]
  · simp [osTimeReflect, h]

def osTimeReflectionIsometry : OSFourSpace ≃ₗᵢ[ℝ] OSFourSpace where
  toFun := osTimeReflect
  invFun := osTimeReflect
  left_inv := osTimeReflect_involutive
  right_inv := osTimeReflect_involutive
  map_add' x y := by
    ext i
    by_cases h : i = 0 <;> simp [osTimeReflect, h, add_comm]
  map_smul' c x := by
    ext i
    by_cases h : i = 0 <;> simp [osTimeReflect, h]
  norm_map' := osTimeReflect_norm

def osReflectProbe (u : OSProbe) : OSProbe :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ osTimeReflectionIsometry.toContinuousLinearEquiv u

@[simp] theorem osReflectProbe_apply (u : OSProbe) (x : OSFourSpace) :
    osReflectProbe u x = u (osTimeReflect x) := rfl

theorem osReflectProbe_fourier (u : OSProbe) (k : OSFourSpace) :
    𝓕 (osReflectProbe u) k = 𝓕 u (osTimeReflect k) :=
  Real.fourierIntegral_comp_linearIsometry osTimeReflectionIsometry _ _

theorem osMassiveLocal_reflect (m : ℝ) (u : OSProbe) :
    osMassiveLocal m (osReflectProbe u) = osReflectProbe (osMassiveLocal m u) := by
  apply (SchwartzMap.fourierTransformCLE ℂ).injective
  ext k
  change 𝓕 (osMassiveLocal m (osReflectProbe u)) k = 𝓕 (osReflectProbe (osMassiveLocal m u)) k
  simp only [osMassiveLocal_fourier, osReflectProbe_fourier, osMassiveSymbol, osTimeReflect_norm]

theorem osMassiveResolvent_reflected_local {m : ℝ} (hm : 0 < m) (u : OSProbe) :
    osMassiveResolvent m (osReflectProbe (osMassiveLocal m u)) = osReflectProbe u := by
  rw [← osMassiveLocal_reflect, osMassiveResolvent_local hm]

/-- The chart takes centred coordinates to oriented coordinates on the given
copy. Reversing the sector reverses only the GT coordinate. -/
def SectorPlane.Plane.osOrientedChart {E : Type*} [Norm E] (diamond : SectorPlane.Plane E) :
    OSFourSpace ≃ₗᵢ[ℝ] OSFourSpace :=
  match diamond.s with
  | .N => LinearIsometryEquiv.refl ℝ OSFourSpace
  | .A => osTimeReflectionIsometry

theorem SectorPlane.Plane.osOrientedChart_time {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (diamond : SectorPlane.Plane E) (x : OSFourSpace) :
    (diamond.osOrientedChart x) 0 = diamond.orientedGT (x 0) := by
  cases diamond with
  | mk s b G =>
    cases s <;> simp [SectorPlane.Plane.osOrientedChart, SectorPlane.Plane.orientedGT,
      SectorPlane.sectorSign, osTimeReflectionIsometry]

theorem SectorPlane.Plane.osOrientedChart_commutes {E : Type*} [Norm E]
    (diamond : SectorPlane.Plane E) (x : OSFourSpace) :
    diamond.osOrientedChart (osTimeReflect x) = osTimeReflect (diamond.osOrientedChart x) := by
  cases diamond with | mk s b G => cases s <;> rfl

/-- An explicit positive-GT bump centred three units along the unit GT axis. -/
def osProbeCenter : OSFourSpace := 3 • (osAxis 0).val

def osPositiveBump : ContDiffBump osProbeCenter := ⟨1, 2, by norm_num, by norm_num⟩

theorem osPositiveBump_support : tsupport (osPositiveBump : OSFourSpace → ℝ) ⊆
    {x | 1 ≤ x 0} := by
  rw [osPositiveBump.tsupport_eq]
  intro x hx
  have hd : ‖x - osProbeCenter‖ ≤ 2 := hx
  have hcoord := (PiLp.norm_apply_le (x - osProbeCenter) 0).trans hd
  have h : |x 0 - 3| ≤ 2 := by
    simpa [osProbeCenter, osAxis, EuclideanSpace.single_apply, Real.norm_eq_abs] using hcoord
  change 1 ≤ x 0
  linarith [(abs_le.mp h).1]

theorem osPositiveBump_nonzero : ∃ x, 0 < osPositiveBump x :=
  ⟨osProbeCenter, by rw [osPositiveBump.one_of_mem_closedBall (Metric.mem_closedBall_self
    osPositiveBump.rIn_pos.le)]; norm_num⟩

def osBumpProbe : OSProbe :=
  (show HasCompactSupport (fun x => (osPositiveBump x : ℂ)) from
    osPositiveBump.hasCompactSupport.comp_left (g := Complex.ofReal) Complex.ofReal_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp osPositiveBump.contDiff)

@[simp] theorem osBumpProbe_apply (x : OSFourSpace) :
    osBumpProbe x = (osPositiveBump x : ℂ) := rfl

theorem osBumpProbe_support : tsupport osBumpProbe ⊆ {x | 1 ≤ x 0} := by
  have h : Function.support osBumpProbe = Function.support (osPositiveBump : OSFourSpace → ℝ) := by
    ext x
    simp [Function.mem_support]
  simpa only [tsupport, h] using osPositiveBump_support

theorem osBumpLocal_support (m : ℝ) :
    tsupport (osMassiveLocal m osBumpProbe) ⊆ {x | 1 ≤ x 0} :=
  (osMassiveLocal_tsupport m _).trans osBumpProbe_support

end UV
