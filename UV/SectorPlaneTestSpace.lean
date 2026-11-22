import UV.MassiveRunningPole
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-! Compact C² four-momentum tests with the norm given by the largest
of the uniform norms of the test and its first two real derivatives. -/

noncomputable section

namespace UV.SectorPlane

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

open Filter MeasureTheory Set
open scoped Topology BoundedContinuousFunction UV.SectorPlane

abbrev MomentumDifferential := MassiveMomentum →L[ℝ] ℂ
abbrev MomentumSecondDifferential := MassiveMomentum →L[ℝ] MomentumDifferential

-- Cache the inherited operator norms for iterated real derivatives.
scoped instance : NormedAddCommGroup MomentumDifferential := ContinuousLinearMap.toNormedAddCommGroup
scoped instance : NormedAddCommGroup MomentumSecondDifferential := ContinuousLinearMap.toNormedAddCommGroup
scoped instance : NormedAddCommGroup (MassiveMomentum →ᵇ MomentumSecondDifferential) :=
  BoundedContinuousFunction.instNormedAddCommGroup

scoped instance : NormedSpace ℂ MomentumDifferential := ContinuousLinearMap.toNormedSpace
scoped instance : NormedSpace ℂ MomentumSecondDifferential := ContinuousLinearMap.toNormedSpace
scoped instance : NormedSpace ℂ (MassiveMomentum →ᵇ MomentumDifferential) :=
  BoundedContinuousFunction.instNormedSpace
scoped instance : NormedSpace ℂ (MassiveMomentum →ᵇ MomentumSecondDifferential) :=
  BoundedContinuousFunction.instNormedSpace

abbrev MomentumTestJet := (MassiveMomentum →ᵇ ℂ) ×
  (MassiveMomentum →ᵇ MomentumDifferential) × (MassiveMomentum →ᵇ MomentumSecondDifferential)

scoped instance momentumTestJetGroup : NormedAddCommGroup MomentumTestJet := inferInstanceAs (NormedAddCommGroup (_ × _))
scoped instance momentumTestJetSpace : NormedSpace ℂ MomentumTestJet := inferInstanceAs (NormedSpace ℂ (_ × _))


scoped instance : AddCommMonoid MomentumTestJet := momentumTestJetGroup.toAddCommGroup.toAddCommMonoid
scoped instance : Module ℂ MomentumTestJet := momentumTestJetSpace.toModule

open scoped UV.SectorPlane

def supportedMomentumTests (K : TopologicalSpace.Compacts MassiveMomentum) : Submodule ℂ MomentumTestJet where
  carrier := {j | (∀ q ∉ K, j.1 q = 0) ∧
    (∀ q, HasFDerivAt (fun p => j.1 p) (j.2.1 q) q) ∧
    (∀ q, HasFDerivAt (fun p => j.2.1 p) (j.2.2 q) q)}
  zero_mem' := ⟨fun _ _ => rfl, fun q => hasFDerivAt_const 0 q, fun q => hasFDerivAt_const 0 q⟩
  add_mem' := by
    rintro x y ⟨hx, dx, ddx⟩ ⟨hy, dy, ddy⟩
    exact ⟨fun q hq => by change x.1 q + y.1 q = 0; rw [hx q hq, hy q hq, add_zero],
      fun q => (dx q).add (dy q), fun q => (ddx q).add (ddy q)⟩
  smul_mem' := by
    rintro c x ⟨hx, dx, ddx⟩
    exact ⟨fun q hq => by change c • x.1 q = 0; rw [hx q hq, smul_zero],
      fun q => (dx q).const_smul c, fun q => (ddx q).const_smul c⟩

theorem supported_momentum_tests_closed (K : TopologicalSpace.Compacts MassiveMomentum) :
    IsClosed (supportedMomentumTests K : Set MomentumTestJet) := by
  apply IsSeqClosed.isClosed
  intro j z hj hz
  have h₀ := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hz.fst_nhds
  have h₁ := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hz.snd_nhds.fst_nhds
  have h₂ := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hz.snd_nhds.snd_nhds
  refine ⟨fun q hq => ?_, ?_, ?_⟩
  · exact tendsto_nhds_unique (h₀.tendsto_at q)
      (tendsto_const_nhds.congr (fun n => ((hj n).1 q hq).symm))
  · exact hasFDerivAt_of_tendstoUniformly h₁ (fun n q => (hj n).2.1 q) (fun q => h₀.tendsto_at q)
  · exact hasFDerivAt_of_tendstoUniformly h₂ (fun n q => (hj n).2.2 q) (fun q => h₁.tendsto_at q)

instance (K : TopologicalSpace.Compacts MassiveMomentum) : CompleteSpace (supportedMomentumTests K) :=
  (supported_momentum_tests_closed K).completeSpace_coe

abbrev CompactMomentumTest (K : TopologicalSpace.Compacts MassiveMomentum) := ↥(supportedMomentumTests K)

def CompactMomentumTest.value {K : TopologicalSpace.Compacts MassiveMomentum}
    (g : CompactMomentumTest K) (q : MassiveMomentum) : ℂ := g.val.1 q

theorem CompactMomentumTest.compact_support {K : TopologicalSpace.Compacts MassiveMomentum}
    (g : CompactMomentumTest K) : HasCompactSupport g.value :=
  HasCompactSupport.intro K.isCompact g.property.1

theorem CompactMomentumTest.contDiff {K : TopologicalSpace.Compacts MassiveMomentum}
    (g : CompactMomentumTest K) : ContDiff ℝ 2 g.value := by
  have d : fderiv ℝ g.value = fun q => g.val.2.1 q := funext fun q => (g.property.2.1 q).fderiv
  have dd : fderiv ℝ (fun q => g.val.2.1 q) = fun q => g.val.2.2 q :=
    funext fun q => (g.property.2.2 q).fderiv
  apply (contDiff_succ_iff_fderiv (n := 1)).mpr
  refine ⟨fun q => (g.property.2.1 q).differentiableAt, by norm_num, ?_⟩
  rw [d]
  apply contDiff_one_iff_fderiv.mpr
  exact ⟨fun q => (g.property.2.2 q).differentiableAt, dd.symm ▸ g.val.2.2.continuous⟩

private def boundedMomentumFunction {V : Type*} [NormedAddCommGroup V]
    (g : MassiveMomentum → V) (hc : Continuous g) (hs : HasCompactSupport g) : MassiveMomentum →ᵇ V :=
  BoundedContinuousFunction.ofNormedAddCommGroup g hc
    (hc.bounded_above_of_compact_support hs).choose (hc.bounded_above_of_compact_support hs).choose_spec

/-- Every ordinary compact C² test on K has this jet, including
complex tests with independent real and imaginary parts. -/
def CompactMomentumTest.ofFunction (K : TopologicalSpace.Compacts MassiveMomentum)
    (g : MassiveMomentum → ℂ) (hg : ContDiff ℝ 2 g) (hK : ∀ q ∉ K, g q = 0) :
    CompactMomentumTest K := by
  have hs : HasCompactSupport g := HasCompactSupport.intro K.isCompact hK
  have d : ContDiff ℝ 1 (fderiv ℝ g) := (contDiff_succ_iff_fderiv (n := 1)).mp hg |>.2.2
  let f := boundedMomentumFunction g hg.continuous hs
  let df := boundedMomentumFunction (fderiv ℝ g) d.continuous (hs.fderiv ℝ)
  let ddf := boundedMomentumFunction (fderiv ℝ (fderiv ℝ g))
    (d.continuous_fderiv le_rfl) ((hs.fderiv ℝ).fderiv ℝ)
  exact ⟨(f, df, ddf), hK, fun q => (hg.differentiable (by norm_num) q).hasFDerivAt,
    fun q => (d.differentiable le_rfl q).hasFDerivAt⟩

@[simp] theorem CompactMomentumTest.ofFunction_value (K : TopologicalSpace.Compacts MassiveMomentum)
    (g : MassiveMomentum → ℂ) (hg : ContDiff ℝ 2 g) (hK : ∀ q ∉ K, g q = 0) (q : MassiveMomentum) :
    (CompactMomentumTest.ofFunction K g hg hK).value q = g q := rfl

theorem CompactMomentumTest.norm_eq {K : TopologicalSpace.Compacts MassiveMomentum} (g : CompactMomentumTest K) :
    ‖g‖ = max ‖g.val.1‖ (max ‖g.val.2.1‖ ‖g.val.2.2‖) := rfl

end UV.SectorPlane
