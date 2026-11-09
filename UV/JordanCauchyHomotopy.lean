/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/

import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Topology.Homotopy.Path

import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import UV.ContourResidue
import Mathlib.Tactic


/-!
# Smooth homotopy invariance for contour integrals

Ported from mathlib master 93c32949a9e7fdbe60d7861ae7e3b513fedbee3f,
Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean, to Lean 4.24.
The original Apache 2.0 copyright and authorship are retained above.

The integral of a closed 1-form along the boundary of a `C²` homotopy
is zero. Closed-loop homotopies therefore preserve the actual curve
integral. This is a smooth geometric theorem; it does not posit a
rectifiable Jordan-curve classification or a general residue formula.

## Implementation notes

In this file, we represent a 1-form as `ω : E → E →L[𝕜] F`, where `𝕜` is `ℝ` or `ℂ`,
not as `ω : E → E [⋀^Fin 1]→L[𝕜] F`.
A 1-form represented this way is closed
iff its Fréchet derivative `dω : E → E →L[𝕜] E →L[𝕜] F` is symmetric, `dω a x y = dω a y x`.
-/


open scoped unitInterval Interval Pointwise Topology
open AffineMap Filter Function MeasureTheory Set

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace UV

variable [NormedSpace ℝ E] [NormedSpace ℝ F] {a b c d : E}
    {γ₁ : Path a b} {γ₂ : Path c d} {s : Set (I × I)} {t : Set E}

private theorem jordan_curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable_real
    {ω : E → E →L[ℝ] F} {dω : E → E →L[ℝ] E →L[ℝ] F}
    (φ : (γ₁ : C(I, E)).Homotopy γ₂)
    (hs : s.Countable)
    (hφt : ∀ a ∈ Ioo 0 1, ∀ b ∈ Ioo 0 1, φ (a, b) ∈ t)
    (hω : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1, (a, b) ∉ s →
      HasFDerivWithinAt ω (dω <| φ (a, b)) t (φ (a, b))) (hωc : ContinuousOn ω (closure t))
    (hdω_symm : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1, (a, b) ∉ s →
      ∀ u ∈ tangentConeAt ℝ t (φ (a, b)), ∀ v ∈ tangentConeAt ℝ t (φ (a, b)),
        dω (φ (a, b)) u v = dω (φ (a, b)) v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1)) :
    ∫ᶜ x in γ₁, ω x + ∫ᶜ x in φ.evalAt 1, ω x = ∫ᶜ x in γ₂, ω x + ∫ᶜ x in φ.evalAt 0, ω x := by
  -- The overall plan of the proof is to pullback the 1-form to the unit square along the homotopy,
  -- prove that it's a closed 1-form, then apply the divergence theorem.
  -- Let `U` be the interior of the unit square
  -- Warning: throughout the proof, we sometimes have `0` or `1` in product spaces,
  -- not only in `I` or `ℝ`, so, e.g., `Icc 0 1` may refer to the unit square
  -- in `ℝ × ℝ`.
  set U : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ Ioo 0 1 with hU
  have hinterior : interior (Icc 0 1) = U := by
    rw [hU, ← interior_Icc, ← interior_prod_eq]
    simp [Prod.mk_zero_zero, Prod.mk_one_one]
  have hunique : UniqueDiffOn ℝ (Icc 0 1 : Set (ℝ × ℝ)) := by
    rw [Icc_prod_eq]
    exact uniqueDiffOn_Icc_zero_one.prod uniqueDiffOn_Icc_zero_one
  have hUopen : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hU_subset : U ⊆ Icc 0 1 := hinterior ▸ interior_subset
  have hclosure : closure U = Icc 0 1 := by
    simp [hU, closure_prod_eq, Prod.mk_zero_zero, Prod.mk_one_one]
  -- Extend the homotopy `φ` to a continuous map  `ψ : ℝ × ℝ → E`
  set ψ : ℝ × ℝ → E := fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2 with hψ
  have hψφ : ∀ a b : I, ψ (a, b) = φ (a, b) := by simp [ψ]
  have hψ_cont : Continuous ψ := by fun_prop
  have hψUt : MapsTo ψ U t := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    lift a to I using Ioo_subset_Icc_self ha
    lift b to I using Ioo_subset_Icc_self hb
    simpa [hψφ] using hφt a ha b hb
  -- Let `dψ` be its derivative.
  set dψ : ℝ × ℝ → ℝ × ℝ →L[ℝ] E := fderivWithin ℝ ψ (Icc 0 1)
  -- Let `s'` be the set `s` interpreted as a set in `ℝ × ℝ`
  set s' : Set (ℝ × ℝ) := Prod.map (↑) (↑) '' s with hs'
  have hmem_s' (x y : I) : (↑x, ↑y) ∈ s' ↔ (x, y) ∈ s := by
    rw [hs', ← Prod.map_apply, Injective.mem_set_image]
    apply Injective.prodMap <;> apply Subtype.val_injective
  have hs'c : s'.Countable := hs.image _
  have hdψ : ∀ a ∈ U, HasFDerivAt ψ (dψ a) a := by
    rintro a haU
    refine hcontdiff.differentiableOn (by decide) a (hU_subset haU)
      |>.hasFDerivWithinAt |>.hasFDerivAt ?_
    rwa [← mem_interior_iff_mem_nhds, hinterior]
  -- Let `d2ψ` be its second derivative
  set d2ψ : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ × ℝ →L[ℝ] E := fderivWithin ℝ dψ (Icc 0 1)
  have hd2ψ : ∀ a ∈ U, HasFDerivAt dψ (d2ψ a) a := by
    rintro a haU
    refine hcontdiff.fderivWithin hunique (by decide) |>.differentiableOn_one a (hU_subset haU)
      |>.hasFDerivWithinAt |>.hasFDerivAt ?_
    rwa [← mem_interior_iff_mem_nhds, hinterior]
  -- Note that `d2ψ` is symmetric
  have hd2ψ_symm : ∀ a ∈ Icc 0 1, ∀ x y, d2ψ a x y = d2ψ a y x := by
    intro a ha
    exact (hcontdiff a ha).isSymmSndFDerivWithinAt (by simp) hunique
      (by simp [hinterior, hclosure, ha]) ha
  -- Consider `η a = ω (ψ a) ∘L dψ a`.
  set η : ℝ × ℝ → ℝ × ℝ →L[ℝ] F := fun a ↦ ω (ψ a) ∘L dψ a
  -- Put `f a = η a (0, 1)`, `g a = -η a (1, 0)`.
  set f : ℝ × ℝ → F := fun a ↦ η a (0, 1)
  have hf : ∀ a ∈ Icc 0 1, f a = ω (ψ a) (derivWithin (ψ ∘ (a.1, ·)) I a.2) := by
    intro a ha
    simp only [f, η, dψ, ContinuousLinearMap.comp_apply]
    congr 1
    have : HasDerivWithinAt (a.1, ·) (0, 1) I a.2 :=
      .prodMk (hasDerivWithinAt_const ..) (hasDerivWithinAt_id ..)
    refine DifferentiableWithinAt.hasFDerivWithinAt ?_ |>.comp_hasDerivWithinAt _ this ?_
      |>.derivWithin ?_ |>.symm
    · exact hcontdiff.differentiableOn (by decide) _ ha
    · exact fun t ht ↦ ⟨⟨ha.1.1, ht.1⟩, ⟨ha.2.1, ht.2⟩⟩
    · exact uniqueDiffOn_Icc_zero_one _ ⟨ha.1.2, ha.2.2⟩
  set g : ℝ × ℝ → F := fun a ↦ -η a (1, 0)
  have hg : ∀ a ∈ Icc 0 1, g a = ω (ψ a) (-derivWithin (ψ ∘ (·, a.2)) I a.1) := by
    intro a ha
    simp only [g, η, dψ, ContinuousLinearMap.comp_apply, map_neg]
    congr 2
    have : HasDerivWithinAt (·, a.2) (1, 0) I a.1 :=
      .prodMk (hasDerivWithinAt_id ..) (hasDerivWithinAt_const ..)
    refine DifferentiableWithinAt.hasFDerivWithinAt ?_ |>.comp_hasDerivWithinAt _ this ?_
      |>.derivWithin ?_ |>.symm
    · exact hcontdiff.differentiableOn (by decide) _ ha
    · exact fun t ht ↦ ⟨⟨ht.1, ha.1.2⟩, ⟨ht.2, ha.2.2⟩⟩
    · exact uniqueDiffOn_Icc_zero_one _ ⟨ha.1.1, ha.2.1⟩
  -- Then our goal is to prove that the integral of `η`
  -- along the boundary of the unit square is zero.
  suffices (((∫ x in 0..1, g (x, 1)) - ∫ x in 0..1, g (x, 0)) +
      ∫ y in 0..1, f (1, y)) - ∫ y in 0..1, f (0, y) = 0 by
    have hfi (s : I) :
        ∫ t in 0..1, f (s, t) = ∫ᶜ x in ⟨φ.curry s, rfl, rfl⟩, ω x := by
      simp only [curveIntegral_def, curveIntegralFun_def]
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le zero_le_one]
      intro t ht
      simp [Path.extend, hf (s, t), Prod.le_def, s.2.1, s.2.2, ht.1, ht.2, Function.comp_def, hψ]
    have hf₀ : ∫ t in 0..1, f (0, t) = ∫ᶜ x in γ₁, ω x := by
      simpa [curveIntegral_def, curveIntegralFun_def, Path.extend] using hfi 0
    have hf₁ : ∫ t in 0..1, f (1, t) = curveIntegral ω γ₂ := by
      simpa [curveIntegral_def, curveIntegralFun_def, Path.extend] using hfi 1
    have hgi (t : I) : ∫ᶜ x in φ.evalAt t, ω x = -∫ s in 0..1, g (s, t) := by
      have heval : ((φ.evalAt t).extend : ℝ → E) = fun x => (φ.extend x) t := by
        funext x
        rfl
      simp only [curveIntegral_def, curveIntegralFun_def, ← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le zero_le_one]
      intro s hs
      dsimp only
      rw [Path.extend_extends (φ.evalAt t) hs]
      change (ω (φ (⟨s, hs⟩, t))) (derivWithin ((φ.evalAt t).extend : ℝ → E) I s) = _
      rw [heval]
      simp [hg (s, t), Prod.le_def, hs.1, hs.2, t.2.1, t.2.2, Function.comp_def, hψ]
    rw [← hf₀, ← hf₁, hgi, hgi]
    linear_combination (norm := {dsimp; abel}) -this
  -- Write a formula for the derivative of `η`.
  set dη : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ × ℝ →L[ℝ] F := fun a ↦
    .compL ℝ (ℝ × ℝ) E F (ω (ψ a)) ∘L d2ψ a + (dω (ψ a)).bilinearComp (dψ a) (dψ a)
  have hdη : ∀ a ∈ U \ s', HasFDerivAt η (dη a) a := by
    rintro a ⟨haU, has⟩
    refine HasFDerivWithinAt.comp_hasFDerivAt (t := t) a ?_ ?_ ?_ |>.clm_comp (hd2ψ a haU)
    · rcases a with ⟨x, y⟩
      lift x to I using Ioo_subset_Icc_self haU.1
      lift y to I using Ioo_subset_Icc_self haU.2
      apply hω
      · simpa using haU.1
      · simpa using haU.2
      · simpa [hmem_s'] using has
    · exact hdψ a haU
    · filter_upwards [hUopen.mem_nhds haU] using hψUt
  have hdη_symm : ∀ a ∈ U \ s', ∀ u v, dη a u v = dη a v u := by
    rintro ⟨a, b⟩ ⟨hU, hs'⟩ u v
    lift a to I using Ioo_subset_Icc_self hU.1
    lift b to I using Ioo_subset_Icc_self hU.2
    have hdψ_mem (u) : dψ (a, b) u ∈ tangentConeAt ℝ t (φ (a, b)) := by
      refine tangentConeAt_mono hψUt.image_subset ?_
      rw [← hψφ]
      refine (hdψ _ hU).hasFDerivWithinAt.mapsTo_tangent_cone ?_
      have htc : tangentConeAt ℝ U ((a : ℝ), (b : ℝ)) = univ := by
        calc
          _ = tangentConeAt ℝ univ ((a : ℝ), (b : ℝ)) := tangentConeAt_congr (by
            rw [nhdsWithin_eq_nhds.mpr (hUopen.mem_nhds hU), nhdsWithin_univ])
          _ = univ := tangentConeAt_univ
      simp [htc]
    have := hdω_symm a hU.1 b hU.2 (by simpa [hmem_s'] using hs') _ (hdψ_mem u) _ (hdψ_mem v)
    simp [dη, hψφ, this, hd2ψ_symm _ (hU_subset hU)]
  -- It gives formulas for the derivatives of `f` and `g`
  set f' : ℝ × ℝ → ℝ × ℝ →L[ℝ] F := fun a ↦ ContinuousLinearMap.apply ℝ F (0, 1) ∘L dη a
  have hf' : ∀ a ∈ U \ s', HasFDerivAt f (f' a) a := by
    intro a ha
    exact (ContinuousLinearMap.apply ℝ F (0, 1)).hasFDerivAt.comp a (hdη a ha)
  set g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] F := fun a ↦ -(ContinuousLinearMap.apply ℝ F (1, 0) ∘L dη a)
  have hg' : ∀ a ∈ U \ s', HasFDerivAt g (g' a) a := by
    intro a ha
    exact (ContinuousLinearMap.apply ℝ F (1, 0)).hasFDerivAt.comp a (hdη a ha) |>.neg
  -- Note that the divergence of `(f, g)` is a.e. zero.
  have hf'g' : (fun a ↦ f' a (1, 0) + g' a (0, 1)) =ᵐ[volume.restrict (Icc 0 1)] 0 := by
    rw [Icc_prod_eq, Measure.volume_eq_prod,
      Measure.restrict_congr_set (Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc).symm]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo), hs'c.ae_notMem _]
      with a hU hs
    simp [f', g', hdη_symm a ⟨hU, hs⟩ (0, 1)]
  suffices ∫ a : ℝ × ℝ in Icc 0 1, f' a (1, 0) + g' a (0, 1) = 0 by
    have hηc : ContinuousOn η (Icc 0 1) := by
      refine .clm_comp (hωc.comp hψ_cont.continuousOn ?_) ?_
      · rw [← hclosure]
        refine MapsTo.closure (fun a ha ↦ ?_) hψ_cont
        lift a to I × I using ⟨Ioo_subset_Icc_self ha.1, Ioo_subset_Icc_self ha.2⟩
        simpa [ψ] using hφt a.1 ha.1 a.2 ha.2
      · exact hcontdiff.continuousOn_fderivWithin hunique (by decide)
    have hdiv := integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le
      f g f' g' 0 1 (show (0 : ℝ × ℝ) ≤ 1 from ⟨zero_le_one, zero_le_one⟩) s' hs'c
      (show ContinuousOn f (Icc 0 1) from hηc.clm_apply continuousOn_const)
      (show ContinuousOn g (Icc 0 1) from (hηc.clm_apply continuousOn_const).neg)
      hf' hg' (by rw [integrableOn_congr_fun_ae hf'g']; exact integrableOn_zero)
    exact hdiv.symm.trans this
  simp [integral_congr_ae hf'g']

/-- The curve integral of a closed 1-form along the boundary of the image of a unit square
under a smooth map is zero. We may ignore the behavior on a countable set.

This theorem is stated in terms of a `C^2` homotopy between two paths. -/
theorem jordan_curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable
    {ω : E → E →L[𝕜] F} {dω : E → E →L[ℝ] E →L[𝕜] F}
    (φ : (γ₁ : C(I, E)).Homotopy γ₂)
    (hs : s.Countable)
    (hφt : ∀ a ∈ Ioo 0 1, ∀ b ∈ Ioo 0 1, φ (a, b) ∈ t)
    (hω : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1, (a, b) ∉ s →
      HasFDerivWithinAt ω (dω <| φ (a, b)) t (φ (a, b)))
    (hωc : ContinuousOn ω (closure t))
    (hdω_symm : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1, (a, b) ∉ s →
      ∀ u ∈ tangentConeAt ℝ t (φ (a, b)), ∀ v ∈ tangentConeAt ℝ t (φ (a, b)),
        dω (φ (a, b)) u v = dω (φ (a, b)) v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1)) :
    ∫ᶜ x in γ₁, ω x + ∫ᶜ x in φ.evalAt 1, ω x = ∫ᶜ x in γ₂, ω x + ∫ᶜ x in φ.evalAt 0, ω x := by
  simp only [← curveIntegral_restrictScalars (𝕜 := 𝕜) (𝕝 := ℝ)]
  set e := ContinuousLinearMap.restrictScalarsL 𝕜 E F ℝ ℝ
  exact jordan_curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable_real φ hs hφt
    (dω := fun x ↦ e ∘L dω x)
    (fun a ha b hb hs ↦ e.hasFDerivAt.comp_hasFDerivWithinAt _ (hω a ha b hb hs))
    (e.continuous.comp_continuousOn hωc) hdω_symm hcontdiff

/-- The curve integral of a closed 1-form along the boundary of the image of a unit square
under a smooth map is zero.

This theorem is stated in terms of a `C^2` homotopy between two paths. -/
theorem jordan_curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
    {ω : E → E →L[𝕜] F} {dω : E → E →L[ℝ] E →L[𝕜] F}
    (φ : (γ₁ : C(I, E)).Homotopy γ₂)
    (hφt : ∀ a ∈ Ioo 0 1, ∀ b ∈ Ioo 0 1, φ (a, b) ∈ t)
    (hω : ∀ x ∈ t, HasFDerivWithinAt ω (dω x) t x)
    (hωc : ContinuousOn ω (closure t))
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x, dω x u v = dω x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1)) :
    ∫ᶜ x in γ₁, ω x + ∫ᶜ x in φ.evalAt 1, ω x = ∫ᶜ x in γ₂, ω x + ∫ᶜ x in φ.evalAt 0, ω x :=
  jordan_curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable φ (s := ∅) (by simp)
    hφt (fun a ha b hb _ ↦ hω _ <| hφt a ha b hb) hωc
    (fun a ha b hb _ ↦ hdω_symm _ <| hφt a ha b hb) hcontdiff

/-- The curve integral of a closed 1-form along the boundary of the image of a unit square
under a smooth map is zero, a version stated in terms of `DiffContOnC1`.

This theorem is stated in terms of a `C^2` homotopy between two paths. -/
theorem jordan_curveIntegral_add_curveIntegral_eq_of_diffContOnCl
    {ω : E → E →L[𝕜] F} (φ : (γ₁ : C(I, E)).Homotopy γ₂)
    (hφt : ∀ a ∈ Ioo 0 1, ∀ b ∈ Ioo 0 1, φ (a, b) ∈ t)
    (hω : DiffContOnCl ℝ ω t)
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      fderivWithin ℝ ω t x u v = fderivWithin ℝ ω t x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1)) :
    ∫ᶜ x in γ₁, ω x + ∫ᶜ x in φ.evalAt 1, ω x = ∫ᶜ x in γ₂, ω x + ∫ᶜ x in φ.evalAt 0, ω x :=
  jordan_curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt φ
    hφt (fun t ht ↦ (hω.differentiableOn t ht).hasFDerivWithinAt) hω.continuousOn
    hdω_symm hcontdiff

/-- Curve integrals depend on the actual extended curve, independently of
the proof fields specifying its endpoint types. -/
theorem jordan_curveIntegral_eq_of_extend_eq
    {ω : E → E →L[𝕜] F} {γ₁ : Path a b} {γ₂ : Path c d}
    (heq : (γ₁.extend : ℝ → E) = γ₂.extend) :
    curveIntegral ω γ₁ = curveIntegral ω γ₂ := by
  simp only [curveIntegral_def, curveIntegralFun_def, heq]

/-- A genuine closed-loop smooth homotopy preserves the integral of a
closed one-form. Its two side integrals cancel by equality of their paths. -/
theorem jordan_curveIntegral_eq_of_closed_homotopy
    {ω : E → E →L[𝕜] F} {dω : E → E →L[ℝ] E →L[𝕜] F}
    (φ : (γ₁ : C(I, E)).Homotopy γ₂)
    (hφt : ∀ a ∈ Ioo 0 1, ∀ b ∈ Ioo 0 1, φ (a, b) ∈ t)
    (hω : ∀ x ∈ t, HasFDerivWithinAt ω (dω x) t x)
    (hωc : ContinuousOn ω (closure t))
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      dω x u v = dω x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ => Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1))
    (hclosed : ∀ s : I, φ (s, 0) = φ (s, 1)) :
    curveIntegral ω γ₁ = curveIntegral ω γ₂ := by
  have heval : ((φ.evalAt 1).extend : ℝ → E) = (φ.evalAt 0).extend := by
    funext s
    exact (hclosed (projIcc 0 1 zero_le_one s)).symm
  have hside := jordan_curveIntegral_eq_of_extend_eq (ω := ω) heval
  have h := jordan_curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
    φ hφt hω hωc hdω_symm hcontdiff
  rw [hside] at h
  exact add_right_cancel h

end UV
