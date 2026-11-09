/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/

import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Topology.Homotopy.Path

import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Tactic


/-!
# Smooth homotopy invariance for contour integrals

Ported from mathlib master 93c32949a9e7fdbe60d7861ae7e3b513fedbee3f,
Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean, to Lean 4.24.
The original Apache 2.0 copyright and authorship are retained above.

Lean 4.32.2 compatibility port: the closed-one-form theorem is now supplied
by mathlib itself. The UV-facing theorem below delegates to that original
native proof, with exactly the same hypotheses and conclusion.

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
    ∫ᶜ x in γ₁, ω x + ∫ᶜ x in φ.evalAt 1, ω x = ∫ᶜ x in γ₂, ω x + ∫ᶜ x in φ.evalAt 0, ω x :=
  φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable
    hs hφt hω hωc hdω_symm hcontdiff

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
