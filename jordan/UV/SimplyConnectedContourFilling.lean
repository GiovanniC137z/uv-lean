import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Complex.Basic

/-! A standard simply-connected domain constructs an actual continuous
closed-loop filling. This proves the filling from the topological predicate;
it does not assert that every Jordan interior satisfies that predicate.
The latter Jordan/Schoenflies theorem is absent from the pinned library. -/

noncomputable section
open Set
open scoped unitInterval Topology

namespace UV

/-- Every continuous closed curve in a specified simply-connected complex
domain has a genuine continuous filling by closed curves in that domain.
No contour integral, primitive, Cauchy identity or filling is a premise. -/
theorem simplyConnected_contour_filling (U : Set ℂ) [SimplyConnectedSpace U]
    (γ : C(I, ℂ)) (hγ : ∀ t : I, γ t ∈ U) (hclosed : γ 0 = γ 1) :
    ∃ H : C(I, C(I, ℂ)),
      (∀ t : I, H 0 t = γ t) ∧
      (∀ t : I, H 1 t = γ 0) ∧
      (∀ s : I, H s 0 = H s 1) ∧
      ∀ s t : I, H s t ∈ U := by
  let a : U := ⟨γ 0, hγ 0⟩
  let p : Path a a := {
    toFun := fun t => ⟨γ t, hγ t⟩
    continuous_toFun := γ.continuous.subtype_mk _
    source' := Subtype.ext rfl
    target' := Subtype.ext hclosed.symm }
  obtain ⟨F⟩ := SimplyConnectedSpace.paths_homotopic p (Path.refl a)
  let h : C(I × I, ℂ) := {
    toFun := fun q => (F q : ℂ)
    continuous_toFun := continuous_subtype_val.comp F.continuous }
  let H : C(I, C(I, ℂ)) := h.curry
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · intro t
    exact congrArg Subtype.val (F.toHomotopy.apply_zero t)
  · intro t
    exact congrArg Subtype.val (F.toHomotopy.apply_one t)
  · intro s
    exact (congrArg Subtype.val (F.source s)).trans (congrArg Subtype.val (F.target s)).symm
  · intro s t
    exact (F (s,t)).property

/-- The same construction in the library's actual homotopy type, suitable
for contour homotopy-invariance theorems. -/
theorem simplyConnected_path_nullhomotopy (U : Set ℂ) [SimplyConnectedSpace U]
    {a : ℂ} (γ : Path a a) (hγ : ∀ t : I, γ t ∈ U) :
    ∃ φ : (γ : C(I,ℂ)).Homotopy (Path.refl a),
      (∀ s t : I, φ (s,t) ∈ U) ∧ (∀ s : I, φ (s,0) = φ (s,1)) := by
  obtain ⟨H,h0,h1,hclosed,hU⟩ := simplyConnected_contour_filling U γ.toContinuousMap hγ
    (γ.source.trans γ.target.symm)
  let φ : (γ : C(I,ℂ)).Homotopy (Path.refl a) := {
    toContinuousMap := H.uncurry
    map_zero_left := h0
    map_one_left := fun t => (h1 t).trans γ.source }
  exact ⟨φ, hU, hclosed⟩

end UV
