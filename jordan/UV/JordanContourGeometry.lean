import Schoenflies.JordanSchoenflies
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Homotopy.Basic

/-! Genuine fillings of arbitrary Jordan contours. The closed-interior chart
is supplied by the proved Jordan–Schoenflies theorem. Contraction in the model
square constructs a continuous homotopy inside the actual filled contour;
neither a simply-connected domain nor a filling is an input. -/

noncomputable section
open Set
open scoped Topology unitInterval

namespace UV

/-- The standard coordinate homeomorphism from the complex to the real plane. -/
def complexPlaneHomeomorph : ℂ ≃ₜ Schoenflies.Plane :=
  (Complex.equivRealProdCLM.toHomeomorph.trans
    (Homeomorph.finTwoArrow : (Fin 2 → ℝ) ≃ₜ ℝ × ℝ).symm).trans
    (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.symm

/-- A simple closed path is a Jordan curve, even when its given real
parameterization has no differentiability or Lipschitz regularity. -/
theorem isJordanCurve_of_simple_closedPath {a : ℂ} (γ : Path a a)
    (hinj : InjOn γ.extend (Ico (0 : ℝ) 1)) :
    Schoenflies.IsJordanCurve
      (complexPlaneHomeomorph '' (γ.extend '' Icc (0 : ℝ) 1)) := by
  refine ⟨fun t => complexPlaneHomeomorph (γ.extend t), ⟨?_,?_,?_⟩,?_⟩
  · exact (complexPlaneHomeomorph.continuous.comp γ.continuous_extend).continuousOn
  · simp only [Path.extend_zero,Path.extend_one]
  · intro s hs t ht hst
    exact hinj hs ht (complexPlaneHomeomorph.injective hst)
  · rw [image_image]

/-- The contour and its geometric bounded interior. The interior is defined
by bounded connected components of the complement, as in Schoenflies. -/
def jordanFilledRegion (C : Set ℂ) : Set ℂ :=
  complexPlaneHomeomorph ⁻¹'
    (complexPlaneHomeomorph '' C ∪ Schoenflies.inside (complexPlaneHomeomorph '' C))

theorem subset_jordanFilledRegion (C : Set ℂ) : C ⊆ jordanFilledRegion C :=
  fun _ hz => Or.inl (mem_image_of_mem complexPlaneHomeomorph hz)

/-- The actual Schoenflies square chart contracts every continuous closed
loop in the closed Jordan interior, including its boundary, inside that same
closed interior. Its endpoint is the original loop's basepoint. -/
theorem jordanFilledRegion_contour_filling (C : Set ℂ)
    (hC : Schoenflies.IsJordanCurve (complexPlaneHomeomorph '' C))
    (γ : C(I, ℂ)) (hγ : ∀ t : I, γ t ∈ jordanFilledRegion C)
    (hclosed : γ 0 = γ 1) :
    ∃ H : C(I, C(I, ℂ)),
      (∀ t : I, H 0 t = γ t) ∧
      (∀ t : I, H 1 t = γ 0) ∧
      (∀ s : I, H s 0 = H s 1) ∧
      ∀ s t : I, H s t ∈ jordanFilledRegion C := by
  obtain ⟨e⟩ := hC.homeomorph_modelCurve
  obtain ⟨u,v,huv,_⟩ := Schoenflies.exists_isHomeoOn_of_homeomorph e
  obtain ⟨F,G,hFG,_⟩ := Schoenflies.squareExtension _ u v hC huv
  have hγP (t : I) : complexPlaneHomeomorph (γ t) ∈
      complexPlaneHomeomorph '' C ∪ Schoenflies.inside (complexPlaneHomeomorph '' C) :=
    hγ t
  let f : C(I, Schoenflies.Plane) := {
    toFun := fun t => F (complexPlaneHomeomorph (γ t))
    continuous_toFun := hFG.continuousOn.comp_continuous
      (complexPlaneHomeomorph.continuous.comp γ.continuous) hγP }
  have hfsquare (t : I) : f t ∈ Schoenflies.Plane.closedSquare 0 1 :=
    hFG.mapsTo (hγP t)
  let q : C(I × I, Schoenflies.Plane) := {
    toFun := fun st => (1-(st.1 : ℝ)) • f st.2+(st.1 : ℝ) • f 0
    continuous_toFun := by fun_prop }
  have hqsquare (st : I × I) : q st ∈ Schoenflies.Plane.closedSquare 0 1 :=
    Schoenflies.Plane.convex_closedSquare 0 1 (hfsquare st.2) (hfsquare 0)
      (sub_nonneg.mpr st.1.property.2) st.1.property.1 (by ring)
  let h : C(I × I, ℂ) := {
    toFun := fun st => complexPlaneHomeomorph.symm (G (q st))
    continuous_toFun := complexPlaneHomeomorph.symm.continuous.comp
      (hFG.continuousOn_inv.comp_continuous q.continuous hqsquare) }
  let H : C(I, C(I, ℂ)) := h.curry
  have hleft (t : I) : complexPlaneHomeomorph.symm (G (f t)) = γ t := by
    change complexPlaneHomeomorph.symm (G (F (complexPlaneHomeomorph (γ t)))) = γ t
    rw [hFG.invOn.1 (hγP t),complexPlaneHomeomorph.symm_apply_apply]
  refine ⟨H,?_,?_,?_,?_⟩
  · intro t
    change complexPlaneHomeomorph.symm (G ((1-(0 : ℝ)) • f t+(0 : ℝ) • f 0)) = γ t
    simpa using hleft t
  · intro t
    change complexPlaneHomeomorph.symm (G ((1-(1 : ℝ)) • f t+(1 : ℝ) • f 0)) = γ 0
    simpa using hleft 0
  · intro s
    have hfclosed : f 0 = f 1 := by
      change F (complexPlaneHomeomorph (γ 0)) = F (complexPlaneHomeomorph (γ 1))
      rw [hclosed]
    change complexPlaneHomeomorph.symm (G ((1-(s : ℝ)) • f 0+(s : ℝ) • f 0)) =
      complexPlaneHomeomorph.symm (G ((1-(s : ℝ)) • f 1+(s : ℝ) • f 0))
    rw [hfclosed]
  · intro s t
    change complexPlaneHomeomorph (complexPlaneHomeomorph.symm (G (q (s,t)))) ∈
      complexPlaneHomeomorph '' C ∪ Schoenflies.inside (complexPlaneHomeomorph '' C)
    rw [complexPlaneHomeomorph.apply_symm_apply]
    exact hFG.mapsTo_inv (hqsquare (s,t))

/-- Every closed path in the filled Jordan region has an actual nullhomotopy
in that same region, including paths touching its boundary. -/
theorem jordanFilledRegion_path_nullhomotopy (C : Set ℂ)
    (hC : Schoenflies.IsJordanCurve (complexPlaneHomeomorph '' C))
    {a : ℂ} (γ : Path a a) (hγ : ∀ t : I, γ t ∈ jordanFilledRegion C) :
    ∃ φ : (γ : C(I, ℂ)).Homotopy (Path.refl a),
      (∀ s t : I, φ (s,t) ∈ jordanFilledRegion C) ∧
      (∀ s : I, φ (s,0) = φ (s,1)) := by
  obtain ⟨H,h0,h1,hclosed,hmem⟩ := jordanFilledRegion_contour_filling C hC
    γ.toContinuousMap hγ (γ.source.trans γ.target.symm)
  let φ : (γ : C(I, ℂ)).Homotopy (Path.refl a) := {
    toContinuousMap := H.uncurry
    map_zero_left := h0
    map_one_left := fun t => (h1 t).trans γ.source }
  exact ⟨φ,hmem,hclosed⟩

/-- In particular the Jordan boundary itself has a derived closed-loop
nullhomotopy inside its filled geometric region. -/
theorem jordanContour_path_nullhomotopy (C : Set ℂ)
    (hC : Schoenflies.IsJordanCurve (complexPlaneHomeomorph '' C))
    {a : ℂ} (γ : Path a a) (hγ : ∀ t : I, γ t ∈ C) :
    ∃ φ : (γ : C(I, ℂ)).Homotopy (Path.refl a),
      (∀ s t : I, φ (s,t) ∈ jordanFilledRegion C) ∧
      (∀ s : I, φ (s,0) = φ (s,1)) :=
  jordanFilledRegion_path_nullhomotopy C hC γ
    (fun t => subset_jordanFilledRegion C (hγ t))

end UV
