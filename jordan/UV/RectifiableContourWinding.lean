import UV.RectifiableCauchyHomotopy
import UV.JordanResidueCertificate

/-! Geometric winding for Lipschitz closed curves. A polynomial curve and a
straight-line homotopy avoiding the pole are constructed from uniform
Bernstein approximation. The integer is the polynomial's exponential-lift
increment; its definition contains no contour integral. -/

/- Ported from the verified UV 4.24 development to Lean/mathlib 4.32.2;
path extension evaluations use the current generic API. -/

noncomputable section
open Set Filter Metric Complex
open scoped Topology unitInterval NNReal

namespace UV

theorem bernsteinClosedPath_c1 {a : ℂ} (n : ℕ) (γ : Path a a) :
    ContDiffOn ℝ 1 (bernsteinClosedPath n γ).extend (Icc (0 : ℝ) 1) := by
  apply ((bernsteinCurveExtension_smooth (n+1) γ.extend).of_le
    (by norm_num)).contDiffOn.congr
  intro t ht
  rw [Path.extend_apply _ ht, bernsteinClosedPath_apply]
  exact (bernsteinCurveExtension_eq_approximation (n+1) γ.extend
    (γ : C(I, ℂ)) (fun x => Path.extend_apply γ x.property) ⟨t,ht⟩).symm

def straightContourHomotopy {a : ℂ} (γ η : Path a a) :
    (γ : C(I, ℂ)).Homotopy η where
  toFun st := γ st.2 + (st.1 : ℝ) • (η st.2-γ st.2)
  continuous_toFun := by fun_prop
  map_zero_left t := by simp
  map_one_left t := by simp

theorem straightContourHomotopy_closed {a : ℂ} (γ η : Path a a) (s : I) :
    straightContourHomotopy γ η (s,0) = straightContourHomotopy γ η (s,1) := by
  change γ 0+(s:ℝ) • (η 0-γ 0) = γ 1+(s:ℝ) • (η 1-γ 1)
  simp

theorem straightContourHomotopy_dist {a : ℂ} (γ η : Path a a) (s t : I) :
    dist (straightContourHomotopy γ η (s,t)) (γ t) ≤ dist (η t) (γ t) := by
  rw [dist_eq_norm, dist_eq_norm]
  change ‖γ t+(s:ℝ) • (η t-γ t)-γ t‖ ≤ ‖η t-γ t‖
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg s.property.1]
  exact mul_le_of_le_one_left (norm_nonneg _) s.property.2

/-- Purely geometric smoothing data. Neither a contour integral nor a
residue identity occurs in these fields. -/
structure ContourWindingSmoothing {a : ℂ} (γ : Path a a) (p : ℂ) where
  degree : ℕ
  homotopy : (γ : C(I, ℂ)).Homotopy (bernsteinClosedPath degree γ)
  avoids : ∀ s t : I, homotopy (s,t) ≠ p
  closed : ∀ s : I, homotopy (s,0) = homotopy (s,1)

theorem contourWindingSmoothing_exists {a p : ℂ} (γ : Path a a)
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ p) :
    Nonempty (ContourWindingSmoothing γ p) := by
  let R : Set ℂ := range (γ : C(I, ℂ))
  have hR : IsCompact R := isCompact_range γ.continuous
  have hRU : R ⊆ {p}ᶜ := by
    rintro z ⟨t,rfl⟩
    change γ t ≠ p
    have h := havoid t t.property
    rw [Path.extend_apply γ t.property] at h
    exact h
  obtain ⟨δ,hδ,hδU⟩ := hR.exists_cthickening_subset_open
    (isOpen_compl_singleton : IsOpen ({p}ᶜ : Set ℂ)) hRU
  have hn := (Metric.tendstoUniformlyOn_iff.mp (bernsteinClosedPath_uniform γ)) δ hδ
  obtain ⟨n,hn⟩ := hn.exists
  let η := bernsteinClosedPath n γ
  let φ := straightContourHomotopy γ η
  refine ⟨⟨n,φ,?_,straightContourHomotopy_closed γ η⟩⟩
  intro s t
  have hdist : dist (η t) (γ t) < δ := by
    have h := hn t t.property
    rw [Path.extend_apply γ t.property, Path.extend_apply _ t.property] at h
    exact (dist_comm _ _).trans_lt h
  have hm := Metric.mem_cthickening_of_dist_le (φ (s,t)) (γ t) δ R
    ⟨t,rfl⟩ ((straightContourHomotopy_dist γ η s t).trans hdist.le)
  exact hδU hm

/-- The winding integer is a geometric argument increment after geometric
smoothing; the subsequent theorem proves independence of this choice. -/
def lipschitzContourWinding {a p : ℂ} (γ : Path a a)
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ p) : ℤ :=
  let S := Classical.choice (contourWindingSmoothing_exists γ havoid)
  c1ContourWinding (bernsteinClosedPath S.degree γ) (bernsteinClosedPath_c1 S.degree γ)
    (fun t ht => by
      rw [Path.extend_apply _ ht]
      have h := S.avoids 1 ⟨t,ht⟩
      change S.homotopy.toFun (1,⟨t,ht⟩) ≠ p at h
      rw [S.homotopy.map_one_left] at h
      exact h)

theorem cauchyKernel_analyticOnNhd (p : ℂ) :
    AnalyticOnNhd ℂ (fun z : ℂ => (z-p)⁻¹) ({p}ᶜ : Set ℂ) := by
  intro z hz
  exact (analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hz)

theorem lipschitzContour_cauchyKernel_of_smoothing {a p : ℂ} {K : ℝ≥0}
    (γ : Path a a) (hLip : LipschitzWith K γ.extend) (S : ContourWindingSmoothing γ p) :
    parametrizedContourIntegral (fun z : ℂ => (z-p)⁻¹) γ =
      (c1ContourWinding (bernsteinClosedPath S.degree γ) (bernsteinClosedPath_c1 S.degree γ)
        (fun t ht => by
          rw [Path.extend_apply _ ht]
          have h := S.avoids 1 ⟨t,ht⟩
          change S.homotopy.toFun (1,⟨t,ht⟩) ≠ p at h
          rw [S.homotopy.map_one_left] at h
          exact h) : ℂ)*
        (2*Real.pi*Complex.I) := by
  rw [lipschitzContour_holomorphic_homotopy hLip
    (bernsteinClosedPath_lipschitz S.degree γ hLip) isOpen_compl_singleton
    S.homotopy S.avoids S.closed (cauchyKernel_analyticOnNhd p)]
  exact parametrizedContourIntegral_cauchyKernel_winding _ (bernsteinClosedPath_c1 S.degree γ)
    (constructedContourLogLift _ _ _)

theorem lipschitzContour_cauchyKernel_winding {a p : ℂ} {K : ℝ≥0}
    (γ : Path a a) (hLip : LipschitzWith K γ.extend)
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ p) :
    parametrizedContourIntegral (fun z : ℂ => (z-p)⁻¹) γ =
      (lipschitzContourWinding γ havoid : ℂ)*(2*Real.pi*Complex.I) := by
  exact lipschitzContour_cauchyKernel_of_smoothing γ hLip
    (Classical.choice (contourWindingSmoothing_exists γ havoid))

theorem lipschitzContour_normalized_cauchyKernel_positive {a p : ℂ} {K : ℝ≥0}
    (γ : Path a a) (hLip : LipschitzWith K γ.extend)
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ p)
    (hpos : lipschitzContourWinding γ havoid = 1) :
    (2*Real.pi*Complex.I : ℂ)⁻¹ * parametrizedContourIntegral (fun z : ℂ => (z-p)⁻¹) γ = 1 := by
  rw [lipschitzContour_cauchyKernel_winding γ hLip havoid, hpos]
  rw [Int.cast_one, one_mul, inv_mul_cancel₀ (by simp [Real.pi_ne_zero])]

/-- Geometric winding agrees with the actual exponential-lift index on
smooth curves, regardless of the smoothing choice. -/
theorem lipschitzContourWinding_eq_c1 {a p : ℂ} {K : ℝ≥0}
    (γ : Path a a) (hLip : LipschitzWith K γ.extend)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc (0 : ℝ) 1))
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ p) :
    lipschitzContourWinding γ havoid = c1ContourWinding γ hγ havoid := by
  have h := (lipschitzContour_cauchyKernel_winding γ hLip havoid).symm.trans
    (parametrizedContourIntegral_cauchyKernel_winding γ hγ
      (constructedContourLogLift γ hγ havoid))
  exact_mod_cast mul_right_cancel₀ (by simp [Real.pi_ne_zero]) h

/-- The geometric index is invariant under any continuous closed-loop
homotopy avoiding the pole. The two basepoints may differ. -/
theorem lipschitzContourWinding_homotopy {a b p : ℂ} {K L : ℝ≥0}
    {γ : Path a a} {η : Path b b}
    (hLip : LipschitzWith K γ.extend) (hηLip : LipschitzWith L η.extend)
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ p)
    (hηavoid : ∀ t ∈ Icc (0 : ℝ) 1, η.extend t ≠ p)
    (φ : (γ : C(I, ℂ)).Homotopy η)
    (hφ : ∀ s t : I, φ (s,t) ≠ p)
    (hclosed : ∀ s : I, φ (s,0) = φ (s,1)) :
    lipschitzContourWinding γ havoid = lipschitzContourWinding η hηavoid := by
  have he := lipschitzContour_holomorphic_homotopy hLip hηLip
    isOpen_compl_singleton φ hφ hclosed (cauchyKernel_analyticOnNhd p)
  rw [lipschitzContour_cauchyKernel_winding γ hLip havoid,
    lipschitzContour_cauchyKernel_winding η hηLip hηavoid] at he
  exact_mod_cast mul_right_cancel₀ (by simp [Real.pi_ne_zero]) he

/-- In particular every geometrically admitted polynomial smoothing has
exactly the intrinsic index; its choice cannot affect orientation. -/
theorem lipschitzContourWinding_smoothing_independent {a p : ℂ} {K : ℝ≥0}
    (γ : Path a a) (hLip : LipschitzWith K γ.extend)
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ p)
    (S : ContourWindingSmoothing γ p) :
    lipschitzContourWinding γ havoid =
      c1ContourWinding (bernsteinClosedPath S.degree γ) (bernsteinClosedPath_c1 S.degree γ)
        (fun t ht => by
          rw [Path.extend_apply _ ht]
          have h := S.avoids 1 ⟨t,ht⟩
          change S.homotopy.toFun (1,⟨t,ht⟩) ≠ p at h
          rw [S.homotopy.map_one_left] at h
          exact h) := by
  have he := (lipschitzContour_cauchyKernel_winding γ hLip havoid).symm.trans
    (lipschitzContour_cauchyKernel_of_smoothing γ hLip S)
  exact_mod_cast mul_right_cancel₀ (by simp [Real.pi_ne_zero]) he

end UV
