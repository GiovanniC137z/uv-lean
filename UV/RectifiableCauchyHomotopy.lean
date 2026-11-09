import UV.JordanHolomorphicHomotopy
import UV.BernsteinContourBoundary
import UV.RectifiableContourConvergence

/-! Actual Cauchy invariance for Lipschitz curves with continuous geometric
homotopies. Polynomial homotopies stay inside the original open domain,
and their boundary integrals converge by the proved common-Lipschitz
contour limit. A filling is geometric data, never an integral identity. -/

noncomputable section
open Set Filter Metric Complex
open scoped Topology unitInterval NNReal

namespace UV

def bernsteinClosedPath {a : ℂ} (n : ℕ) (γ : Path a a) : Path a a where
  toContinuousMap := bernsteinApproximation (n+1) (γ : C(I, ℂ))
  source' := by
    change bernsteinApproximation (n+1) (γ : C(I, ℂ)) 0 = a
    rw [bernsteinApproximation.apply_zero]
    exact γ.source
  target' := by
    change bernsteinApproximation (n+1) (γ : C(I, ℂ)) 1 = a
    rw [bernsteinApproximation.apply_one (show n+1 ≠ 0 by omega)]
    exact γ.target

@[simp] theorem bernsteinClosedPath_apply {a : ℂ} (n : ℕ) (γ : Path a a) (t : I) :
    bernsteinClosedPath n γ t = bernsteinApproximation (n+1) (γ : C(I, ℂ)) t := rfl

theorem bernsteinClosedPath_lipschitz {a : ℂ} {K : ℝ≥0}
    (n : ℕ) (γ : Path a a) (hLip : LipschitzWith K γ.extend) :
    LipschitzWith K (bernsteinClosedPath n γ).extend := by
  have h := bernsteinCurveExtension_lipschitzOnWith hLip.lipschitzOnWith n
  have he : (bernsteinClosedPath n γ).extend =
      IccExtend zero_le_one (fun t : I => bernsteinCurveExtension (n+1) γ.extend t) := by
    funext t
    change IccExtend zero_le_one (bernsteinClosedPath n γ) t = _
    congr 2
    funext x
    exact (bernsteinCurveExtension_eq_approximation (n+1) γ.extend
      (γ : C(I, ℂ)) (fun x => Path.extend_extends γ x.property) x).symm
  rw [he]
  exact lipschitz_IccExtend zero_le_one h

theorem bernsteinClosedPath_uniform {a : ℂ} (γ : Path a a) :
    TendstoUniformlyOn (fun n t => (bernsteinClosedPath n γ).extend t)
      γ.extend atTop (Icc (0 : ℝ) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have h := ((tendsto_iff_dist_tendsto_zero
    (f := fun n : ℕ => bernsteinApproximation (n+1) (γ : C(I, ℂ)))
    (a := (γ : C(I, ℂ)))).mp
    ((bernsteinApproximation_uniform (γ : C(I, ℂ))).comp (tendsto_add_atTop_nat 1))).eventually
      (Iio_mem_nhds hε)
  filter_upwards [h] with n hn t ht
  rw [Path.extend_extends _ ht, Path.extend_extends _ ht]
  exact (ContinuousMap.dist_apply_le_dist (f := (γ : C(I, ℂ)))
    (g := bernsteinApproximation (n+1) (γ : C(I, ℂ))) ⟨t,ht⟩).trans_lt
      (by simpa only [dist_comm] using hn)

def bernsteinLoopHomotopy {a b : ℂ} {γ : Path a a} {η : Path b b}
    (φ : (γ : C(I, ℂ)).Homotopy η) (n : ℕ) :
    ((bernsteinClosedPath n γ : Path a a) : C(I, ℂ)).Homotopy (bernsteinClosedPath n η) where
  toContinuousMap := (bernsteinTensor (n+1) (n+1) φ.curry).uncurry
  map_zero_left t := by
    change bernsteinTensor (n+1) (n+1) φ.curry 0 t = _
    rw [bernsteinTensor_start, ContinuousMap.Homotopy.curry_zero]
    rfl
  map_one_left t := by
    change bernsteinTensor (n+1) (n+1) φ.curry 1 t = _
    rw [bernsteinTensor_end (show n+1 ≠ 0 by omega), ContinuousMap.Homotopy.curry_one]
    rfl

theorem bernsteinLoopHomotopy_contDiff {a b : ℂ} {γ : Path a a} {η : Path b b}
    (φ : (γ : C(I, ℂ)).Homotopy η) (n : ℕ) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ => IccExtend zero_le_one
      ((bernsteinLoopHomotopy φ n).extend p.1) p.2) (Icc 0 1) := by
  apply ((bernsteinTensorExtension_contDiff (n+1) (n+1) φ.curry).of_le
    (by norm_num : (2 : WithTop ℕ∞) ≤ ⊤)).contDiffOn.congr
  intro p hp
  rw [ContinuousMap.Homotopy.extend_of_mem_I _ ⟨hp.1.1,hp.2.1⟩,
    IccExtend_of_mem zero_le_one _ ⟨hp.1.2,hp.2.2⟩]
  exact (bernsteinTensorExtension_eq (n+1) (n+1) φ.curry
    ⟨p.1,⟨hp.1.1,hp.2.1⟩⟩ ⟨p.2,⟨hp.1.2,hp.2.2⟩⟩).symm

/-- Holomorphic Cauchy invariance for Lipschitz loops and an arbitrary
continuous geometric homotopy in the original open analytic domain. No
differentiability or contour-integral identity is required of the homotopy. -/
theorem lipschitzContour_holomorphic_homotopy
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]
    [FiniteDimensional ℂ Z]
    {a b : ℂ} {γ : Path a a} {η : Path b b} {K L : ℝ≥0} {U : Set ℂ} {f : ℂ → Z}
    (hLip : LipschitzWith K γ.extend) (hηLip : LipschitzWith L η.extend) (hU : IsOpen U)
    (φ : (γ : C(I, ℂ)).Homotopy η)
    (hφ : ∀ s t : I, φ (s,t) ∈ U)
    (hclosed : ∀ s : I, φ (s,0) = φ (s,1))
    (hf : AnalyticOnNhd ℂ f U) :
    parametrizedContourIntegral f γ = parametrizedContourIntegral f η := by
  let R : Set ℂ := range φ.curry.uncurry
  have hR : IsCompact R := isCompact_range φ.curry.uncurry.continuous
  have hRU : R ⊆ U := by rintro z ⟨⟨s,t⟩,rfl⟩; exact hφ s t
  obtain ⟨δ,hδ,hδU⟩ := hR.exists_cthickening_subset_open hU hRU
  let V := thickening δ R
  let S := cthickening δ R
  have hRV : R ⊆ V := self_subset_thickening hδ R
  have hVS : V ⊆ S := thickening_subset_cthickening δ R
  have hclosure : closure V ⊆ U :=
    (closure_thickening_subset_cthickening δ R).trans hδU
  have hV : IsOpen V := isOpen_thickening
  have hφV : ∀ s t : I, φ.curry s t ∈ V :=
    fun s t => hRV ⟨(s,t),rfl⟩
  have hnV := bernsteinTensorExtension_eventually_mem φ.curry hV hφV
  have hneq : ∀ᶠ n : ℕ in atTop,
      parametrizedContourIntegral f (bernsteinClosedPath n γ) =
        parametrizedContourIntegral f (bernsteinClosedPath n η) := by
    filter_upwards [hnV] with n hn
    apply parametrizedContourIntegral_holomorphic_homotopy
      (bernsteinLoopHomotopy φ n) (U := V)
    · intro s hs t ht
      change bernsteinTensor (n+1) (n+1) φ.curry s t ∈ V
      rw [← bernsteinTensorExtension_eq]
      exact hn s t
    · exact hf.mono hclosure
    · exact bernsteinLoopHomotopy_contDiff φ n
    · intro s
      exact bernsteinTensor_closed (show n+1 ≠ 0 by omega) φ.curry hclosed s
  have hnS : ∀ᶠ n : ℕ in atTop,
      MapsTo (bernsteinClosedPath n γ).extend (Icc (0 : ℝ) 1) S := by
    filter_upwards [hnV] with n hn t ht
    rw [Path.extend_extends _ ht]
    apply hVS
    have hz := hn 0 ⟨t,ht⟩
    rw [bernsteinTensorExtension_eq, bernsteinTensor_start,
      ContinuousMap.Homotopy.curry_zero] at hz
    exact hz
  have hγS : MapsTo γ.extend (Icc (0 : ℝ) 1) S := by
    intro t ht
    apply hVS
    rw [Path.extend_extends _ ht]
    exact hRV ⟨(0,⟨t,ht⟩),φ.apply_zero _⟩
  have hηnS : ∀ᶠ n : ℕ in atTop,
      MapsTo (bernsteinClosedPath n η).extend (Icc (0 : ℝ) 1) S := by
    filter_upwards [hnV] with n hn t ht
    rw [Path.extend_extends _ ht]
    apply hVS
    have hz := hn 1 ⟨t,ht⟩
    rw [bernsteinTensorExtension_eq, bernsteinTensor_end (show n+1 ≠ 0 by omega),
      ContinuousMap.Homotopy.curry_one] at hz
    exact hz
  have hηS : MapsTo η.extend (Icc (0 : ℝ) 1) S := by
    intro t ht
    apply hVS
    rw [Path.extend_extends _ ht]
    exact hRV ⟨(1,⟨t,ht⟩),φ.apply_one _⟩
  have hlim := lipschitzContourIntegral_uniform_limit
    (fun n => bernsteinClosedPath n γ) γ
    (fun n => bernsteinClosedPath_lipschitz n γ hLip) hLip
    (bernsteinClosedPath_uniform γ) hR.cthickening hnS hγS
    (hf.continuousOn.mono hδU)
  have hηlim := lipschitzContourIntegral_uniform_limit
    (fun n => bernsteinClosedPath n η) η
    (fun n => bernsteinClosedPath_lipschitz n η hηLip) hηLip
    (bernsteinClosedPath_uniform η) hR.cthickening hηnS hηS
    (hf.continuousOn.mono hδU)
  exact tendsto_nhds_unique hlim (hηlim.congr' (hneq.mono (fun _ h => h.symm)))

/-- A continuous geometric filling suffices for Cauchy's theorem along
the actual Lipschitz representative, with no smoothness assumption. -/
theorem lipschitzContour_holomorphic_nullhomotopy
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]
    [FiniteDimensional ℂ Z]
    {a b : ℂ} {γ : Path a a} {K : ℝ≥0} {U : Set ℂ} {f : ℂ → Z}
    (hLip : LipschitzWith K γ.extend) (hU : IsOpen U)
    (φ : (γ : C(I, ℂ)).Homotopy (Path.refl b))
    (hφ : ∀ s t : I, φ (s,t) ∈ U)
    (hclosed : ∀ s : I, φ (s,0) = φ (s,1))
    (hf : AnalyticOnNhd ℂ f U) :
    parametrizedContourIntegral f γ = 0 := by
  have hconst : LipschitzWith 0 (Path.refl b).extend := by
    rw [Path.refl_extend]
    exact LipschitzWith.const b
  rw [lipschitzContour_holomorphic_homotopy hLip hconst hU φ hφ hclosed hf]
  exact curveIntegral_refl _ _

end UV
