import UV.UnboundedSourceResolution

/-! The actual common spectral cut core lies in all source domains.
Bounded reciprocal spectral integrals provide explicit preimages; no
domain inclusion is a field of the supplied spectral resolutions. -/

noncomputable section
open Set

namespace UV

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Each F cut has an actual preimage under sqrt(F). This proves its
membership in the generally unbounded inverse-square-root domain. -/
theorem sourceResolution_cut_normalizer_domain
    (F : H →L[ℂ] H) (hF : 0 ≤ F) (hFInj : Function.Injective F)
    (RF : SourceSpectralResolution (F.toLinearMap.toPMap ⊤)) (n : ℕ) (x : H) :
    RF.measure.projection (sourcePositiveSpectralCut n) x ∈
      (sourceHilbertNormalizer F hF hFInj).domain := by
  obtain ⟨u,_,hu⟩ := (F.toLinearMap.toPMap ⊤).mem_graph_iff.mp
    (sourceResolution_reciprocal_graph RF n x)
  refine ⟨(CFC.sqrt F : H →L[ℂ] H) (u : H), ?_⟩
  change ((CFC.sqrt F : H →L[ℂ] H)*(CFC.sqrt F : H →L[ℂ] H)) (u : H) = _
  rw [CFC.sqrt_mul_sqrt_self F hF]
  exact hu

theorem source_jointProjection_reverse_apply (P Q : SourcePVM H)
    (hPQ : ∀ A B, MeasurableSet A → MeasurableSet B →
      Commute (P.projection A) (Q.projection B)) (n : ℕ) (x : H) :
    sourcePVMJointProjection P Q n x =
      Q.projection (sourcePositiveSpectralCut n) (P.projection (sourcePositiveSpectralCut n) x) := by
  exact congrArg (fun A : H →L[ℂ] H => A x)
    (hPQ _ _ (sourcePositiveSpectralCut_measurable n) (sourcePositiveSpectralCut_measurable n)).eq

/-- The actual union of common cuts belongs to the kinetic domain. -/
theorem source_jointCore_kinetic_domain {K : H →ₗ.[ℂ] H}
    (P : SourcePVM H) (RK : SourceSpectralResolution K)
    (hPQ : ∀ A B, MeasurableSet A → MeasurableSet B →
      Commute (P.projection A) (RK.measure.projection B)) :
    sourcePVMJointCore P RK.measure ≤ K.domain := by
  apply iSup_le
  intro n x hx
  obtain ⟨y,rfl⟩ := hx
  change sourcePVMJointProjection P RK.measure n y ∈ K.domain
  rw [source_jointProjection_reverse_apply P RK.measure hPQ]
  exact LinearPMap.mem_domain_of_mem_graph (sourceResolution_cut_graph RK n
    (P.projection (sourcePositiveSpectralCut n) y))

/-- Bounded reciprocal cuts construct actual kinetic preimages, so the
common core belongs to the unbounded covariance domain as well. -/
theorem source_jointCore_covariance_domain {K : H →ₗ.[ℂ] H}
    (P : SourcePVM H) (RK : SourceSpectralResolution K)
    (hPQ : ∀ A B, MeasurableSet A → MeasurableSet B →
      Commute (P.projection A) (RK.measure.projection B)) :
    sourcePVMJointCore P RK.measure ≤ K.inverse.domain := by
  apply iSup_le
  intro n x hx
  obtain ⟨y,rfl⟩ := hx
  change sourcePVMJointProjection P RK.measure n y ∈ K.inverse.domain
  rw [source_jointProjection_reverse_apply P RK.measure hPQ, LinearPMap.inverse_domain]
  obtain ⟨u,_,hu⟩ := K.mem_graph_iff.mp (sourceResolution_reciprocal_graph RK n
    (P.projection (sourcePositiveSpectralCut n) y))
  exact ⟨u,hu⟩

/-- The common core lies in the true normalizer domain without a global
positive lower bound for F or an assumed common scalar representation. -/
theorem source_jointCore_normalizer_domain
    (F : H →L[ℂ] H) (hF : 0 ≤ F) (hFInj : Function.Injective F)
    (RF : SourceSpectralResolution (F.toLinearMap.toPMap ⊤)) (Q : SourcePVM H) :
    sourcePVMJointCore RF.measure Q ≤ (sourceHilbertNormalizer F hF hFInj).domain := by
  apply iSup_le
  intro n x hx
  obtain ⟨y,rfl⟩ := hx
  exact sourceResolution_cut_normalizer_domain F hF hFInj RF n
    (Q.projection (sourcePositiveSpectralCut n) y)

end UV
