import UV.ContinueNormalPhotonEnvelope
import UV.ContinueNormalShellDecay

/-! Extract three observed coordinates directly from the range of the
specified linear shell readout. The fourth carrier coordinate is independent. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure UV.SectorPlane
open scoped RealInnerProductSpace

namespace UV

private theorem normal_split_surjection (F : OSFourSpace →ₗ[ℝ] Spatial) (hF : Function.Surjective F) :
    ∃ U : NormalPhotonChart, ∀ p, (U p).1 = F p := by
  obtain ⟨J,hJ⟩ := F.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hF)
  have hJ' (q : Spatial) : F (J q) = q := LinearMap.congr_fun hJ q
  let A : OSFourSpace →ₗ[ℝ] LinearMap.ker F := (LinearMap.id-J.comp F).codRestrict _ (fun p => by
    change F (p-J (F p)) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (hJ' (F p)).symm)
  let U := F.prod A
  have hU : Function.Bijective U := by
    constructor
    · intro p q he
      have he' : F p=F q := congrArg Prod.fst he
      have hk : p-J (F p)=q-J (F q) := congrArg (fun z : Spatial × LinearMap.ker F => (z.2:OSFourSpace)) he
      rw [he'] at hk
      exact sub_left_inj.mp hk
    · rintro ⟨q,k⟩
      refine ⟨J q+k.val,Prod.ext ?_ (Subtype.ext ?_)⟩
      · change F (J q+k.val)=q
        rw [map_add,hJ',show F k.val=0 from k.property,add_zero]
      · change J q+k.val-J (F (J q+k.val))=k.val
        rw [map_add,hJ',show F k.val=0 from k.property,add_zero]
        abel
  have hd := F.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hF,finrank_top,finrank_euclideanSpace_fin,finrank_euclideanSpace_fin] at hd
  let k : LinearMap.ker F ≃ₗ[ℝ] ℝ := LinearEquiv.ofFinrankEq _ _ (by rw [Module.finrank_self]; omega)
  exact ⟨((LinearEquiv.ofBijective U hU).trans ((LinearEquiv.refl ℝ Spatial).prodCongr k)).toContinuousLinearEquiv,fun _ => rfl⟩

theorem normal_rank_three_chart {ι : Type*} [Fintype ι] (T : OSFourSpace →L[ℝ] WilsonBallSpace ι)
    (hr : 3 ≤ Module.finrank ℝ (LinearMap.range T.toLinearMap)) :
    ∃ (U : NormalPhotonChart) (M : ℝ), 0 ≤ M ∧ ∀ p, ‖(U p).1‖ ≤ M*‖T p‖ := by
  let S := LinearMap.range T.toLinearMap
  let d := Module.finrank ℝ S
  let j : Fin 3 ↪ Fin d := Fin.castLEEmb hr
  let b := Module.finBasis ℝ S
  let A : S →ₗ[ℝ] (Fin 3 → ℝ) := LinearMap.pi fun i => (LinearMap.proj (j i)).comp b.equivFun.toLinearMap
  let E := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  let B : S →ₗ[ℝ] Spatial := E.toLinearEquiv.toLinearMap.comp A
  have hA : Function.Surjective A := by
    intro x
    refine ⟨b.equivFun.symm (Function.extend j x (fun _ => 0)),funext fun i => ?_⟩
    change b.equivFun (b.equivFun.symm _) (j i) = x i
    rw [b.equivFun.apply_symm_apply,j.injective.extend_apply]
  have hB : Function.Surjective B := E.surjective.comp hA
  let F := B.comp T.toLinearMap.rangeRestrict
  have hF : Function.Surjective F := hB.comp (LinearMap.range_eq_top.mp T.toLinearMap.range_rangeRestrict)
  obtain ⟨U,hU⟩ := normal_split_surjection F hF
  refine ⟨U,‖B.toContinuousLinearMap‖,norm_nonneg B.toContinuousLinearMap,fun p => ?_⟩
  rw [hU]
  exact B.toContinuousLinearMap.le_opNorm (T.toLinearMap.rangeRestrict p)

def normalPhotonForm {ι : Type*} [Fintype ι] (L : ℝ) (T : OSFourSpace →L[ℝ] WilsonBallSpace ι)
    (p : OSFourSpace) : ℂ := normalShellCharacteristic (L • T p)

theorem normal_photon_form_continuous {ι : Type*} [Fintype ι] (L : ℝ) (T : OSFourSpace →L[ℝ] WilsonBallSpace ι) :
    Continuous (normalPhotonForm L T) := by
  have hc : Continuous (fun z : OSFourSpace × WilsonBallSpace ι => Complex.exp (Complex.I*(⟪L • T z.1,z.2⟫:ℝ))) := by fun_prop
  apply continuous_iff_continuousAt.mpr
  intro p
  unfold ContinuousAt normalPhotonForm normalShellCharacteristic
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
    (Filter.Eventually.of_forall fun q => (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun q => Filter.Eventually.of_forall fun y => by simp [Complex.norm_exp,Complex.mul_re])
    (integrable_const 1)
  exact Filter.Eventually.of_forall fun y => (hc.comp (continuous_id.prodMk continuous_const)).tendsto p

theorem normal_rank_three_form_bound {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L)
    (T : OSFourSpace →L[ℝ] WilsonBallSpace ι) (hr : 3 ≤ Module.finrank ℝ (LinearMap.range T.toLinearMap)) :
    ∃ (U : NormalPhotonChart) (C : ℝ), 0 ≤ C ∧ ∀ p, ‖normalPhotonForm L T p‖ ≤ C / (1+‖(U p).1‖)^2 := by
  obtain ⟨U,M,hM,hq⟩ := normal_rank_three_chart T hr
  have hn := hr.trans (LinearMap.range T.toLinearMap).finrank_le
  rw [finrank_euclideanSpace] at hn
  obtain ⟨B,hB,hf⟩ := normal_shell_characteristic_decay ι hn
  let D := 1+M/L
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨U,B*D^2,by positivity,fun p => ?_⟩
  apply (hf (L • T p)).trans
  have hrel : 1+‖(U p).1‖ ≤ D*(1+‖L • T p‖) := by
    rw [norm_smul,Real.norm_of_nonneg hL.le]
    have he : M/L*L = M := div_mul_cancel₀ _ hL.ne'
    dsimp [D]
    nlinarith [hq p,div_nonneg hM hL.le,mul_nonneg hL.le (norm_nonneg (T p)),
      congrArg (·*‖T p‖) he]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hrel 2) hB.le
  simpa only [mul_pow,mul_assoc] using h

end UV
