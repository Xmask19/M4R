import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.Complex.Tietze

variable {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]


set_option linter.unnecessarySimpa false
-- def zero : E := 0 : E
-- {x : E // x ∈ Metric.closedBall 0 1 } → {x : E // x ∈ Metric.closedBall 0 1 }
theorem brouwer_fixed_point (f : (Metric.closedBall (0 : E) 1) → (Metric.closedBall 0 1)) (hf : Continuous f) :
        ∃ x, f x = x := by sorry

theorem restated_IoD (f : E → E)
        (hf_cont : Continuous f) (hf_inj : Function.Injective f)
        : f 0 ∈ interior (f ''(Metric.closedBall 0 1)) := by sorry


theorem IoD2 (f : E → E)
        (hf_cont : ContinuousOn f (Metric.closedBall 0 1)) (hf_inj : Set.InjOn f (Metric.closedBall 0 1))
        : f 0 ∈ interior (f ''(Metric.closedBall 0 1)) := by
    let hBn_equiv := Equiv.Set.imageOfInjOn f (Metric.closedBall 0 1) hf_inj
    let hBn_inv_cmap : C(f '' Metric.closedBall 0 1, (Metric.closedBall (0 : E) 1)) :=
    ⟨hBn_equiv.symm,  Continuous.continuous_symm_of_equiv_compact_to_t2 (continuous_induced_rng.mpr <|
        ContinuousOn.restrict hf_cont)⟩
    have hballimageclosed : IsClosed (f '' Metric.closedBall 0 1) := IsClosed.mono
      ((isCompact_closedBall 0 1).image_of_continuousOn hf_cont).isClosed fun U a ↦ a
    obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq hballimageclosed hBn_inv_cmap
    -- clear! h_closed_image
    have hG0 : G (f 0) = (0 : E) := by
        let fzero' : (f '' Metric.closedBall (0 : E) 1) := ⟨f 0, ⟨0, by simp, rfl⟩⟩
        have := congr($hG fzero')
        conv_lhs at this => simp [fzero']

        have H : (⟨f 0, ⟨0, by simp, rfl⟩⟩ : f '' Metric.closedBall 0 1) = hBn_equiv ⟨0, by simp⟩ := by
            apply Subtype.ext
            rfl
        simp [this, hBn_inv_cmap, fzero', H]
    have hStability_of_zero (Gtilde : E → E)
            (hGtilde : Continuous Gtilde) (hy : ∀ y ∈ (f '' (Metric.closedBall 0 1)), ‖G y - Gtilde y‖ ≤ 1 ) : ∃ y ∈ f '' (Metric.closedBall 0 1), Gtilde y = 0 := by
        let diff_fun : E → E := fun x => x - Gtilde (f x)
        have hMaps_To : Set.MapsTo diff_fun (Metric.closedBall (0 : E) 1) (Metric.closedBall (0 : E) 1) := by
            intro x hx
            dsimp [diff_fun]
            have hxeq : x = G (f x) := by
                have hfx : f x ∈ f '' (Metric.closedBall 0 1) := Set.mem_image_of_mem f hx
                simp only [← G.restrict_apply_mk _ _ hfx, hG, ContinuousMap.coe_mk, hBn_inv_cmap, hBn_equiv]
                let e := Equiv.Set.imageOfInjOn f (Metric.closedBall 0 1) hf_inj
                have hfxeq : ⟨f (x : E), hfx⟩ = e ⟨x, Metric.mem_closedBall.mpr hx⟩ := SetCoe.ext rfl
                rw [hfxeq, (e.symm_apply_apply ⟨x, Metric.mem_closedBall.mpr hx⟩)]
            nth_rw 1 [hxeq]
            have h4 : f x ∈ f '' Metric.closedBall 0 1 := Set.mem_image_of_mem f hx
            apply hy (f x) at h4
            exact mem_closedBall_zero_iff.mpr h4
        have diff_fun_cont_on : ContinuousOn diff_fun (Metric.closedBall 0 1):=
            ContinuousOn.sub (continuousOn_id' (Metric.closedBall 0 1)) (Continuous.comp_continuousOn' hGtilde hf_cont)
        have hBrouwer := brouwer_fixed_point (Set.MapsTo.restrict diff_fun (Metric.closedBall (0:E)  1) (Metric.closedBall 0 1) hMaps_To)
        rcases hBrouwer (ContinuousOn.mapsToRestrict diff_fun_cont_on hMaps_To) with ⟨x, hx⟩
        refine ⟨f x, ⟨⟨x ,⟨(by simpa [Metric.mem_closedBall, dist_zero_right] using mem_closedBall_zero_iff.mp x.2), rfl⟩⟩, ?_⟩⟩
        · simp [diff_fun, Subtype.ext_iff] at hx
          simpa [Set.MapsTo.val_restrict_apply, sub_eq_self] using (AddOpposite.op_eq_zero_iff (Gtilde (f ↑x))).mp (congrArg AddOpposite.op hx)
    by_contra hnotinterior
    have hGconton := Continuous.continuousOn (ContinuousMap.continuous G) (s := f '' (Metric.closedBall 0 1))
    -- have h8 : IsCompact (Metric.closedBall 0 1) := by exact isCompact_closedBall 0 1
    have himgcompact := IsCompact.image_of_continuousOn (isCompact_closedBall 0 1) hf_cont
    have hGuniformcont := IsCompact.uniformContinuousOn_of_continuous himgcompact hGconton
    rw [Metric.uniformContinuousOn_iff_le] at hGuniformcont
    specialize hGuniformcont 0.1
    have h0 : 0.1 > (0 : ℝ) := by
        norm_num
    apply hGuniformcont at h0
    rcases h0 with ⟨ε , hε1, hε2⟩
    have h1 : (0:E) ∈ (Metric.closedBall 0 1) := by simp
    have h2 := Set.mem_image_of_mem f h1
    apply hε2 (f 0) at h2
    have ⟨c, hc1, hc2⟩ : ∃ c, dist c (f 0) < ε ∧ c ∉ f '' Metric.closedBall 0 1 := by
        rw [mem_interior] at hnotinterior
        push_neg at hnotinterior
        specialize hnotinterior (Metric.ball (f 0) ε)
        simp only [Metric.isOpen_ball, Metric.mem_ball, dist_self,
          forall_const] at hnotinterior
        rw [imp_not_comm] at hnotinterior
        have hnotball := hnotinterior hε1
        rw [Set.not_subset] at hnotball
        rcases hnotball with ⟨c, hc1, hc2⟩
        use c
        constructor
        ·   exact Metric.mem_ball.mp hc1
        ·   exact (Set.mem_compl_iff (f '' Metric.closedBall 0 1) c).mp hc2
    let sigma1 : Set E := {y ∈ f '' (Metric.closedBall 0 1) | ‖y - c‖ ≥ ε}
    let sigma2 : Set E := Metric.sphere c ε
    let sigma := sigma1 ∪ sigma2
    have hsigmacompact : IsCompact sigma := by
        rw [Metric.isCompact_iff_isClosed_bounded]
        constructor
        ·   apply IsClosed.union
            ·   have hsigma1eq : sigma1 = (f '' Metric.closedBall 0 1) ∩ {y | ‖y - c‖ ≥ ε } := by
                    ext x
                    constructor
                    ·   intro hx
                        exact
                          (Set.mem_inter_iff x (f '' Metric.closedBall 0 1) {y | ‖y - c‖ ≥ ε}).mpr
                            hx
                    ·   rw [Set.mem_inter_iff]
                        intro ⟨hx1, hx2⟩
                        constructor
                        ·   exact (Set.mem_image f (Metric.closedBall 0 1) x).mpr hx1
                        ·   exact le_of_eq_of_le rfl hx2
                have h2 : IsClosed {y | ‖y - c‖ ≥ ε } := by
                    have h3 : IsOpen {y | ‖y - c‖ ≥ ε }ᶜ := by
                        have h4 : {y | ‖y - c‖ ≥ ε}ᶜ = Metric.ball c ε := by
                            ext x
                            constructor
                            ·   intro hx
                                rw [Set.mem_compl_iff, Set.notMem_setOf_iff, not_le] at hx
                                exact mem_ball_iff_norm.mpr hx
                            ·   intro hx
                                simp only [ge_iff_le, Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
                                exact mem_ball_iff_norm.mp hx
                        rw [h4]
                        exact Metric.isOpen_ball
                    exact { isOpen_compl := h3 }
                exact IsClosed.and hballimageclosed h2
            ·   exact Metric.isClosed_sphere

        ·   rw [Bornology.isBounded_union]
            constructor
            ·   have himgbounded := IsCompact.isBounded himgcompact
                have hsigma1subset : sigma1 ⊆ (f '' Metric.closedBall 0 1) := by
                    exact Set.sep_subset (f '' Metric.closedBall 0 1) fun x ↦ ‖x - c‖ ≥ ε
                exact Bornology.IsBounded.subset himgbounded hsigma1subset
            ·   exact Metric.isBounded_sphere
    have hcnotinsigma : c ∉ sigma := by
        by_contra hcinsigma
        rw [Set.mem_union] at hcinsigma
        rcases hcinsigma with h1 | h2
        ·   rw [Set.mem_sep_iff] at h1
            rcases h1 with ⟨h1, h2⟩
            simp only [sub_self, norm_zero, ge_iff_le] at h2
            aesop
        ·   have h3 : c ∈ Metric.sphere c ε := Metric.mem_sphere.mpr h2
            rw [mem_sphere_iff_norm] at h3
            simp only [sub_self, norm_zero] at h3
            aesop
    let Phi : E → E := fun y => (max (ε / ‖y - c‖) (1 : ℝ)) • y
    -- have hPhiimg : Phi '' (f '' Metric.closedBall 0 1) = sigma := by
    --     ext x
    have hPhicont : ContinuousOn Phi (f '' Metric.closedBall 0 1) := by
        apply ContinuousOn.smul
        ·   rw [continuousOn_iff_continuous_restrict]
            apply Continuous.max
            ·   apply Continuous.div
                ·   exact continuous_const
                ·   apply Continuous.norm
                    apply Continuous.sub
                    ·   exact continuous_subtype_val
                    ·   exact continuous_const
                ·   intro x
                    simp only [ne_eq, norm_eq_zero]
                    by_contra hx
                    rw [sub_eq_zero] at hx
                    aesop
            ·   exact continuous_const
        ·   exact continuousOn_id' (f '' Metric.closedBall 0 1)









theorem invariance_of_domain (f : E → E)
        (hf_cont : Continuous f) (hf_inj : Function.Injective f) : IsOpenMap f := by
    intro U hU
    rw [isOpen_iff_forall_mem_open]
    rintro y ⟨x, hxU, hfx⟩
    rw [Metric.isOpen_iff] at hU
    have hclosedball: ∀ x' ∈ U, ∃ ε' > 0, Metric.closedBall x' ε' ⊆ U:= by
        intro x' hx'
        specialize hU x'
        apply hU at hx'
        rcases hx' with ⟨ε, hε, hball⟩
        refine ⟨ε/2, half_pos hε, ?_⟩
        trans Metric.ball x' ε
        ·   exact Metric.closedBall_subset_ball (div_two_lt_of_pos hε)
        ·   exact hball
    specialize hclosedball x hxU
    rcases hclosedball with ⟨ε, hε , hclosedball⟩
    let g := fun (v : E) => ε • v + x
    have hg_cont : Continuous g := ((continuous_const_smul ε).add continuous_const : Continuous g)
    have hg_inj : Function.Injective g:= by
        intro v1 v2 himeq
        dsimp [g] at himeq
        simp only [add_left_inj] at himeq
        exact (smul_right_inj (by linarith)).mp himeq
    let e := f ∘ g
    have he_cont : Continuous e := Continuous.comp hf_cont hg_cont
    have he_inj : Function.Injective e := Function.Injective.comp hf_inj hg_inj
    have h_interior : e 0 ∈ interior (e '' (Metric.closedBall 0 1)) :=
        restated_IoD e he_cont he_inj
    have h_g_eq : g '' (Metric.closedBall 0 1) = Metric.closedBall x ε := by
        unfold g
        rw [Eq.symm (Set.image_image (fun v ↦ v + x) (fun v ↦ ε • v) (Metric.closedBall 0 1)),
            Set.image_smul, smul_unitClosedBall]
        simp only [Real.norm_eq_abs, Set.image_add_right, Metric.preimage_add_right_closedBall,
          sub_neg_eq_add, zero_add]
        rw [abs_of_pos hε]
    use interior (f '' U)
    refine ⟨interior_subset, isOpen_interior, ?_⟩
    unfold e at h_interior
    rw [Set.image_comp] at h_interior
    rw [h_g_eq] at h_interior
    unfold g at h_interior
    simp only [Function.comp_apply, smul_zero, zero_add] at h_interior
    rw [hfx] at h_interior
    grw [hclosedball] at h_interior
    exact h_interior
