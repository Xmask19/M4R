import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.Complex.Tietze

variable {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- def zero : E := 0 : E
-- {x : E // x ∈ Metric.closedBall 0 1 } → {x : E // x ∈ Metric.closedBall 0 1 }
theorem brouwer_fixed_point (f : (Metric.closedBall (0 : E) 1) → (Metric.closedBall 0 1)) (hf : Continuous f) : ∃ x, f x = x := by sorry

theorem restated_IoD (f : E → E)
        (hf_cont : Continuous f) (hf_inj : Function.Injective f)
        : f 0 ∈ interior (f ''(Metric.closedBall 0 1)) := by sorry


theorem IoD2 (f : E → E)
        (hf_cont : ContinuousOn f (Metric.closedBall 0 1)) (hf_inj : Set.InjOn f (Metric.closedBall 0 1))
        : f 0 ∈ interior (f ''(Metric.closedBall 0 1)) := by
    let hBn_equiv := Equiv.Set.imageOfInjOn f (Metric.closedBall 0 1) hf_inj
    have hfrestrict_cont := ContinuousOn.restrict hf_cont
    have hBn_equiv_cont : Continuous hBn_equiv := continuous_induced_rng.mpr hfrestrict_cont
    have hfinv_cont := Continuous.continuous_symm_of_equiv_compact_to_t2 hBn_equiv_cont
    have h_closed_image : IsClosed (f '' Metric.closedBall 0 1) :=
        ((isCompact_closedBall 0 1).image_of_continuousOn hf_cont).isClosed
    let hBn_inv_cmap : C(f '' Metric.closedBall 0 1, (Metric.closedBall (0 : E) 1)) :=
    ⟨hBn_equiv.symm, hfinv_cont⟩
    have hballimageclosed : IsClosed (f '' Metric.closedBall 0 1) := IsClosed.mono h_closed_image fun U a ↦ a
    have : TietzeExtension (Metric.closedBall (0 : E) 1) :=
        Set.instTietzeExtensionUnitClosedBall (𝕜 := ℝ)
    have hTietze_exists := ContinuousMap.exists_restrict_eq hballimageclosed hBn_inv_cmap
    obtain ⟨G, hG⟩ := hTietze_exists
    -- clear! h_closed_image
    have hG0 : G (f 0) = (0 : E) := by
        let fzero' : (f '' Metric.closedBall (0 : E) 1) := ⟨f 0, ⟨0, by simp, rfl⟩⟩
        have := congr($hG fzero')
        conv_lhs at this => simp [fzero']
        rw [this]
        have H : (⟨f 0, ⟨0, by simp, rfl⟩⟩ : f '' Metric.closedBall 0 1) = hBn_equiv ⟨0, by simp⟩ := by
            apply Subtype.ext
            rfl
        dsimp [hBn_inv_cmap, fzero']
        rw [H, Equiv.leftInverse_symm hBn_equiv]
    have hStability_of_zero : ∀ Gtilde : E → E,
            (Continuous Gtilde) → (∀ y ∈ (f '' (Metric.closedBall 0 1)), ‖G y - Gtilde y‖ ≤ 1 ) → ∃ y ∈ f '' (Metric.closedBall 0 1), Gtilde y = 0 := by
        intro Gtilde hGtilde hy
        let diff_fun : E → E := fun x => x - Gtilde (f x)
        have hMaps_To : Set.MapsTo diff_fun (Metric.closedBall (0 : E) 1) (Metric.closedBall (0 : E) 1) := by
            intro x hx
            dsimp [diff_fun]
            have hxeq : x = G (f x) := by
                have hfx : f x ∈ f '' (Metric.closedBall 0 1) := Set.mem_image_of_mem f hx
                rw [← G.restrict_apply_mk _ _ hfx]
                rw [hG]
                dsimp [hBn_inv_cmap]
                dsimp [hBn_equiv]
                let e := Equiv.Set.imageOfInjOn f (Metric.closedBall 0 1) hf_inj
                have h1 : e ⟨x, Metric.mem_closedBall.mpr hx⟩ = ⟨f (x : E), hfx⟩ := by
                    apply Subtype.ext
                    rfl
                have h_symm_apply : e.symm ((Equiv.Set.imageOfInjOn f (Metric.closedBall 0 1) hf_inj) ⟨x, Metric.mem_closedBall.mpr hx⟩) = ⟨x, Metric.mem_closedBall.mpr hx⟩ := e.symm_apply_apply ⟨x, Metric.mem_closedBall.mpr hx⟩
                have h2 : e.symm ⟨f x, hfx⟩ = e.symm (e ⟨x, Metric.mem_closedBall.mpr hx⟩) := by
                    rw [h1]
                have h3 : e.symm ⟨f x, hfx⟩ = x := by
                    rw [h2, h_symm_apply]
                rw [h3]
            nth_rw 1 [hxeq]
            specialize hy (f x)
            have h4 : f x ∈ f '' Metric.closedBall 0 1 := Set.mem_image_of_mem f hx
            apply hy at h4
            exact mem_closedBall_zero_iff.mpr h4
        have diff_fun_cont_on : ContinuousOn diff_fun (Metric.closedBall 0 1):= by
            exact ContinuousOn.sub (continuousOn_id' (Metric.closedBall 0 1)) (Continuous.comp_continuousOn' hGtilde hf_cont)
        have diff_fun_cont := ContinuousOn.mapsToRestrict diff_fun_cont_on hMaps_To

        have hBrouwer := brouwer_fixed_point (Set.MapsTo.restrict diff_fun (Metric.closedBall (0:E)  1) (Metric.closedBall 0 1) hMaps_To)

        have hfixed := hBrouwer diff_fun_cont

        rcases hfixed with ⟨x, hx⟩
        use f x

        constructor
        .   simp only [Set.mem_image, Metric.mem_closedBall, dist_zero_right]
            use x
            constructor

            ·
                simp_all [hBn_equiv, hBn_inv_cmap, diff_fun]
                obtain ⟨val, property⟩ := x
                exact mem_closedBall_zero_iff.mp property
            ·   rfl
        ·

            dsimp [diff_fun] at hx
            rw [Subtype.ext_iff] at hx
            simp only [Set.MapsTo.val_restrict_apply, sub_eq_self] at hx
            exact (AddOpposite.op_eq_zero_iff (Gtilde (f ↑x))).mp (congrArg AddOpposite.op hx)





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
