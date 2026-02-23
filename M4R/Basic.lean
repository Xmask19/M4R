import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.Complex.Tietze
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.NNReal.Defs

variable {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
open NNReal

-- theorem stoneweierstrass {X : Type u_1} [TopologicalSpace X] [CompactSpace X] (A : Subalgebra E C(X, E)) (w : A.SeparatesPoints) (f : C(X, ℝ)) (ε : ℝ) (pos : 0 < ε) :
--         ∃ (g : ↥A), ‖↑g - f‖ < ε := by sorry


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
    -- let d : ℕ := Set.finrank ℝ E

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
        have H : (⟨f 0, ⟨0, by simp, rfl⟩⟩ : f '' Metric.closedBall 0 1) = hBn_equiv ⟨0, by simp⟩ := Subtype.ext rfl
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
        simp [diff_fun, Subtype.ext_iff] at hx
        simpa [Set.MapsTo.val_restrict_apply, sub_eq_self] using (AddOpposite.op_eq_zero_iff (Gtilde (f ↑x))).mp (congrArg AddOpposite.op hx)

    let ι := Module.Basis.ofVectorSpaceIndex ℝ E
    let d : ℝ := Fintype.card ι

    by_cases hdim_zero : d = 0
    ·   sorry
    ·   by_contra hnotinterior
        have hGconton := Continuous.continuousOn (ContinuousMap.continuous G) (s := f '' (Metric.closedBall 0 1))
        -- have h8 : IsCompact (Metric.closedBall 0 1) := by exact isCompact_closedBall 0 1
        have himgcompact := IsCompact.image_of_continuousOn (isCompact_closedBall 0 1) hf_cont
        have hGuniformcont := IsCompact.uniformContinuousOn_of_continuous himgcompact hGconton
        rw [Metric.uniformContinuousOn_iff_le] at hGuniformcont
        specialize hGuniformcont 0.1
        have h0 : 0.1 > (0 : ℝ) := by norm_num
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
            forall_const, imp_not_comm] at hnotinterior
            have hnotball := hnotinterior hε1
            rw [Set.not_subset] at hnotball
            rcases hnotball with ⟨c, hc1, hc2⟩
            exact ⟨c, ⟨Metric.mem_ball.mp hc1, (Set.mem_compl_iff (f '' Metric.closedBall 0 1) c).mp hc2⟩⟩
        let sigma1 : Set E := {y ∈ f '' (Metric.closedBall 0 1) | ‖y - c‖ ≥ ε}
        let sigma2 : Set E := Metric.sphere c ε
        let sigma := sigma1 ∪ sigma2
        -- change this proof to show that sigma1 and sigma2 are each compact as you use compactness of sigma1 later
        have hsigma1compact : IsCompact sigma1 := by
            rw [Metric.isCompact_iff_isClosed_bounded]
            refine ⟨?_, Bornology.IsBounded.subset (IsCompact.isBounded himgcompact) (Set.sep_subset (f '' Metric.closedBall 0 1) fun x ↦ ‖x - c‖ ≥ ε)⟩
            have hsigma1eq : sigma1 = (f '' Metric.closedBall 0 1) ∩ {y | ‖y - c‖ ≥ ε } := by
                ext x
                exact ⟨fun hx ↦
                        (Set.mem_inter_iff x (f '' Metric.closedBall 0 1) {y | ‖y - c‖ ≥ ε}).mpr
                        hx, fun ⟨hx1, hx2⟩ ↦ ⟨(Set.mem_image f (Metric.closedBall 0 1) x).mpr hx1, le_of_eq_of_le rfl hx2⟩⟩
            have h4 : {y | ‖y - c‖ ≥ ε}ᶜ = Metric.ball c ε := by
                        ext x
                        constructor
                        ·   intro hx
                            rw [Set.mem_compl_iff, Set.notMem_setOf_iff, not_le] at hx
                            exact mem_ball_iff_norm.mpr hx
                        ·   intro hx
                            simp only [ge_iff_le, Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
                            exact mem_ball_iff_norm.mp hx
            have h3 : IsOpen {y | ‖y - c‖ ≥ ε }ᶜ := by
                    rw [h4]
                    exact Metric.isOpen_ball
            exact IsClosed.and hballimageclosed ({ isOpen_compl := h3 })
        have hsigmacompact : IsCompact sigma := by
            apply IsCompact.union hsigma1compact
            rw [Metric.isCompact_iff_isClosed_bounded]
            exact ⟨ Metric.isClosed_sphere, Metric.isBounded_sphere⟩
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
            apply ContinuousOn.smul ?_ (continuousOn_id' (f '' Metric.closedBall 0 1))
            rw [continuousOn_iff_continuous_restrict]
            apply Continuous.max ((Continuous.div continuous_const (Continuous.norm (Continuous.sub continuous_subtype_val continuous_const))) ?_) continuous_const
            intro x
            simp only [ne_eq, norm_eq_zero]
            by_contra hx
            rw [sub_eq_zero] at hx
            aesop
        have hGavoids : ∀ y ∈ sigma1, G y ≠ (0 : E) := by
            intro y hy
            by_contra hGeq
            -- have hGinjective : Function.Injective ((f '' Metric.closedBall 0 1).restrict G)  := by
            have hG_inj_on_image : Set.InjOn G (f '' Metric.closedBall 0 1) := by
                intro x hx y hy h
                have hx_eq : G x = hBn_inv_cmap ⟨x, hx⟩ := by
                    rw [← ContinuousMap.restrict_apply G (f '' Metric.closedBall 0 1) ⟨x, hx⟩, hG]
                have hy_eq : G y = hBn_inv_cmap ⟨y, hy⟩ := by
                    rw [← ContinuousMap.restrict_apply G (f '' Metric.closedBall 0 1) ⟨y, hy⟩, hG]
                rw [hx_eq, hy_eq] at h
                exact congr_arg Subtype.val (hBn_equiv.symm.injective h)
            have hyeq : y = f 0 := by
                have heq : G y = G (f 0) := SetCoe.ext (Eq.trans hGeq hG0.symm)
                apply hG_inj_on_image ((Set.mem_image f (Metric.closedBall 0 1) y).mpr hy.1) (Set.mem_image_of_mem f h1) at heq
                assumption
            rw [Set.mem_sep_iff, hyeq] at hy
            rw [dist_eq_norm, ← norm_neg, neg_sub] at hc1
            linarith
        let normG : E → ℝ := fun y => ‖(G y : E)‖
        -- have hgnormconton : ContinuousOn normG (f '' Metric.closedBall 0 1) := ContinuousOn.norm (continuous_subtype_val.comp_continuousOn hGconton)
        have hgnormconton1 : ContinuousOn normG sigma1 := ContinuousOn.norm (continuous_subtype_val.comp_continuousOn (ContinuousOn.mono hGconton (Set.sep_subset (f '' Metric.closedBall 0 1) fun x ↦ ‖x - c‖ ≥ ε)))
        have hδ : ∃ (δ : ℝ), 0 < δ ∧ δ < 0.1 ∧ ∀ y ∈ sigma1, δ ≤ ‖(G y : E)‖ := by
            by_cases hP : sigma1.Nonempty
            ·   have ⟨z, hz, hmin⟩ := IsCompact.exists_isMinOn hsigma1compact hP hgnormconton1
                let δ := min (normG z) (0.05)
                have hδ_pos : 0 < δ := lt_min_iff.mpr ⟨norm_pos_iff.mpr (hGavoids z hz), by norm_num⟩
                have hδ_lt_0_1 : δ < 0.1 := by
                    calc δ ≤ 0.05 := min_le_right (normG z) 5e-2
                    _ < 0.1 := by norm_num
                have hδ_lower : ∀ y ∈ sigma1, normG y ≥ δ := by
                    intro y hy
                    calc normG y ≥ normG z := hmin hy
                        _ ≥ δ := min_le_left _ _
                use δ
            ·   exact ⟨0.05, ⟨by norm_num, ⟨by norm_num, fun y hy ↦ False.elim (hP ⟨y, hy⟩)⟩⟩⟩

        let l := (Module.Basis.ofVectorSpace ℝ E).equivFun.toContinuousLinearEquiv
        let coord_E (i : ι) : C(E, ℝ) :=
            { toFun := fun y => l y i,
                continuous_toFun := (continuous_apply i).comp l.continuous }
        let generator_E : Set C(E, ℝ) := Set.range coord_E
        let A_E : Subalgebra ℝ C(E, ℝ) := Algebra.adjoin ℝ generator_E
        let coord_sigma1 (i : ι) : C(sigma1, ℝ) :=
            { toFun := fun sigma1 => l (sigma1) i,
                continuous_toFun := by
                apply (continuous_apply i).comp
                exact l.continuous.comp continuous_subtype_val }
        let generator_sigma1 : Set C(sigma1, ℝ) := Set.range coord_sigma1
        let A_sigma1 : Subalgebra ℝ C(sigma1, ℝ) := Algebra.adjoin ℝ generator_sigma1
        have sep_sigma1 : A_sigma1.SeparatesPoints := by
            intro x y hxy
            let inc : sigma1 → E := Subtype.val
            have hxyneq: inc x ≠  inc y := Subtype.coe_ne_coe.mpr hxy
            have : l (inc x) ≠ l (inc y) := (ContinuousLinearEquiv.injective l).ne hxyneq
            obtain ⟨i, hi⟩ := Function.ne_iff.mp this
            use coord_sigma1 i
            constructor
            ·   apply Set.mem_image_of_mem
                exact (Algebra.subset_adjoin (Set.mem_range_self i))
            ·   simpa using hi

        let incl : C(Metric.closedBall (0 : E) 1, E) := ⟨Subtype.val, continuous_subtype_val⟩
        let G_rest : C(sigma1, E) := incl.comp (G.restrict sigma1)

        let G_i (i : ι) : C(sigma1, ℝ) :=
            { toFun := fun y => (l (G_rest y)) i,
                continuous_toFun := by
                apply (continuous_apply i).comp (l.continuous.comp G_rest.continuous) }
        haveI : CompactSpace sigma1 := isCompact_iff_compactSpace.mp hsigma1compact

        let norm_l := ‖(l : E →L[ℝ] (ι → ℝ))‖
        let norm_l_symm := ‖(l.symm : (ι → ℝ) →L[ℝ] E)‖
        let C := (max norm_l norm_l_symm) + 1
        have hC : 0 < C := by positivity
        rcases hδ with ⟨δ, hδ1, hδ2⟩
        let ε' := δ / (C * d)
        have hd : 0 ≤ d := Nat.cast_nonneg' (Fintype.card ↑ι)
        have hε' : 0 < ε' := div_pos hδ1 (mul_pos hC (lt_of_le_of_ne hd (Ne.symm hdim_zero)))
        have approx (i : ι) : ∃ p_i : A_sigma1, ‖(p_i : C(sigma1, ℝ)) - G_i i‖ < ε' :=
            ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
                A_sigma1 sep_sigma1 (G_i i) ε' hε'
        choose p_i hp_i using approx

        let P : C(sigma1, E) :=
            { toFun := fun y => l.symm (fun i => (p_i i : C(sigma1, ℝ)) y),
                continuous_toFun := by
                have h_cont_coord : Continuous (fun y => fun i => (p_i i : C(sigma1, ℝ)) y) :=
                    continuous_pi fun i => (p_i i : C(sigma1, ℝ)).continuous
                exact l.symm.continuous.comp h_cont_coord}



        have hP_bound : ∀ y , ‖P y - G_rest y‖ < δ := by
            intro y
            let dvec : ι → ℝ := fun i => (p_i i : C(sigma1, ℝ)) y - (l (G_rest y)) i

            haveI : Nonempty ι := not_isEmpty_iff.1 $ λ h_isEmpty => hdim_zero $ (Nat.cast_eq_zero (R := ℝ)).mpr $ Fintype.card_eq_zero_iff.2 h_isEmpty
            have univ_nonempty : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty

            have h_coord (i : ι) : |dvec i| < ε' := by
                have := hp_i i
                rw [ContinuousMap.norm_lt_iff _ hε'] at this
                exact this y

            let ε'nn : ℝ≥0 := ⟨ε', le_of_lt hε'⟩
            have h_coord_nn i : ‖dvec i‖₊ < ε'nn := by
                rw [← NNReal.coe_lt_coe]
                exact h_coord i

            have h_sup : (Finset.univ.sup fun i => ‖dvec i‖₊) < ε'nn := by
                rw [Finset.sup_lt_iff]
                ·   intro i _
                    exact h_coord_nn i
                ·   exact coe_lt_coe.mp hε'

            have h_norm_eq : ‖dvec‖ = (Finset.univ.sup fun i => ‖dvec i‖₊).toReal := by rw [Pi.norm_def]
            have h_norm_dvec : ‖dvec‖ < ε' := by
                rw [h_norm_eq]
                exact gt_iff_lt.mp h_sup

            have h_eq : P y - G_rest y = l.symm dvec := by
                dsimp [P]
                have h : G_rest y = l.symm (l (G_rest y)) := (l.symm_apply_apply (G_rest y)).symm
                rw [h]
                rw [← l.symm.map_sub]
                rfl


            have h_pos_norm : 0 < norm_l_symm := by
                refine lt_of_le_of_ne (norm_nonneg _) ?_
                intro h_eq
                have h_l_symm_zero : (l.symm : (ι → ℝ) →L[ℝ] E) = 0 := (norm_eq_zero.1 h_eq.symm)

                -- have h_comp : (l : E →L[ℝ] (ι → ℝ)) ∘L (l.symm : (ι → ℝ) →L[ℝ] E) = ContinuousLinearMap.id ℝ (ι → ℝ) :=
                --     ContinuousLinearEquiv.self_comp_symm l
                -- have : ContinuousLinearMap.id ℝ (ι → ℝ) = (l : E →L[ℝ] (ι → ℝ)) ∘L (l.symm : (ι → ℝ) →L[ℝ] E) :=
                --         by rw [← ContinuousLinearEquiv.coe_comp_coe_symm]; rfl

                -- refine ⟨fun i _ => h_coord_nn i, fun heq => ?_⟩
                -- exact ⟨univ_nonempty, fun i _ => h_coord_nn i⟩
            -- have h_sup : (Finset.univ.sup fun i => ‖dvec i‖₊) < ε'nn := by
            --     apply (Finset.sup_lt_iff univ_nonempty).mpr
            --     intro i _
            --     exact h_coord_nn i

            -- have h_sup : (Finset.univ.sup fun i => ‖dvec i‖₊) < ε'nn := by
            --     rw [Finset.sup_lt_iff]
            --     ·
            --     ·
                -- constructor
                -- apply Finset.sup_lt_iff
                -- · exact univ_nonempty
                -- · intro i _
                --     exact h_coord_nn i


            -- let sup_norm := Finset.univ.sup' univ_nonempty (fun i => |dvec i|)
            -- have hsup : sup_norm < ε' := (Finset.sup'_lt_iff univ_nonempty).mpr (fun i _ => h_coord i)
            -- have hnorm_eq : ‖dvec‖ = sup_norm := by
            --     rw [Pi.norm_def, sup_norm]



            -- have hsup_real : Finset.univ.max' (fun i => ‖dvec i‖) (Finset.univ_nonempty) < ε' := by
            --     apply Finset.max_lt
            --     intro i _
            --     exact hd i  -- hd i : |dvec i| < ε', and note that |dvec i| = ‖dvec i‖

            -- let ε'_nn : ℝ≥0 := ⟨ε', le_of_lt hε'⟩
            -- have hd i : |dvec i| < ε' := by
            --     have := hp_i i
            --     rw [ContinuousMap.norm_lt_iff _ hε'] at this
            --     exact this y
            -- have hsup : Finset.univ.sup (fun i => ‖dvec i‖₊) < ε'nn := by
            --     apply Finset.sup_lt_iff
            --     · exact Finset.univ.nonempty
            --     · intro i _
            --         exact hd_nn i


            -- have hsup : ‖dvec‖ < ε' := by
            --     rw [Pi.norm_def]
            --     let ε'nn : ℝ≥0 := ⟨ε', hε'.le⟩
                -- apply Finset.sup_lt_iff (by linarith [hε'])
                -- intro i _
                -- exact hd i
        --     have h1 : ‖P y - G_rest y‖^2 = ∑ i, ((p_i i : C(sigma1, ℝ)) y - (l (G_rest y)) i)^2 := by











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
