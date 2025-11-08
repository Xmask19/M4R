import Mathlib.Tactic
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.Basic



theorem brouwer_fixed_point (n : ℕ) (f : Euclidean.closedBall ((0 : EuclideanSpace ℝ (Fin n))) 1 →
        Euclidean.closedBall 0 1) (hf : Continuous f) : ∃ x, f x = x := by sorry


lemma zero_mem_closed_ball (n : ℕ) :
        (0 : EuclideanSpace ℝ (Fin n)) ∈ Euclidean.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    apply Euclidean.ball_subset_closedBall
    exact Euclidean.mem_ball_self zero_lt_one

theorem restated_IoD (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (hf_cont : Continuous f) (hf_inj : Function.Injective f)
        : f 0 ∈ interior (f ''(Euclidean.closedBall 0 1)) := by sorry

theorem invariance_of_domain (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (hf_cont : Continuous f) (hf_inj : Function.Injective f) : IsOpenMap f := by
    intro U hU
    rw [isOpen_iff_forall_mem_open]
    intro y hy
    rcases hy with ⟨x, hxU, hfx⟩
    rcases (isOpen_iff_forall_mem_open.mp hU x hxU) with ⟨nbd, hnbd1, hnbd2, hnbd3⟩
    rw [Metric.isOpen_iff] at hnbd2
    specialize hnbd2 x hnbd3
    rcases hnbd2 with ⟨ε, hε1, hε2⟩
    let g := fun (v : EuclideanSpace ℝ (Fin n)) => f (x + (ε/2) • v)
    have hg_cont : Continuous g :=
        hf_cont.comp (continuous_const.add (continuous_const.smul continuous_id))
    have hg_inj : Function.Injective g
     := by
        intro v1 v2 h
        have h13 := hf_inj h
        rw [add_right_inj] at h13
        rw [← sub_eq_zero] at h13 ⊢
        rw [← smul_sub] at h13
        have h10 : 0 < ε/2 := half_pos hε1
        rw [smul_eq_zero] at h13
        rcases h13 with h11 | h12
        ·   exfalso
            subst hfx
            simp_all only [gt_iff_lt, zero_smul, add_zero, lt_self_iff_false, g]
        · exact h12

    let shift := fun (v : EuclideanSpace ℝ (Fin n)) => x + (ε/2) • v
    have h1 : g = f ∘ shift := by
            funext v
            rfl
    have h2 : shift '' (Euclidean.closedBall 0 1) ⊆ nbd := by
        unfold shift
        have h6 : (fun v ↦ x + (ε/2) • v) = (fun w => x + w) ∘ (fun v => (ε/2) • v) := by rfl
        rw [h6, Set.image_comp, Set.image_smul]
        rw [ ← Set.singleton_add]
        have hball_eq : Euclidean.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 =
                Metric.closedBall 0 1 := by
            ext p
            simp only [Metric.mem_closedBall, dist_zero_right]
            unfold Euclidean.closedBall
            simp only [Set.mem_setOf_eq]
            rw [Euclidean.dist]
            rw [dist_eq_norm]
            simp only [map_zero, sub_zero]
            -- have h : ‖toEuclidean p‖ = ‖p‖ := sorry
            -- This is probably not true as, toEuclidean is a continous ℝ linear equivalence
            -- so it might be that p doesn't necessarily go to p but instead to some c*p?
            -- Hopefully this can be fixed via multiplying by a constant or something simple
            sorry
        rw [hball_eq]
        rw [smul_closedBall]
        ·   simp only [Real.norm_eq_abs, singleton_add_closedBall]
            have h7 : 0 < (ε/2) := half_pos hε1
            have h8 : 0 ≤ (ε/2) := Std.le_of_lt h7
            simp only [smul_zero, add_zero, mul_one]
            rw [abs_of_nonneg h8]
            transitivity Metric.ball x ε
            ·   have h9 : ε/2 < ε := by exact div_two_lt_of_pos hε1
                exact Metric.closedBall_subset_ball h9
            · exact hε2
        · exact zero_le_one' ℝ

    have h3 : f '' nbd ⊆ f '' U := Set.image_mono hnbd1
    have h4 : g '' (Euclidean.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) ⊆ f '' U := by
        rw [h1]
        rw [Set.image_comp]
        transitivity f '' nbd
        ·   exact Set.image_mono h2
        ·   exact h3

    have restated := restated_IoD n g hg_cont hg_inj
    rw [mem_interior] at restated
    rcases restated with ⟨a, ha, ha1, ha2⟩
    use a
    constructor
    ·   transitivity g '' Euclidean.closedBall 0 1
        · exact ha
        · exact h4
    constructor
    · exact ha1
    ·   unfold g at ha2
        rw [smul_zero, add_zero] at ha2
        exact Set.mem_of_eq_of_mem (hf_inj (congrArg f (id (Eq.symm hfx)))) ha2
