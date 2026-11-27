import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27627

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def pm3 (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def p4 (u : Fin 4 → Bool) : Bool :=
  (u 0 && u 1) || (u 1 && u 2) || (u 2 && u 3)

def mix (A : Finset (Fin 4)) (u v : Fin 4 → Bool) : Fin 4 → Bool :=
  fun i => if i ∈ A then u i else v i

def mixB (b0 b1 b2 b3 : Bool) (u v : Fin 4 → Bool) : Fin 4 → Bool :=
  ![if b0 then u 0 else v 0, if b1 then u 1 else v 1,
    if b2 then u 2 else v 2, if b3 then u 3 else v 3]

theorem mix_eq_mixB (A : Finset (Fin 4)) (u v : Fin 4 → Bool) :
    mix A u v = mixB (decide ((0 : Fin 4) ∈ A)) (decide ((1 : Fin 4) ∈ A))
      (decide ((2 : Fin 4) ∈ A)) (decide ((3 : Fin 4) ∈ A)) u v := by
  funext i
  fin_cases i <;> simp [mix, mixB]

theorem card_fin4_eq (A : Finset (Fin 4)) :
    A.card = (if (0 : Fin 4) ∈ A then 1 else 0) + (if (1 : Fin 4) ∈ A then 1 else 0) +
             (if (2 : Fin 4) ∈ A then 1 else 0) + (if (3 : Fin 4) ∈ A then 1 else 0) := by
  have h : A = Finset.univ.filter (fun i : Fin 4 => i ∈ A) := by ext i; simp
  conv_lhs => rw [h, Finset.card_filter, Fin.sum_univ_four]

theorem forall_fin4 {P : (Fin 4 → Bool) → Prop} (h : ∀ a b c d : Bool, P ![a, b, c, d]) :
    ∀ u : Fin 4 → Bool, P u := by
  intro u
  have hu : u = ![u 0, u 1, u 2, u 3] := by funext i; fin_cases i <;> rfl
  rw [hu]
  exact h (u 0) (u 1) (u 2) (u 3)

theorem p4_nonconst : ∃ u v : Fin 4 → Bool, p4 u ≠ p4 v := by
  refine ⟨fun _ => false, fun _ => true, ?_⟩
  decide

theorem p4_essential (i : Fin 4) :
    ∃ u v : Fin 4 → Bool, (∀ j : Fin 4, j ≠ i → u j = v j) ∧ p4 u ≠ p4 v := by
  fin_cases i
  · exact ⟨![false, true, false, false], ![true, true, false, false], by decide, by decide⟩
  · exact ⟨![true, false, false, false], ![true, true, false, false], by decide, by decide⟩
  · exact ⟨![false, false, false, true], ![false, false, true, true], by decide, by decide⟩
  · exact ⟨![false, false, true, false], ![false, false, true, true], by decide, by decide⟩

theorem p4_not_and_decomp_bool (b0 b1 b2 b3 : Bool)
    (h1 : (b0 || b1 || b2 || b3) = true) (h2 : (b0 && b1 && b2 && b3) = false) :
    ∃ u v : Fin 4 → Bool, p4 u = true ∧ p4 v = true ∧ p4 (mixB b0 b1 b2 b3 u v) = false := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3
  · simp at h1
  · exact ⟨![true,true,false,false], ![false,false,true,true], by decide, by decide, by decide⟩
  · exact ⟨![true,true,false,false], ![false,true,true,false], by decide, by decide, by decide⟩
  · exact ⟨![true,true,false,false], ![false,true,true,false], by decide, by decide, by decide⟩
  · exact ⟨![false,false,true,true], ![true,true,false,false], by decide, by decide, by decide⟩
  · exact ⟨![false,false,true,true], ![true,true,false,false], by decide, by decide, by decide⟩
  · exact ⟨![true,true,false,false], ![false,true,true,false], by decide, by decide, by decide⟩
  · exact ⟨![true,true,false,false], ![false,true,true,false], by decide, by decide, by decide⟩
  · exact ⟨![false,true,true,false], ![true,true,false,false], by decide, by decide, by decide⟩
  · exact ⟨![true,true,false,false], ![false,false,true,true], by decide, by decide, by decide⟩
  · exact ⟨![true,true,false,false], ![false,false,true,true], by decide, by decide, by decide⟩
  · exact ⟨![true,true,false,false], ![false,false,true,true], by decide, by decide, by decide⟩
  · exact ⟨![false,true,true,false], ![true,true,false,false], by decide, by decide, by decide⟩
  · exact ⟨![false,true,true,false], ![true,true,false,false], by decide, by decide, by decide⟩
  · exact ⟨![false,false,true,true], ![true,true,false,false], by decide, by decide, by decide⟩
  · simp at h2

theorem p4_not_and_decomp (A : Finset (Fin 4)) (hne : A.Nonempty) (hnu : A ≠ Finset.univ) :
    ∃ u v : Fin 4 → Bool, p4 u = true ∧ p4 v = true ∧ p4 (mix A u v) = false := by
  have hc := card_fin4_eq A
  have hc1 : 1 ≤ A.card := Finset.card_pos.mpr hne
  have hc3 : A.card ≤ 3 := by
    have hlt : A.card < (Finset.univ : Finset (Fin 4)).card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ A, hnu⟩)
    simp at hlt; omega
  have h1 : (decide ((0 : Fin 4) ∈ A) || decide ((1 : Fin 4) ∈ A) ||
      decide ((2 : Fin 4) ∈ A) || decide ((3 : Fin 4) ∈ A)) = true := by
    by_cases h0 : (0 : Fin 4) ∈ A <;> by_cases h1 : (1 : Fin 4) ∈ A <;>
    by_cases h2 : (2 : Fin 4) ∈ A <;> by_cases h3 : (3 : Fin 4) ∈ A <;>
    simp_all
  have h2 : (decide ((0 : Fin 4) ∈ A) && decide ((1 : Fin 4) ∈ A) &&
      decide ((2 : Fin 4) ∈ A) && decide ((3 : Fin 4) ∈ A)) = false := by
    by_cases h0 : (0 : Fin 4) ∈ A <;> by_cases h1 : (1 : Fin 4) ∈ A <;>
    by_cases h2 : (2 : Fin 4) ∈ A <;> by_cases h3 : (3 : Fin 4) ∈ A <;>
    simp_all
  obtain ⟨u, v, hu, hv, huv⟩ := p4_not_and_decomp_bool _ _ _ _ h1 h2
  exact ⟨u, v, hu, hv, by rw [mix_eq_mixB]; exact huv⟩

theorem p4_not_or_decomp_bool (b0 b1 b2 b3 : Bool)
    (h1 : (b0 || b1 || b2 || b3) = true) (h2 : (b0 && b1 && b2 && b3) = false) :
    ∃ u v : Fin 4 → Bool, p4 u = false ∧ p4 v = false ∧ p4 (mixB b0 b1 b2 b3 u v) = true := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3
  · simp at h1
  · exact ⟨![false,false,false,true], ![false,false,true,false], by decide, by decide, by decide⟩
  · exact ⟨![false,false,true,false], ![false,true,false,false], by decide, by decide, by decide⟩
  · exact ⟨![false,false,true,false], ![false,true,false,false], by decide, by decide, by decide⟩
  · exact ⟨![false,true,false,false], ![true,false,false,false], by decide, by decide, by decide⟩
  · exact ⟨![false,true,false,false], ![true,false,false,false], by decide, by decide, by decide⟩
  · exact ⟨![false,true,false,false], ![true,false,false,false], by decide, by decide, by decide⟩
  · exact ⟨![false,true,false,false], ![true,false,false,false], by decide, by decide, by decide⟩
  · exact ⟨![true,false,false,false], ![false,true,false,false], by decide, by decide, by decide⟩
  · exact ⟨![true,false,false,false], ![false,true,false,false], by decide, by decide, by decide⟩
  · exact ⟨![true,false,false,false], ![false,true,false,false], by decide, by decide, by decide⟩
  · exact ⟨![true,false,false,false], ![false,true,false,false], by decide, by decide, by decide⟩
  · exact ⟨![false,true,false,false], ![false,false,true,false], by decide, by decide, by decide⟩
  · exact ⟨![false,true,false,false], ![false,false,true,false], by decide, by decide, by decide⟩
  · exact ⟨![false,false,true,false], ![false,false,false,true], by decide, by decide, by decide⟩
  · simp at h2

theorem p4_not_or_decomp (A : Finset (Fin 4)) (hne : A.Nonempty) (hnu : A ≠ Finset.univ) :
    ∃ u v : Fin 4 → Bool, p4 u = false ∧ p4 v = false ∧ p4 (mix A u v) = true := by
  have hc := card_fin4_eq A
  have hc1 : 1 ≤ A.card := Finset.card_pos.mpr hne
  have hc3 : A.card ≤ 3 := by
    have hlt : A.card < (Finset.univ : Finset (Fin 4)).card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ A, hnu⟩)
    simp at hlt; omega
  have h1 : (decide ((0 : Fin 4) ∈ A) || decide ((1 : Fin 4) ∈ A) ||
      decide ((2 : Fin 4) ∈ A) || decide ((3 : Fin 4) ∈ A)) = true := by
    by_cases h0 : (0 : Fin 4) ∈ A <;> by_cases h1 : (1 : Fin 4) ∈ A <;>
    by_cases h2 : (2 : Fin 4) ∈ A <;> by_cases h3 : (3 : Fin 4) ∈ A <;>
    simp_all
  have h2 : (decide ((0 : Fin 4) ∈ A) && decide ((1 : Fin 4) ∈ A) &&
      decide ((2 : Fin 4) ∈ A) && decide ((3 : Fin 4) ∈ A)) = false := by
    by_cases h0 : (0 : Fin 4) ∈ A <;> by_cases h1 : (1 : Fin 4) ∈ A <;>
    by_cases h2 : (2 : Fin 4) ∈ A <;> by_cases h3 : (3 : Fin 4) ∈ A <;>
    simp_all
  obtain ⟨u, v, hu, hv, huv⟩ := p4_not_or_decomp_bool _ _ _ _ h1 h2
  exact ⟨u, v, hu, hv, by rw [mix_eq_mixB]; exact huv⟩

theorem p4_no_module_bool (b0 b1 b2 b3 : Bool)
    (h2 : 2 ≤ (if b0 then 1 else 0) + (if b1 then 1 else 0) + (if b2 then 1 else 0) + (if b3 then 1 else 0))
    (h3 : (if b0 then 1 else 0) + (if b1 then 1 else 0) + (if b2 then 1 else 0) + (if b3 then 1 else 0) ≤ 3) :
    ∃ u1 u2 u3 : Fin 4 → Bool,
      (∃ v : Fin 4 → Bool, p4 (mixB b0 b1 b2 b3 u1 v) ≠ p4 (mixB b0 b1 b2 b3 u2 v)) ∧
      (∃ v : Fin 4 → Bool, p4 (mixB b0 b1 b2 b3 u1 v) ≠ p4 (mixB b0 b1 b2 b3 u3 v)) ∧
      (∃ v : Fin 4 → Bool, p4 (mixB b0 b1 b2 b3 u2 v) ≠ p4 (mixB b0 b1 b2 b3 u3 v)) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3
  · simp at h2
  · simp at h2
  · simp at h2
  · exact ⟨![false,false,false,false], ![false,false,true,false], ![false,false,true,true],
      ⟨![false,true,false,false], by decide⟩, ⟨![false,false,false,false], by decide⟩, ⟨![false,false,false,false], by decide⟩⟩
  · simp at h2
  · exact ⟨![false,false,false,false], ![false,true,false,false], ![false,false,false,true],
      ⟨![true,false,false,false], by decide⟩, ⟨![false,false,true,false], by decide⟩, ⟨![true,false,false,false], by decide⟩⟩
  · exact ⟨![false,false,false,false], ![false,true,false,false], ![false,false,true,false],
      ⟨![true,false,false,false], by decide⟩, ⟨![false,false,false,true], by decide⟩, ⟨![true,false,false,false], by decide⟩⟩
  · exact ⟨![false,false,false,false], ![false,true,false,false], ![false,true,true,false],
      ⟨![true,false,false,false], by decide⟩, ⟨![false,false,false,false], by decide⟩, ⟨![false,false,false,false], by decide⟩⟩
  · simp at h2
  · exact ⟨![false,false,false,false], ![true,false,false,false], ![false,false,false,true],
      ⟨![false,true,false,false], by decide⟩, ⟨![false,false,true,false], by decide⟩, ⟨![false,true,false,false], by decide⟩⟩
  · exact ⟨![false,false,false,false], ![true,false,false,false], ![false,false,true,false],
      ⟨![false,true,false,false], by decide⟩, ⟨![false,true,false,false], by decide⟩, ⟨![false,false,false,true], by decide⟩⟩
  · exact ⟨![false,false,false,false], ![true,false,false,false], ![false,false,true,true],
      ⟨![false,true,false,false], by decide⟩, ⟨![false,false,false,false], by decide⟩, ⟨![false,false,false,false], by decide⟩⟩
  · exact ⟨![false,false,false,false], ![false,true,false,false], ![true,true,false,false],
      ⟨![false,false,true,false], by decide⟩, ⟨![false,false,false,false], by decide⟩, ⟨![false,false,false,false], by decide⟩⟩
  · exact ⟨![false,false,false,false], ![false,true,false,false], ![true,true,false,false],
      ⟨![false,false,true,false], by decide⟩, ⟨![false,false,false,false], by decide⟩, ⟨![false,false,false,false], by decide⟩⟩
  · exact ⟨![false,false,false,false], ![true,true,false,false], ![false,false,true,false],
      ⟨![false,false,false,false], by decide⟩, ⟨![false,false,false,true], by decide⟩, ⟨![false,false,false,false], by decide⟩⟩
  · simp at h3

theorem p4_no_module (A : Finset (Fin 4)) (h2 : 2 ≤ A.card) (h3 : A.card ≤ 3) :
    ∃ u1 u2 u3 : Fin 4 → Bool,
      (∃ v : Fin 4 → Bool, p4 (mix A u1 v) ≠ p4 (mix A u2 v)) ∧
      (∃ v : Fin 4 → Bool, p4 (mix A u1 v) ≠ p4 (mix A u3 v)) ∧
      (∃ v : Fin 4 → Bool, p4 (mix A u2 v) ≠ p4 (mix A u3 v)) := by
  have hc := card_fin4_eq A
  have h2' : 2 ≤ (if decide ((0 : Fin 4) ∈ A) then 1 else 0) + (if decide ((1 : Fin 4) ∈ A) then 1 else 0) +
      (if decide ((2 : Fin 4) ∈ A) then 1 else 0) + (if decide ((3 : Fin 4) ∈ A) then 1 else 0) := by
    simp only [decide_eq_true_eq]; omega
  have h3' : (if decide ((0 : Fin 4) ∈ A) then 1 else 0) + (if decide ((1 : Fin 4) ∈ A) then 1 else 0) +
      (if decide ((2 : Fin 4) ∈ A) then 1 else 0) + (if decide ((3 : Fin 4) ∈ A) then 1 else 0) ≤ 3 := by
    simp only [decide_eq_true_eq]; omega
  obtain ⟨u1, u2, u3, ⟨v12, h12⟩, ⟨v13, h13⟩, ⟨v23, h23⟩⟩ := p4_no_module_bool _ _ _ _ h2' h3'
  refine ⟨u1, u2, u3, ⟨v12, ?_⟩, ⟨v13, ?_⟩, ⟨v23, ?_⟩⟩
  · rw [mix_eq_mixB, mix_eq_mixB]; exact h12
  · rw [mix_eq_mixB, mix_eq_mixB]; exact h13
  · rw [mix_eq_mixB, mix_eq_mixB]; exact h23

inductive Expr where
  | const (b : Bool)
  | var (i : Fin 4)
  | not (e : Expr)
  | and (e1 e2 : Expr)
  | or (e1 e2 : Expr)

def Expr.eval (v : Fin 4 → Bool) : Expr → Bool
  | .const b => b
  | .var i => v i
  | .not e => !(e.eval v)
  | .and e1 e2 => e1.eval v && e2.eval v
  | .or e1 e2 => e1.eval v || e2.eval v

def Expr.vars : Expr → Finset (Fin 4)
  | .const _ => ∅
  | .var i => {i}
  | .not e => e.vars
  | .and e1 e2 => e1.vars ∪ e2.vars
  | .or e1 e2 => e1.vars ∪ e2.vars

def Expr.readOnce : Expr → Prop
  | .const _ => True
  | .var _ => True
  | .not e => e.readOnce
  | .and e1 e2 => e1.readOnce ∧ e2.readOnce ∧ Disjoint e1.vars e2.vars
  | .or e1 e2 => e1.readOnce ∧ e2.readOnce ∧ Disjoint e1.vars e2.vars

theorem Expr.eval_eq_of_eq_on_vars : ∀ (e : Expr) {u v : Fin 4 → Bool},
    (∀ i ∈ e.vars, u i = v i) → e.eval u = e.eval v
  | .const _, _, _, _ => rfl
  | .var i, _, _, h => h i (by simp [Expr.vars])
  | .not e, _, _, h => congrArg (! ·) (e.eval_eq_of_eq_on_vars h)
  | .and e1 e2, _, _, h => by
    simp only [Expr.eval]
    rw [e1.eval_eq_of_eq_on_vars (fun i hi => h i (Finset.mem_union_left _ hi)),
        e2.eval_eq_of_eq_on_vars (fun i hi => h i (Finset.mem_union_right _ hi))]
  | .or e1 e2, _, _, h => by
    simp only [Expr.eval]
    rw [e1.eval_eq_of_eq_on_vars (fun i hi => h i (Finset.mem_union_left _ hi)),
        e2.eval_eq_of_eq_on_vars (fun i hi => h i (Finset.mem_union_right _ hi))]

theorem Expr.not_p4_or_not_p4 : ∀ (e : Expr), e.readOnce →
    ((∀ u, e.eval u = p4 u) ∨ (∀ u, e.eval u = !p4 u)) → False
  | .const b, _, h => by
    obtain ⟨u, v, huv⟩ := p4_nonconst
    rcases h with h | h
    · exact huv ((h u).symm.trans (h v))
    · have hu := h u; have hv := h v
      simp only [Expr.eval] at hu hv
      exact huv (Bool.not_inj (hu.symm.trans hv))
  | .var i, _, h => by
    obtain ⟨j, hji⟩ : ∃ j : Fin 4, j ≠ i := by
      fin_cases i
      · exact ⟨1, by decide⟩
      · exact ⟨0, by decide⟩
      · exact ⟨0, by decide⟩
      · exact ⟨0, by decide⟩
    obtain ⟨u, v, heq, hne⟩ := p4_essential j
    have hi : u i = v i := heq i hji.symm
    rcases h with h | h
    · exact hne ((h u).symm.trans (hi.trans (h v)))
    · have hu := h u; have hv := h v
      simp only [Expr.eval] at hu hv
      exact hne (Bool.not_inj (hu.symm.trans (hi.trans hv)))
  | .not e, hro, h => by
    apply e.not_p4_or_not_p4 hro
    rcases h with h | h
    · right; intro u; have := h u; simp only [Expr.eval] at this; rw [← this, Bool.not_not]
    · left; intro u; have := h u; simp only [Expr.eval] at this; exact Bool.not_inj this
  | .and e1 e2, ⟨hro1, hro2, hdisj⟩, h => by
    by_cases hc1 : ∃ c, ∀ u, e1.eval u = c
    · obtain ⟨c, hc⟩ := hc1
      cases c
      · obtain ⟨u, v, huv⟩ := p4_nonconst
        rcases h with h | h
        · have hu := h u; have hv := h v
          simp only [Expr.eval, hc, Bool.false_and] at hu hv
          exact huv (hu.symm.trans hv)
        · have hu := h u; have hv := h v
          simp only [Expr.eval, hc, Bool.false_and] at hu hv
          exact huv (Bool.not_inj (hu.symm.trans hv))
      · apply e2.not_p4_or_not_p4 hro2
        rcases h with h | h
        · left; intro u; have := h u; simp only [Expr.eval, hc, Bool.true_and] at this; exact this
        · right; intro u; have := h u; simp only [Expr.eval, hc, Bool.true_and] at this; exact this
    · by_cases hc2 : ∃ c, ∀ u, e2.eval u = c
      · obtain ⟨c, hc⟩ := hc2
        cases c
        · obtain ⟨u, v, huv⟩ := p4_nonconst
          rcases h with h | h
          · have hu := h u; have hv := h v
            simp only [Expr.eval, hc, Bool.and_false] at hu hv
            exact huv (hu.symm.trans hv)
          · have hu := h u; have hv := h v
            simp only [Expr.eval, hc, Bool.and_false] at hu hv
            exact huv (Bool.not_inj (hu.symm.trans hv))
        · apply e1.not_p4_or_not_p4 hro1
          rcases h with h | h
          · left; intro u; have := h u; simp only [Expr.eval, hc, Bool.and_true] at this; exact this
          · right; intro u; have := h u; simp only [Expr.eval, hc, Bool.and_true] at this; exact this
      · have hne1 : e1.vars.Nonempty := by
          by_contra hempty
          rw [Finset.not_nonempty_iff_eq_empty] at hempty
          exact hc1 ⟨e1.eval (fun _ => false), fun u =>
            e1.eval_eq_of_eq_on_vars (fun i hi => by rw [hempty] at hi; exact absurd hi (by simp))⟩
        have hne2 : e2.vars.Nonempty := by
          by_contra hempty
          rw [Finset.not_nonempty_iff_eq_empty] at hempty
          exact hc2 ⟨e2.eval (fun _ => false), fun u =>
            e2.eval_eq_of_eq_on_vars (fun i hi => by rw [hempty] at hi; exact absurd hi (by simp))⟩
        have hnu1 : e1.vars ≠ Finset.univ := by
          intro huniv
          obtain ⟨j, hj⟩ := hne2
          have hj1 : j ∈ e1.vars := by rw [huniv]; exact Finset.mem_univ j
          exact Finset.disjoint_left.mp hdisj hj1 hj
        rcases h with h | h
        · obtain ⟨u, v, hu, hv, huv⟩ := p4_not_and_decomp e1.vars hne1 hnu1
          have h1 : e1.eval u = true := by
            have := h u; simp only [Expr.eval, hu] at this; exact (Bool.and_eq_true _ _).mp this |>.1
          have h2 : e2.eval v = true := by
            have := h v; simp only [Expr.eval, hv] at this; exact (Bool.and_eq_true _ _).mp this |>.2
          have hm1 : e1.eval (mix e1.vars u v) = e1.eval u :=
            e1.eval_eq_of_eq_on_vars (fun i hi => by simp [mix, hi])
          have hm2 : e2.eval (mix e1.vars u v) = e2.eval v :=
            e2.eval_eq_of_eq_on_vars (fun i hi => by
              have hni : i ∉ e1.vars := Finset.disjoint_right.mp hdisj hi
              simp [mix, hni])
          have hm := h (mix e1.vars u v)
          simp only [Expr.eval, hm1, hm2, h1, h2, Bool.true_and, huv] at hm
          exact Bool.noConfusion hm
        · obtain ⟨u, v, hu, hv, huv⟩ := p4_not_or_decomp e1.vars hne1 hnu1
          have h1 : e1.eval u = true := by
            have := h u; simp only [Expr.eval, hu, Bool.not_false] at this
            exact (Bool.and_eq_true _ _).mp this |>.1
          have h2 : e2.eval v = true := by
            have := h v; simp only [Expr.eval, hv, Bool.not_false] at this
            exact (Bool.and_eq_true _ _).mp this |>.2
          have hm1 : e1.eval (mix e1.vars u v) = e1.eval u :=
            e1.eval_eq_of_eq_on_vars (fun i hi => by simp [mix, hi])
          have hm2 : e2.eval (mix e1.vars u v) = e2.eval v :=
            e2.eval_eq_of_eq_on_vars (fun i hi => by
              have hni : i ∉ e1.vars := Finset.disjoint_right.mp hdisj hi
              simp [mix, hni])
          have hm := h (mix e1.vars u v)
          simp only [Expr.eval, hm1, hm2, h1, h2, Bool.true_and, huv, Bool.not_true] at hm
          exact Bool.noConfusion hm
  | .or e1 e2, ⟨hro1, hro2, hdisj⟩, h => by
    by_cases hc1 : ∃ c, ∀ u, e1.eval u = c
    · obtain ⟨c, hc⟩ := hc1
      cases c
      · apply e2.not_p4_or_not_p4 hro2
        rcases h with h | h
        · left; intro u; have := h u; simp only [Expr.eval, hc, Bool.false_or] at this; exact this
        · right; intro u; have := h u; simp only [Expr.eval, hc, Bool.false_or] at this; exact this
      · obtain ⟨u, v, huv⟩ := p4_nonconst
        rcases h with h | h
        · have hu := h u; have hv := h v
          simp only [Expr.eval, hc, Bool.true_or] at hu hv
          exact huv (hu.symm.trans hv)
        · have hu := h u; have hv := h v
          simp only [Expr.eval, hc, Bool.true_or] at hu hv
          exact huv (Bool.not_inj (hu.symm.trans hv))
    · by_cases hc2 : ∃ c, ∀ u, e2.eval u = c
      · obtain ⟨c, hc⟩ := hc2
        cases c
        · apply e1.not_p4_or_not_p4 hro1
          rcases h with h | h
          · left; intro u; have := h u; simp only [Expr.eval, hc, Bool.or_false] at this; exact this
          · right; intro u; have := h u; simp only [Expr.eval, hc, Bool.or_false] at this; exact this
        · obtain ⟨u, v, huv⟩ := p4_nonconst
          rcases h with h | h
          · have hu := h u; have hv := h v
            simp only [Expr.eval, hc, Bool.or_true] at hu hv
            exact huv (hu.symm.trans hv)
          · have hu := h u; have hv := h v
            simp only [Expr.eval, hc, Bool.or_true] at hu hv
            exact huv (Bool.not_inj (hu.symm.trans hv))
      · have hne1 : e1.vars.Nonempty := by
          by_contra hempty
          rw [Finset.not_nonempty_iff_eq_empty] at hempty
          exact hc1 ⟨e1.eval (fun _ => false), fun u =>
            e1.eval_eq_of_eq_on_vars (fun i hi => by rw [hempty] at hi; exact absurd hi (by simp))⟩
        have hne2 : e2.vars.Nonempty := by
          by_contra hempty
          rw [Finset.not_nonempty_iff_eq_empty] at hempty
          exact hc2 ⟨e2.eval (fun _ => false), fun u =>
            e2.eval_eq_of_eq_on_vars (fun i hi => by rw [hempty] at hi; exact absurd hi (by simp))⟩
        have hnu1 : e1.vars ≠ Finset.univ := by
          intro huniv
          obtain ⟨j, hj⟩ := hne2
          have hj1 : j ∈ e1.vars := by rw [huniv]; exact Finset.mem_univ j
          exact Finset.disjoint_left.mp hdisj hj1 hj
        rcases h with h | h
        · obtain ⟨u, v, hu, hv, huv⟩ := p4_not_or_decomp e1.vars hne1 hnu1
          have h1 : e1.eval u = false := by
            have := h u; simp only [Expr.eval, hu] at this; exact (Bool.or_eq_false_iff.mp this).1
          have h2 : e2.eval v = false := by
            have := h v; simp only [Expr.eval, hv] at this; exact (Bool.or_eq_false_iff.mp this).2
          have hm1 : e1.eval (mix e1.vars u v) = e1.eval u :=
            e1.eval_eq_of_eq_on_vars (fun i hi => by simp [mix, hi])
          have hm2 : e2.eval (mix e1.vars u v) = e2.eval v :=
            e2.eval_eq_of_eq_on_vars (fun i hi => by
              have hni : i ∉ e1.vars := Finset.disjoint_right.mp hdisj hi
              simp [mix, hni])
          have hm := h (mix e1.vars u v)
          simp only [Expr.eval, hm1, hm2, h1, h2, Bool.false_or, huv] at hm
          exact Bool.noConfusion hm
        · obtain ⟨u, v, hu, hv, huv⟩ := p4_not_and_decomp e1.vars hne1 hnu1
          have h1 : e1.eval u = false := by
            have := h u; simp only [Expr.eval, hu, Bool.not_true] at this
            exact (Bool.or_eq_false_iff.mp this).1
          have h2 : e2.eval v = false := by
            have := h v; simp only [Expr.eval, hv, Bool.not_true] at this
            exact (Bool.or_eq_false_iff.mp this).2
          have hm1 : e1.eval (mix e1.vars u v) = e1.eval u :=
            e1.eval_eq_of_eq_on_vars (fun i hi => by simp [mix, hi])
          have hm2 : e2.eval (mix e1.vars u v) = e2.eval v :=
            e2.eval_eq_of_eq_on_vars (fun i hi => by
              have hni : i ∉ e1.vars := Finset.disjoint_right.mp hdisj hi
              simp [mix, hni])
          have hm := h (mix e1.vars u v)
          simp only [Expr.eval, hm1, hm2, h1, h2, Bool.false_or, huv, Bool.not_false] at hm
          exact Bool.noConfusion hm

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wireVal (C : Circuit) (x : Fin 9 → Bool) (k : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD k false

theorem foldl_step_len : ∀ (gs : List Gate) (w : List Bool),
    (gs.foldl step w).length = w.length + gs.length
  | [], w => by simp
  | g :: gs, w => by
    simp only [List.foldl_cons, foldl_step_len, step, List.length_append, List.length_cons,
      List.length_nil]
    omega

theorem foldl_step_getD_lt : ∀ (gs : List Gate) (w : List Bool) {k : ℕ},
    k < w.length → (gs.foldl step w).getD k false = w.getD k false
  | [], _, _, _ => rfl
  | g :: gs, w, k, hk => by
    simp only [List.foldl_cons]
    have hlt : k < (step w g).length := by simp [step]; omega
    rw [foldl_step_getD_lt gs (step w g) hlt]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem wireVal_lt_nine (C : Circuit) (x : Fin 9 → Bool) {k : ℕ} (hk : k < 9) :
    wireVal C x k = x ⟨k, hk⟩ := by
  unfold wireVal Circuit.wires
  have hlen : k < (List.ofFn x).length := by simp [hk]
  change (C.gates.foldl step (List.ofFn x)).getD k false = x ⟨k, hk⟩
  rw [foldl_step_getD_lt C.gates (List.ofFn x) hlen, List.getD_eq_getElem _ _ hlen,
    List.getElem_ofFn]

theorem wireVal_gate (C : Circuit) (x : Fin 9 → Bool) (j : ℕ) (hj : j < C.gates.length)
    (hin : ∀ a ∈ (C.gates[j]).inputs, a < 9 + j) :
    wireVal C x (9 + j) =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map (wireVal C x)) := by
  unfold wireVal Circuit.wires
  change (C.gates.foldl step (List.ofFn x)).getD (9 + j) false = _
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    have h1 := (List.take_append_drop j C.gates).symm
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    exact h1
  set w := (C.gates.take j).foldl step (List.ofFn x)
  have hwlen : w.length = 9 + j := by
    rw [foldl_step_len, List.length_ofFn, List.length_take_of_le (Nat.le_of_lt hj)]
  have hstep_val : (C.gates.foldl step (List.ofFn x)).getD (9 + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => w.getD i false) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    have hlt : 9 + j < (step w C.gates[j]).length := by simp [step, hwlen]
    rw [foldl_step_getD_lt _ _ hlt]
    simp only [step, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega), hwlen]
    simp
  rw [hstep_val]
  congr 1
  apply List.map_congr_left
  intro a ha
  have halt : a < w.length := by rw [hwlen]; exact hin a ha
  change w.getD a false = (C.gates.foldl step (List.ofFn x)).getD a false
  conv_rhs => rw [hsplit]
  rw [List.foldl_append, foldl_step_getD_lt _ _ halt]

theorem list_length_eq_sum_count : ∀ (l : List ℕ) (B : ℕ),
    (∀ a ∈ l, a < B) → l.length = ∑ w ∈ Finset.range B, l.count w
  | [], B, _ => by simp
  | a :: l, B, h => by
    have ha : a < B := h a List.mem_cons_self
    have hl : ∀ b ∈ l, b < B := fun b hb => h b (List.mem_cons_of_mem _ hb)
    rw [List.length_cons, list_length_eq_sum_count l B hl]
    have hstep : ∀ w, (a :: l).count w = l.count w + if w = a then 1 else 0 := by
      intro w
      simp only [List.count_cons, beq_iff_eq]
      by_cases hwa : a = w
      · subst hwa; simp
      · have hne : w ≠ a := Ne.symm hwa
        simp [hwa, hne]
    simp_rw [hstep]
    rw [Finset.sum_add_distrib]
    have h1 : (∑ w ∈ Finset.range B, if w = a then 1 else 0) = 1 := by
      rw [Finset.sum_ite_eq' (Finset.range B) a (fun _ => 1)]
      simp [ha]
    rw [h1]

theorem list_flatMap_length_le_two_mul : ∀ (gs : List Gate),
    (∀ g ∈ gs, g.inputs.length ≤ 2) → (gs.flatMap (·.inputs)).length ≤ 2 * gs.length
  | [], _ => by simp
  | g :: gs, h => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 : g.inputs.length ≤ 2 := h g List.mem_cons_self
    have h2 := list_flatMap_length_le_two_mul gs (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
    omega

theorem count_ge_two_of_two_gates (R : List Gate) {i1 i2 : ℕ}
    (h1 : i1 < R.length) (h2 : i2 < R.length) (hne : i1 ≠ i2)
    {u : ℕ} (hu1 : u ∈ R[i1].inputs) (hu2 : u ∈ R[i2].inputs) :
    2 ≤ (R.flatMap (·.inputs)).count u := by
  have hmem_count : ∀ {l : List ℕ}, u ∈ l → 1 ≤ l.count u :=
    fun h => Nat.succ_le_of_lt (List.count_pos_iff.mpr h)
  have hcount_flat : ∀ (L : List Gate), (L.flatMap (·.inputs)).count u =
      (L.map (fun g => g.inputs.count u)).sum := by
    intro L
    induction L with
    | nil => simp
    | cons g L ih => simp [List.flatMap_cons, List.count_append, ih]
  rw [hcount_flat]
  have hsum_fin : (R.map (fun g => g.inputs.count u)).sum =
      ∑ idx : Fin R.length, (R[idx.val]).inputs.count u := by
    rw [← List.sum_ofFn]
    congr 1
    apply List.ext_getElem (by simp)
    intro i hi _
    simp
  rw [hsum_fin]
  let f1 : Fin R.length := ⟨i1, h1⟩
  let f2 : Fin R.length := ⟨i2, h2⟩
  have hfne : f1 ≠ f2 := fun heq => hne (congrArg Fin.val heq)
  have hsub : ({f1, f2} : Finset (Fin R.length)) ⊆ Finset.univ := Finset.subset_univ _
  have hle := Finset.sum_le_sum_of_subset (f := fun idx : Fin R.length => (R[idx.val]).inputs.count u) hsub
  rw [Finset.sum_pair hfne] at hle
  have hc1 : 1 ≤ (R[f1.val]).inputs.count u := hmem_count hu1
  have hc2 : 1 ≤ (R[f2.val]).inputs.count u := hmem_count hu2
  omega

def reach (C : Circuit)
    (hWF : ∀ j : Fin C.gates.length, ∀ a ∈ (C.gates.get j).inputs, a < 9 + j.val)
    (stop : Option ℕ) (k : ℕ) : Finset ℕ :=
  if some k = stop then {k}
  else if h : 11 ≤ k ∧ k - 9 < C.gates.length then
    insert k (((C.gates.get ⟨k - 9, h.2⟩).inputs).attach.foldr
      (fun ⟨a, ha⟩ s =>
        have : a < k := by have h1 : a < 9 + (k - 9) := hWF ⟨k - 9, h.2⟩ a ha; omega
        reach C hWF stop a ∪ s) ∅)
  else {k}
termination_by k

theorem mem_reach_self (C : Circuit)
    (hWF : ∀ j : Fin C.gates.length, ∀ a ∈ (C.gates.get j).inputs, a < 9 + j.val)
    (stop : Option ℕ) (k : ℕ) : k ∈ reach C hWF stop k := by
  rw [reach]
  split_ifs <;> simp

theorem foldr_union_mem {α : Type*} [DecidableEq α] {β : Type*}
    (f : β → Finset α) : ∀ (l : List β) (u : α),
    u ∈ l.foldr (fun x s => f x ∪ s) ∅ ↔ ∃ x ∈ l, u ∈ f x
  | [], _ => by simp
  | x :: l, u => by
    simp only [List.foldr_cons, Finset.mem_union, List.mem_cons, foldr_union_mem]
    constructor
    · rintro (h | ⟨y, hy, h⟩)
      · exact ⟨x, Or.inl rfl, h⟩
      · exact ⟨y, Or.inr hy, h⟩
    · rintro ⟨y, rfl | hy, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨y, hy, h⟩

theorem mem_reach_gate_iff (C : Circuit)
    (hWF : ∀ j : Fin C.gates.length, ∀ a ∈ (C.gates.get j).inputs, a < 9 + j.val)
    (stop : Option ℕ) {k : ℕ} (hns : some k ≠ stop) (hk1 : 11 ≤ k) (hk2 : k - 9 < C.gates.length)
    (u : ℕ) :
    u ∈ reach C hWF stop k ↔
      u = k ∨ ∃ a ∈ (C.gates.get ⟨k - 9, hk2⟩).inputs, u ∈ reach C hWF stop a := by
  conv_lhs => rw [reach]
  simp only [hns, ↓reduceIte, hk1, hk2, and_self, ↓reduceDIte, Finset.mem_insert, foldr_union_mem]
  constructor
  · rintro (rfl | ⟨⟨a, ha⟩, _, hu⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨a, ha, hu⟩
  · rintro (rfl | ⟨a, ha, hu⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨⟨a, ha⟩, List.mem_attach _ _, hu⟩

theorem le_of_mem_reach (C : Circuit)
    (hWF : ∀ j : Fin C.gates.length, ∀ a ∈ (C.gates.get j).inputs, a < 9 + j.val)
    (stop : Option ℕ) : ∀ k u, u ∈ reach C hWF stop k → u ≤ k := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro u hu
    by_cases hns : some k = stop
    · rw [reach, ite_eq_left_iff.mpr (fun h => absurd hns h)] at hu; simp at hu; omega
    · by_cases hg : 11 ≤ k ∧ k - 9 < C.gates.length
      · rw [mem_reach_gate_iff C hWF stop hns hg.1 hg.2] at hu
        rcases hu with rfl | ⟨a, ha, hua⟩
        · exact le_rfl
        · have halt : a < k := by have h1 : a < 9 + (k - 9) := hWF ⟨k - 9, hg.2⟩ a ha; omega
          exact le_trans (ih a halt u hua) (Nat.le_of_lt halt)
      · rw [reach, ite_eq_right_iff.mpr (fun h => absurd h hns),
            dite_eq_right_iff.mpr (fun h => absurd h hg)] at hu; simp at hu; omega

theorem reach_subset_of_mem (C : Circuit)
    (hWF : ∀ j : Fin C.gates.length, ∀ a ∈ (C.gates.get j).inputs, a < 9 + j.val)
    (stop : Option ℕ) : ∀ k a, a ∈ reach C hWF stop k → reach C hWF stop a ⊆ reach C hWF stop k := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro a ha u hu
    by_cases hns : some k = stop
    · rw [reach, ite_eq_left_iff.mpr (fun h => absurd hns h)] at ha; simp at ha; subst ha; exact hu
    · by_cases hg : 11 ≤ k ∧ k - 9 < C.gates.length
      · rw [mem_reach_gate_iff C hWF stop hns hg.1 hg.2] at ha
        rcases ha with rfl | ⟨b, hb, hab⟩
        · exact hu
        · have hblt : b < k := by have h1 : b < 9 + (k - 9) := hWF ⟨k - 9, hg.2⟩ b hb; omega
          have hub : u ∈ reach C hWF stop b := ih b hblt a hab hu
          rw [mem_reach_gate_iff C hWF stop hns hg.1 hg.2]
          exact Or.inr ⟨b, hb, hub⟩
      · rw [reach, ite_eq_right_iff.mpr (fun h => absurd h hns),
            dite_eq_right_iff.mpr (fun h => absurd h hg)] at ha; simp at ha; subst ha; exact hu

theorem reach_parent_of_lt (C : Circuit)
    (hWF : ∀ j : Fin C.gates.length, ∀ a ∈ (C.gates.get j).inputs, a < 9 + j.val)
    (stop : Option ℕ) : ∀ k u, u ∈ reach C hWF stop k → u < k →
    ∃ p ∈ reach C hWF stop k, some p ≠ stop ∧ 11 ≤ p ∧
      ∃ hp : p - 9 < C.gates.length, u ∈ (C.gates.get ⟨p - 9, hp⟩).inputs := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro u hu hlt
    by_cases hns : some k = stop
    · rw [reach, ite_eq_left_iff.mpr (fun h => absurd hns h)] at hu; simp at hu; omega
    · by_cases hg : 11 ≤ k ∧ k - 9 < C.gates.length
      · rw [mem_reach_gate_iff C hWF stop hns hg.1 hg.2] at hu
        rcases hu with rfl | ⟨a, ha, hua⟩
        · omega
        · have hale : u ≤ a := le_of_mem_reach C hWF stop a u hua
          have halt : a < k := by have h1 : a < 9 + (k - 9) := hWF ⟨k - 9, hg.2⟩ a ha; omega
          by_cases heq : u = a
          · subst heq
            exact ⟨k, mem_reach_self C hWF stop k, hns, hg.1, hg.2, ha⟩
          · obtain ⟨p, hp_mem, hp_ns, hp11, hp_lt, hp_in⟩ := ih a halt u hua (by omega)
            have hp_k : p ∈ reach C hWF stop k := by
              rw [mem_reach_gate_iff C hWF stop hns hg.1 hg.2]
              exact Or.inr ⟨a, ha, hp_mem⟩
            exact ⟨p, hp_k, hp_ns, hp11, hp_lt, hp_in⟩
      · rw [reach, ite_eq_right_iff.mpr (fun h => absurd h hns),
            dite_eq_right_iff.mpr (fun h => absurd h hg)] at hu; simp at hu; omega

theorem reach_disjoint_of_single_read (C : Circuit)
    (hWF : ∀ j : Fin C.gates.length, ∀ a ∈ (C.gates.get j).inputs, a < 9 + j.val)
    (stop : Option ℕ) (B : ℕ)
    (hcnt : ∀ u, u < B → some u ≠ stop →
      ((C.gates.drop 2).flatMap (·.inputs)).count u ≤ 1)
    {p : ℕ} (_hpns : some p ≠ stop) (hp11 : 11 ≤ p) (hplt : p - 9 < C.gates.length)
    (hpB : p ≤ B)
    {a b : ℕ} (hab : a < b) (hins : (C.gates.get ⟨p - 9, hplt⟩).inputs = [a, b]) :
    Disjoint ((reach C hWF stop a).filter (fun x => some x ≠ stop))
             ((reach C hWF stop b).filter (fun x => some x ≠ stop)) := by
  rw [Finset.disjoint_left]
  intro u0 hu0a hu0b
  let I := ((reach C hWF stop a).filter (fun x => some x ≠ stop)) ∩
           ((reach C hWF stop b).filter (fun x => some x ≠ stop))
  have hIne : I.Nonempty := ⟨u0, Finset.mem_inter.mpr ⟨hu0a, hu0b⟩⟩
  set M := I.max' hIne
  have hMmem : M ∈ I := Finset.max'_mem I hIne
  have hMa : M ∈ reach C hWF stop a := (Finset.mem_filter.mp (Finset.mem_inter.mp hMmem).1).1
  have hMb : M ∈ reach C hWF stop b := (Finset.mem_filter.mp (Finset.mem_inter.mp hMmem).2).1
  have hMns : some M ≠ stop := (Finset.mem_filter.mp (Finset.mem_inter.mp hMmem).1).2
  have hMlea : M ≤ a := le_of_mem_reach C hWF stop a M hMa
  have hMltb : M < b := lt_of_le_of_lt hMlea hab
  have hbltp : b < p := by
    have h1 : b < 9 + (p - 9) := hWF ⟨p - 9, hplt⟩ b (by rw [hins]; simp)
    omega
  have hMltB : M < B := by omega
  obtain ⟨q2, hq2b, hq2ns, hq211, hq2lt, hq2in⟩ := reach_parent_of_lt C hWF stop b M hMb hMltb
  have hq2leb : q2 ≤ b := le_of_mem_reach C hWF stop b q2 hq2b
  by_cases hMeqa : M = a
  · have hRlen : (C.gates.drop 2).length = C.gates.length - 2 := List.length_drop
    have hi1 : p - 11 < (C.gates.drop 2).length := by omega
    have hi2 : q2 - 11 < (C.gates.drop 2).length := by omega
    have hne : p - 11 ≠ q2 - 11 := by omega
    have hin1 : M ∈ (C.gates.drop 2)[p - 11].inputs := by
      simp only [List.getElem_drop]
      have heq : 2 + (p - 11) = p - 9 := by omega
      have : C.gates[2 + (p - 11)]'(by omega) = C.gates.get ⟨p - 9, hplt⟩ := by
        simp [heq]
      rw [this, hins, hMeqa]; simp
    have hin2 : M ∈ (C.gates.drop 2)[q2 - 11].inputs := by
      simp only [List.getElem_drop]
      have heq : 2 + (q2 - 11) = q2 - 9 := by omega
      have : C.gates[2 + (q2 - 11)]'(by omega) = C.gates.get ⟨q2 - 9, hq2lt⟩ := by
        simp [heq]
      rw [this]; exact hq2in
    have hge2 := count_ge_two_of_two_gates (C.gates.drop 2) hi1 hi2 hne hin1 hin2
    have hle1 := hcnt M hMltB hMns
    omega
  · obtain ⟨q1, hq1a, hq1ns, hq111, hq1lt, hq1in⟩ :=
      reach_parent_of_lt C hWF stop a M hMa (by omega)
    by_cases hqeq : q1 = q2
    · subst hqeq
      have hq1inI : q1 ∈ I := Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mpr ⟨hq1a, hq1ns⟩, Finset.mem_filter.mpr ⟨hq2b, hq1ns⟩⟩
      have hqleM : q1 ≤ M := Finset.le_max' I q1 hq1inI
      have hMltq1 : M < q1 := by have h1 : M < 9 + (q1 - 9) := hWF ⟨q1 - 9, hq1lt⟩ M hq1in; omega
      omega
    · have hRlen : (C.gates.drop 2).length = C.gates.length - 2 := List.length_drop
      have hi1 : q1 - 11 < (C.gates.drop 2).length := by omega
      have hi2 : q2 - 11 < (C.gates.drop 2).length := by omega
      have hne : q1 - 11 ≠ q2 - 11 := by omega
      have hin1 : M ∈ (C.gates.drop 2)[q1 - 11].inputs := by
        simp only [List.getElem_drop]
        have heq : 2 + (q1 - 11) = q1 - 9 := by omega
        have : C.gates[2 + (q1 - 11)]'(by omega) = C.gates.get ⟨q1 - 9, hq1lt⟩ := by
          simp [heq]
        rw [this]; exact hq1in
      have hin2 : M ∈ (C.gates.drop 2)[q2 - 11].inputs := by
        simp only [List.getElem_drop]
        have heq : 2 + (q2 - 11) = q2 - 9 := by omega
        have : C.gates[2 + (q2 - 11)]'(by omega) = C.gates.get ⟨q2 - 9, hq2lt⟩ := by
          simp [heq]
        rw [this]; exact hq2in
      have hge2 := count_ge_two_of_two_gates (C.gates.drop 2) hi1 hi2 hne hin1 hin2
      have hle1 := hcnt M hMltB hMns
      omega

theorem reach_disjoint_sub_outer (C : Circuit)
    (hWF : ∀ j : Fin C.gates.length, ∀ a ∈ (C.gates.get j).inputs, a < 9 + j.val)
    (wstar : ℕ) (hwlt : wstar < 8 + C.gates.length)
    (hcnt : ∀ u, u < 8 + C.gates.length → u ≠ wstar →
      ((C.gates.drop 2).flatMap (·.inputs)).count u ≤ 1) :
    Disjoint ((reach C hWF none wstar).erase wstar)
             ((reach C hWF (some wstar) (8 + C.gates.length)).erase wstar) := by
  rw [Finset.disjoint_left]
  intro u0 hu01 hu02
  let I := ((reach C hWF none wstar).erase wstar) ∩
           ((reach C hWF (some wstar) (8 + C.gates.length)).erase wstar)
  have hIne : I.Nonempty := ⟨u0, Finset.mem_inter.mpr ⟨hu01, hu02⟩⟩
  set M := I.max' hIne
  have hMmem : M ∈ I := Finset.max'_mem I hIne
  have hM1 : M ∈ reach C hWF none wstar := (Finset.mem_erase.mp (Finset.mem_inter.mp hMmem).1).2
  have hM2 : M ∈ reach C hWF (some wstar) (8 + C.gates.length) :=
    (Finset.mem_erase.mp (Finset.mem_inter.mp hMmem).2).2
  have hMne : M ≠ wstar := (Finset.mem_erase.mp (Finset.mem_inter.mp hMmem).1).1
  have hMle : M ≤ wstar := le_of_mem_reach C hWF none wstar M hM1
  have hMltw : M < wstar := lt_of_le_of_ne hMle hMne
  have hMltOut : M < 8 + C.gates.length := lt_trans hMltw hwlt
  obtain ⟨q1, hq1m, _, hq111, hq1lt, hq1in⟩ := reach_parent_of_lt C hWF none wstar M hM1 hMltw
  obtain ⟨q2, hq2m, hq2ns, hq211, hq2lt, hq2in⟩ :=
    reach_parent_of_lt C hWF (some wstar) (8 + C.gates.length) M hM2 hMltOut
  have hq2ne : q2 ≠ wstar := fun h => hq2ns (congrArg some h)
  by_cases hqeq : q1 = q2
  · subst hqeq
    have hq1inI : q1 ∈ I := Finset.mem_inter.mpr
      ⟨Finset.mem_erase.mpr ⟨hq2ne, hq1m⟩, Finset.mem_erase.mpr ⟨hq2ne, hq2m⟩⟩
    have hqleM : q1 ≤ M := Finset.le_max' I q1 hq1inI
    have hMltq1 : M < q1 := by have h1 : M < 9 + (q1 - 9) := hWF ⟨q1 - 9, hq1lt⟩ M hq1in; omega
    omega
  · have hRlen : (C.gates.drop 2).length = C.gates.length - 2 := List.length_drop
    have hi1 : q1 - 11 < (C.gates.drop 2).length := by omega
    have hi2 : q2 - 11 < (C.gates.drop 2).length := by omega
    have hne : q1 - 11 ≠ q2 - 11 := by omega
    have hin1 : M ∈ (C.gates.drop 2)[q1 - 11].inputs := by
      simp only [List.getElem_drop]
      have heq : 2 + (q1 - 11) = q1 - 9 := by omega
      have : C.gates[2 + (q1 - 11)]'(by omega) = C.gates.get ⟨q1 - 9, hq1lt⟩ := by
        simp [heq]
      rw [this]; exact hq1in
    have hin2 : M ∈ (C.gates.drop 2)[q2 - 11].inputs := by
      simp only [List.getElem_drop]
      have heq : 2 + (q2 - 11) = q2 - 9 := by omega
      have : C.gates[2 + (q2 - 11)]'(by omega) = C.gates.get ⟨q2 - 9, hq2lt⟩ := by
        simp [heq]
      rw [this]; exact hq2in
    have hge2 := count_ge_two_of_two_gates (C.gates.drop 2) hi1 hi2 hne hin1 hin2
    have hle1 := hcnt M hMltOut hMne
    omega

theorem nine_not_in_reach_of_count_zero (C : Circuit)
    (hWF : ∀ j : Fin C.gates.length, ∀ a ∈ (C.gates.get j).inputs, a < 9 + j.val)
    (stop : Option ℕ)
    (hcnt9 : ((C.gates.drop 2).flatMap (·.inputs)).count 9 = 0)
    {k : ℕ} (hkne : k ≠ 9) : 9 ∉ reach C hWF stop k := by
  intro h9
  have h9le : 9 ≤ k := le_of_mem_reach C hWF stop k 9 h9
  have h9lt : 9 < k := lt_of_le_of_ne h9le (Ne.symm hkne)
  obtain ⟨p, _, _, hp11, hplt, hpin⟩ := reach_parent_of_lt C hWF stop k 9 h9 h9lt
  have hmemR : C.gates.get ⟨p - 9, hplt⟩ ∈ C.gates.drop 2 := by
    have : C.gates.get ⟨p - 9, hplt⟩ = (C.gates.drop 2)[p - 11]'(by simp; omega) := by
      simp only [List.getElem_drop, List.get_eq_getElem]
      congr 1; omega
    rw [this]
    exact List.getElem_mem _
  have hmem : 9 ∈ (C.gates.drop 2).flatMap (·.inputs) :=
    List.mem_flatMap.mpr ⟨C.gates.get ⟨p - 9, hplt⟩, hmemR, hpin⟩
  have hpos : 0 < ((C.gates.drop 2).flatMap (·.inputs)).count 9 := List.count_pos_iff.mpr hmem
  omega

structure Restr where
  V : Fin 4 → Fin 9
  emb : (Fin 4 → Bool) → (Fin 9 → Bool)
  fix : Fin 9 → Bool
  c10 : Bool
  V_inj : Function.Injective V
  emb_V : ∀ u i, emb u (V i) = u i
  emb_other : ∀ u j, (∀ i, V i ≠ j) → emb u j = fix j
  g1_const : ∀ u, (emb u 1 && (emb u 0 || emb u 4)) = c10
  pm3_eq_p4 : ∀ u, pm3 (emb u) = p4 u

theorem eval_depends_only_on_reach (C : Circuit)
    (hWF : ∀ j : Fin C.gates.length, ∀ a ∈ (C.gates.get j).inputs, a < 9 + j.val)
    (_hg0 : ∀ x, wireVal C x 9 = (x 0 || x 4))
    (hg1 : ∀ x, wireVal C x 10 = (x 1 && (x 0 || x 4)))
    (R : Restr) (stop : Option ℕ)
    : ∀ k, k < 9 + C.gates.length →
      (9 ∈ reach C hWF stop k → ∀ u1 u2, wireVal C (R.emb u1) 9 = wireVal C (R.emb u2) 9) →
      ∀ u1 u2 : Fin 4 → Bool,
      (∀ i : Fin 4, (R.V i).val ∈ reach C hWF stop k → some (R.V i).val ≠ stop → u1 i = u2 i) →
      (∀ w, stop = some w → w ∈ reach C hWF stop k →
        wireVal C (R.emb u1) w = wireVal C (R.emb u2) w) →
      wireVal C (R.emb u1) k = wireVal C (R.emb u2) k := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hklt h9 u1 u2 hvar hstop
    by_cases hks : some k = stop
    · exact hstop k hks.symm (mem_reach_self C hWF stop k)
    · by_cases hk9 : k < 9
      · rw [wireVal_lt_nine C _ hk9, wireVal_lt_nine C _ hk9]
        by_cases hex : ∃ i : Fin 4, R.V i = ⟨k, hk9⟩
        · obtain ⟨i, hi⟩ := hex
          rw [← hi, R.emb_V, R.emb_V]
          apply hvar i
          · rw [hi]; exact mem_reach_self C hWF stop k
          · rw [hi]; exact hks
        · push Not at hex
          rw [R.emb_other u1 ⟨k, hk9⟩ hex, R.emb_other u2 ⟨k, hk9⟩ hex]
      · by_cases hk9eq : k = 9
        · subst hk9eq
          exact h9 (mem_reach_self C hWF stop 9) u1 u2
        · by_cases hk10 : k = 10
          · subst hk10
            rw [hg1, hg1, R.g1_const u1, R.g1_const u2]
          · have hk11 : 11 ≤ k := by omega
            have hkl : k - 9 < C.gates.length := by omega
            have h1 : 9 + (k - 9) = k := by omega
            have hin : ∀ a ∈ (C.gates[k - 9]'hkl).inputs, a < 9 + (k - 9) := by
              intro a ha
              exact hWF ⟨k - 9, hkl⟩ a ha
            have hw1 := wireVal_gate C (R.emb u1) (k - 9) hkl hin
            have hw2 := wireVal_gate C (R.emb u2) (k - 9) hkl hin
            rw [h1] at hw1 hw2
            rw [hw1, hw2]
            congr 1
            apply List.map_congr_left
            intro a ha
            have halt : a < k := by have := hin a ha; omega
            have hsub : reach C hWF stop a ⊆ reach C hWF stop k := by
              intro z hz
              rw [mem_reach_gate_iff C hWF stop hks hk11 hkl]
              exact Or.inr ⟨a, ha, hz⟩
            exact ih a halt (by omega) (fun ha9 => h9 (hsub ha9)) u1 u2
              (fun i hi hni => hvar i (hsub hi) hni)
              (fun w hw hwm => hstop w hw (hsub hwm))

theorem buildExpr_of_reach (C : Circuit)
    (hNF : ∀ j : Fin C.gates.length,
      ((C.gates.get j).op = GateOp.not ∧ ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = GateOp.and ∨ (C.gates.get j).op = GateOp.or) ∧
        ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b]))
    (hWF : ∀ j : Fin C.gates.length, ∀ a ∈ (C.gates.get j).inputs, a < 9 + j.val)
    (_hg0 : ∀ x, wireVal C x 9 = (x 0 || x 4))
    (hg1 : ∀ x, wireVal C x 10 = (x 1 && (x 0 || x 4)))
    (R : Restr) (stop : Option ℕ) (B : ℕ)
    (hstopConst : ∀ w, stop = some w → ∃ c, ∀ u, wireVal C (R.emb u) w = c)
    (hcnt : ∀ u, u < B → some u ≠ stop →
      ((C.gates.drop 2).flatMap (·.inputs)).count u ≤ 1)
    : ∀ k, k ≤ B → k < 9 + C.gates.length →
      (9 ∈ reach C hWF stop k → ∃ c, ∀ u, wireVal C (R.emb u) 9 = c) →
      ∃ e : Expr, e.readOnce ∧
        (∀ i ∈ e.vars, (R.V i).val ∈ reach C hWF stop k ∧ some (R.V i).val ≠ stop) ∧
        (∀ u, e.eval u = wireVal C (R.emb u) k) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hkB hklt h9Const
    by_cases hks : some k = stop
    · obtain ⟨c, hc⟩ := hstopConst k hks.symm
      exact ⟨.const c, trivial, by simp [Expr.vars], fun u => (hc u).symm⟩
    · by_cases hk9 : k < 9
      · by_cases hex : ∃ i : Fin 4, R.V i = ⟨k, hk9⟩
        · obtain ⟨i, hi⟩ := hex
          refine ⟨.var i, trivial, ?_, ?_⟩
          · intro j hj
            simp only [Expr.vars, Finset.mem_singleton] at hj
            subst hj
            rw [hi]
            exact ⟨mem_reach_self C hWF stop k, hks⟩
          · intro u
            rw [wireVal_lt_nine C _ hk9, ← hi, R.emb_V]
            rfl
        · push Not at hex
          refine ⟨.const (R.fix ⟨k, hk9⟩), trivial, by simp [Expr.vars], fun u => ?_⟩
          rw [wireVal_lt_nine C _ hk9, R.emb_other u ⟨k, hk9⟩ hex]
          rfl
      · by_cases hk9eq : k = 9
        · subst hk9eq
          obtain ⟨c, hc⟩ := h9Const (mem_reach_self C hWF stop 9)
          exact ⟨.const c, trivial, by simp [Expr.vars], fun u => (hc u).symm⟩
        · by_cases hk10 : k = 10
          · subst hk10
            refine ⟨.const R.c10, trivial, by simp [Expr.vars], fun u => ?_⟩
            rw [hg1, R.g1_const u]; rfl
          · have hk11 : 11 ≤ k := by omega
            have hkl : k - 9 < C.gates.length := by omega
            have h1 : 9 + (k - 9) = k := by omega
            have hin : ∀ a ∈ (C.gates[k - 9]'hkl).inputs, a < 9 + (k - 9) := fun a ha =>
              hWF ⟨k - 9, hkl⟩ a ha
            have hwg : ∀ u, wireVal C (R.emb u) k =
                (C.gates[k - 9]'hkl).op.eval ((C.gates[k - 9]'hkl).inputs.map (wireVal C (R.emb u))) := by
              intro u
              have := wireVal_gate C (R.emb u) (k - 9) hkl hin
              rw [h1] at this
              exact this
            rcases hNF ⟨k - 9, hkl⟩ with ⟨hop, a, halt, hins⟩ | ⟨hop, a, b, hab, hblt, hins⟩
            · have ha_lt : a < k := by dsimp at halt; omega
              have ha_sub : reach C hWF stop a ⊆ reach C hWF stop k := fun z hz => by
                rw [mem_reach_gate_iff C hWF stop hks hk11 hkl]
                exact Or.inr ⟨a, by rw [hins]; simp, hz⟩
              obtain ⟨ea, hea_ro, hea_vars, hea_eval⟩ :=
                ih a ha_lt (by omega) (by omega) (fun ha9 => h9Const (ha_sub ha9))
              refine ⟨.not ea, hea_ro, ?_, ?_⟩
              · intro i hi
                obtain ⟨hmem, hns⟩ := hea_vars i hi
                exact ⟨ha_sub hmem, hns⟩
              · intro u
                rw [hwg u]
                change (!(ea.eval u)) = _
                rw [hea_eval u]
                have hget : C.gates[k - 9]'hkl = C.gates.get ⟨k - 9, hkl⟩ := rfl
                rw [hget, hop, hins]
                simp [GateOp.eval]
            · have ha_lt : a < k := by dsimp at hblt; omega
              have hb_lt : b < k := by dsimp at hblt; omega
              have ha_sub : reach C hWF stop a ⊆ reach C hWF stop k := fun z hz => by
                rw [mem_reach_gate_iff C hWF stop hks hk11 hkl]
                exact Or.inr ⟨a, by rw [hins]; simp, hz⟩
              have hb_sub : reach C hWF stop b ⊆ reach C hWF stop k := fun z hz => by
                rw [mem_reach_gate_iff C hWF stop hks hk11 hkl]
                exact Or.inr ⟨b, by rw [hins]; simp, hz⟩
              obtain ⟨ea, hea_ro, hea_vars, hea_eval⟩ :=
                ih a ha_lt (by omega) (by omega) (fun ha9 => h9Const (ha_sub ha9))
              obtain ⟨eb, heb_ro, heb_vars, heb_eval⟩ :=
                ih b hb_lt (by omega) (by omega) (fun hb9 => h9Const (hb_sub hb9))
              have hd_reach := reach_disjoint_of_single_read C hWF stop B hcnt hks hk11 hkl hkB hab hins
              have hd_vars : Disjoint ea.vars eb.vars := by
                rw [Finset.disjoint_left]
                intro i hia hib
                have h1a : (R.V i).val ∈ (reach C hWF stop a).filter (fun x => some x ≠ stop) :=
                  Finset.mem_filter.mpr (hea_vars i hia)
                have h1b : (R.V i).val ∈ (reach C hWF stop b).filter (fun x => some x ≠ stop) :=
                  Finset.mem_filter.mpr (heb_vars i hib)
                exact Finset.disjoint_left.mp hd_reach h1a h1b
              rcases hop with hop | hop
              · refine ⟨.and ea eb, ⟨hea_ro, heb_ro, hd_vars⟩, ?_, ?_⟩
                · intro i hi
                  rcases Finset.mem_union.mp hi with hia | hib
                  · obtain ⟨hmem, hns⟩ := hea_vars i hia
                    exact ⟨ha_sub hmem, hns⟩
                  · obtain ⟨hmem, hns⟩ := heb_vars i hib
                    exact ⟨hb_sub hmem, hns⟩
                · intro u
                  rw [hwg u]
                  change (ea.eval u && eb.eval u) = _
                  rw [hea_eval u, heb_eval u]
                  have hget : C.gates[k - 9]'hkl = C.gates.get ⟨k - 9, hkl⟩ := rfl
                  rw [hget, hop, hins]
                  simp [GateOp.eval]
              · refine ⟨.or ea eb, ⟨hea_ro, heb_ro, hd_vars⟩, ?_, ?_⟩
                · intro i hi
                  rcases Finset.mem_union.mp hi with hia | hib
                  · obtain ⟨hmem, hns⟩ := hea_vars i hia
                    exact ⟨ha_sub hmem, hns⟩
                  · obtain ⟨hmem, hns⟩ := heb_vars i hib
                    exact ⟨hb_sub hmem, hns⟩
                · intro u
                  rw [hwg u]
                  change (ea.eval u || eb.eval u) = _
                  rw [hea_eval u, heb_eval u]
                  have hget : C.gates[k - 9]'hkl = C.gates.get ⟨k - 9, hkl⟩ := rfl
                  rw [hget, hop, hins]
                  simp [GateOp.eval]

def R1 : Restr where
  V := ![0, 4, 2, 3]
  emb := fun u => ![u 0, false, u 2, u 3, u 1, false, true, true, true]
  fix := ![false, false, false, false, false, false, true, true, true]
  c10 := false
  V_inj := by decide
  emb_V := forall_fin4 (by decide)
  emb_other := forall_fin4 (by decide)
  g1_const := forall_fin4 (by decide)
  pm3_eq_p4 := forall_fin4 (by decide)

def R2 : Restr where
  V := ![6, 5, 0, 8]
  emb := fun u => ![u 2, true, false, false, true, u 1, u 0, true, u 3]
  fix := ![false, true, false, false, true, false, false, true, false]
  c10 := true
  V_inj := by decide
  emb_V := forall_fin4 (by decide)
  emb_other := forall_fin4 (by decide)
  g1_const := forall_fin4 (by decide)
  pm3_eq_p4 := forall_fin4 (by decide)

def R3 : Restr where
  V := ![5, 1, 3, 7]
  emb := fun u => ![false, u 1, true, u 2, false, u 0, true, u 3, true]
  fix := ![false, false, true, false, false, false, true, false, true]
  c10 := false
  V_inj := by decide
  emb_V := forall_fin4 (by decide)
  emb_other := forall_fin4 (by decide)
  g1_const := forall_fin4 (by decide)
  pm3_eq_p4 := forall_fin4 (by decide)

theorem R3_g0_const : ∀ u, (R3.emb u 0 || R3.emb u 4) = false := forall_fin4 (by decide)

def R4 : Restr where
  V := ![6, 2, 3, 8]
  emb := fun u => ![false, true, u 1, u 2, true, false, u 0, true, u 3]
  fix := ![false, true, false, false, true, false, false, true, false]
  c10 := true
  V_inj := by decide
  emb_V := forall_fin4 (by decide)
  emb_other := forall_fin4 (by decide)
  g1_const := forall_fin4 (by decide)
  pm3_eq_p4 := forall_fin4 (by decide)

def R5 : Restr where
  V := ![3, 8, 4, 6]
  emb := fun u => ![true, true, true, u 0, u 2, false, u 3, false, u 1]
  fix := ![true, true, true, false, false, false, false, false, false]
  c10 := true
  V_inj := by decide
  emb_V := forall_fin4 (by decide)
  emb_other := forall_fin4 (by decide)
  g1_const := forall_fin4 (by decide)
  pm3_eq_p4 := forall_fin4 (by decide)

theorem no_hitting_set_card_one (S : Finset (Fin 9))
    (h1 : (Finset.univ.filter (fun i : Fin 4 => R1.V i ∈ S)).card = 1)
    (h2 : (Finset.univ.filter (fun i : Fin 4 => R2.V i ∈ S)).card = 1)
    (h3 : (Finset.univ.filter (fun i : Fin 4 => R3.V i ∈ S)).card = 1)
    (h4 : (Finset.univ.filter (fun i : Fin 4 => R4.V i ∈ S)).card = 1)
    (h5 : (Finset.univ.filter (fun i : Fin 4 => R5.V i ∈ S)).card = 1) : False := by
  rw [Finset.card_filter, Fin.sum_univ_four] at h1 h2 h3 h4 h5
  have h1' : (if (0 : Fin 9) ∈ S then 1 else 0) + (if (4 : Fin 9) ∈ S then 1 else 0) +
      (if (2 : Fin 9) ∈ S then 1 else 0) + (if (3 : Fin 9) ∈ S then 1 else 0) = 1 := h1
  have h2' : (if (6 : Fin 9) ∈ S then 1 else 0) + (if (5 : Fin 9) ∈ S then 1 else 0) +
      (if (0 : Fin 9) ∈ S then 1 else 0) + (if (8 : Fin 9) ∈ S then 1 else 0) = 1 := h2
  have h3' : (if (5 : Fin 9) ∈ S then 1 else 0) + (if (1 : Fin 9) ∈ S then 1 else 0) +
      (if (3 : Fin 9) ∈ S then 1 else 0) + (if (7 : Fin 9) ∈ S then 1 else 0) = 1 := h3
  have h4' : (if (6 : Fin 9) ∈ S then 1 else 0) + (if (2 : Fin 9) ∈ S then 1 else 0) +
      (if (3 : Fin 9) ∈ S then 1 else 0) + (if (8 : Fin 9) ∈ S then 1 else 0) = 1 := h4
  have h5' : (if (3 : Fin 9) ∈ S then 1 else 0) + (if (8 : Fin 9) ∈ S then 1 else 0) +
      (if (4 : Fin 9) ∈ S then 1 else 0) + (if (6 : Fin 9) ∈ S then 1 else 0) = 1 := h5
  set b0 : ℕ := if (0 : Fin 9) ∈ S then 1 else 0
  set b1 : ℕ := if (1 : Fin 9) ∈ S then 1 else 0
  set b2 : ℕ := if (2 : Fin 9) ∈ S then 1 else 0
  set b3 : ℕ := if (3 : Fin 9) ∈ S then 1 else 0
  set b4 : ℕ := if (4 : Fin 9) ∈ S then 1 else 0
  set b5 : ℕ := if (5 : Fin 9) ∈ S then 1 else 0
  set b6 : ℕ := if (6 : Fin 9) ∈ S then 1 else 0
  set b7 : ℕ := if (7 : Fin 9) ∈ S then 1 else 0
  set b8 : ℕ := if (8 : Fin 9) ∈ S then 1 else 0
  have hb0 : b0 ≤ 1 := by dsimp [b0]; split_ifs <;> omega
  have hb1 : b1 ≤ 1 := by dsimp [b1]; split_ifs <;> omega
  have hb2 : b2 ≤ 1 := by dsimp [b2]; split_ifs <;> omega
  have hb3 : b3 ≤ 1 := by dsimp [b3]; split_ifs <;> omega
  have hb4 : b4 ≤ 1 := by dsimp [b4]; split_ifs <;> omega
  have hb5 : b5 ≤ 1 := by dsimp [b5]; split_ifs <;> omega
  have hb6 : b6 ≤ 1 := by dsimp [b6]; split_ifs <;> omega
  have hb7 : b7 ≤ 1 := by dsimp [b7]; split_ifs <;> omega
  have hb8 : b8 ≤ 1 := by dsimp [b8]; split_ifs <;> omega
  omega

theorem witness_essential (i : Fin 9) :
    ∃ x y : Fin 9 → Bool,
      (∀ j : Fin 9, j ≠ i → x j = y j) ∧
      (x 0 || x 4) = (y 0 || y 4) ∧
      (x 1 && (x 0 || x 4)) = (y 1 && (y 0 || y 4)) ∧
      pm3 x ≠ pm3 y := by
  fin_cases i
  · exact ⟨![false,false,false,false,true,true,false,true,false],
           ![true,false,false,false,true,true,false,true,false], by decide, by decide, by decide, by decide⟩
  · exact ⟨![false,false,false,false,false,true,true,false,false],
           ![false,true,false,false,false,true,true,false,false], by decide, by decide, by decide, by decide⟩
  · exact ⟨![false,false,false,false,true,false,true,false,false],
           ![false,false,true,false,true,false,true,false,false], by decide, by decide, by decide, by decide⟩
  · exact ⟨![false,false,true,false,false,false,false,true,false],
           ![false,false,true,true,false,false,false,true,false], by decide, by decide, by decide, by decide⟩
  · exact ⟨![true,false,true,false,false,false,true,false,false],
           ![true,false,true,false,true,false,true,false,false], by decide, by decide, by decide, by decide⟩
  · exact ⟨![false,true,false,false,false,false,true,false,false],
           ![false,true,false,false,false,true,true,false,false], by decide, by decide, by decide, by decide⟩
  · exact ⟨![false,false,true,false,true,false,false,false,false],
           ![false,false,true,false,true,false,true,false,false], by decide, by decide, by decide, by decide⟩
  · exact ⟨![false,false,true,true,false,false,false,false,false],
           ![false,false,true,true,false,false,false,true,false], by decide, by decide, by decide, by decide⟩
  · exact ⟨![false,true,false,true,false,false,false,false,false],
           ![false,true,false,true,false,false,false,false,true], by decide, by decide, by decide, by decide⟩

theorem main_proof : ¬ (∃ C : Circuit,
    FanInTwo C ∧ C.size ≤ 12 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = pm3 x) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = GateOp.and ∨
          (C.gates.get j).op = GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨GateOp.or, [0, 4]⟩ ∧
    C.gates.tail.head? = some ⟨GateOp.and, [1, 9]⟩) := by
  rintro ⟨C, hfan, hsize, heval, hout, hNF, _, hlive, hg0h, hg1h⟩
  have hWF : ∀ j : Fin C.gates.length, ∀ a ∈ (C.gates.get j).inputs, a < 9 + j.val := by
    intro j a ha
    rcases hNF j with ⟨_, x, hx, hins⟩ | ⟨_, x, y, hxy, hy, hins⟩
    · rw [hins] at ha; simp at ha; omega
    · rw [hins] at ha; simp at ha; rcases ha with rfl | rfl <;> omega
  cases hgs : C.gates with
  | nil => rw [hgs] at hg0h; simp at hg0h
  | cons g0 rest1 =>
    rw [hgs] at hg0h; simp only [List.head?_cons, Option.some.injEq] at hg0h; subst hg0h
    cases rest1 with
    | nil => rw [hgs] at hg1h; simp at hg1h
    | cons g1 rest2 =>
      rw [hgs] at hg1h; simp only [List.tail_cons, List.head?_cons, Option.some.injEq] at hg1h; subst hg1h
      have hlen : C.gates.length = rest2.length + 2 := by rw [hgs]; simp
      have hm_le : rest2.length ≤ 10 := by
        have : C.size = C.gates.length := rfl
        omega
      have hout_eq : C.output = 10 + rest2.length := by
        have : C.size = C.gates.length := rfl
        omega
      have hg0_val : ∀ x, wireVal C x 9 = (x 0 || x 4) := by
        intro x
        have h0lt : 0 < C.gates.length := by omega
        have h := wireVal_gate C x 0 h0lt (fun a ha => hWF ⟨0, h0lt⟩ a ha)
        have hget : C.gates[0]'h0lt = ⟨GateOp.or, [0, 4]⟩ := by simp [hgs]
        rw [hget] at h
        simp only [Nat.add_zero, List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
          List.any_nil, id_eq, Bool.or_false] at h
        rw [wireVal_lt_nine C x (k := 0) (by decide), wireVal_lt_nine C x (k := 4) (by decide)] at h
        exact h
      have hg1_val : ∀ x, wireVal C x 10 = (x 1 && (x 0 || x 4)) := by
        intro x
        have h1lt : 1 < C.gates.length := by omega
        have h := wireVal_gate C x 1 h1lt (fun a ha => hWF ⟨1, h1lt⟩ a ha)
        have hget : C.gates[1]'h1lt = ⟨GateOp.and, [1, 9]⟩ := by simp [hgs]
        rw [hget] at h
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
          id_eq, Bool.and_true] at h
        rw [wireVal_lt_nine C x (k := 1) (by decide), hg0_val x] at h
        exact h
      have hm_pos : 1 ≤ rest2.length := by
        by_contra h0
        have hm0 : rest2.length = 0 := by omega
        have ho10 : C.output = 10 := by omega
        let x0 : Fin 9 → Bool := ![false, false, true, true, false, false, false, true, false]
        have he := heval x0
        have hw : C.eval (List.ofFn x0) = wireVal C x0 10 := by unfold Circuit.eval wireVal; rw [ho10]
        rw [hw, hg1_val x0] at he
        revert he; decide
      have hdrop : C.gates.drop 2 = rest2 := by simp [hgs]
      set allIns : List ℕ := rest2.flatMap (·.inputs)

      have hread_in : ∀ i < 9, 1 ≤ allIns.count i := by
        intro i hi
        by_contra hlt1
        have hcz : allIns.count i = 0 := by omega
        have hnotmem : ∀ g ∈ rest2, i ∉ g.inputs := by
          intro g hg hin
          have hmem : i ∈ allIns := List.mem_flatMap.mpr ⟨g, hg, hin⟩
          have hpos := List.count_pos_iff.mpr hmem
          omega
        obtain ⟨x, y, hxy, hg0eq, hg1eq, hpmne⟩ := witness_essential ⟨i, hi⟩
        have hagree : ∀ k, k < 9 + C.gates.length → k ≠ i → wireVal C x k = wireVal C y k := by
          intro k
          induction k using Nat.strongRecOn with
          | ind k ih =>
            intro hklt hkne
            by_cases hk9 : k < 9
            · rw [wireVal_lt_nine C x hk9, wireVal_lt_nine C y hk9]
              exact hxy ⟨k, hk9⟩ (fun heq => hkne (congrArg Fin.val heq))
            · by_cases hk9eq : k = 9
              · subst hk9eq; rw [hg0_val, hg0_val, hg0eq]
              · by_cases hk10 : k = 10
                · subst hk10; rw [hg1_val, hg1_val, hg1eq]
                · have hkl : k - 9 < C.gates.length := by omega
                  have h1 : 9 + (k - 9) = k := by omega
                  have hin : ∀ a ∈ (C.gates[k - 9]'hkl).inputs, a < 9 + (k - 9) := fun a ha =>
                    hWF ⟨k - 9, hkl⟩ a ha
                  have hwx := wireVal_gate C x (k - 9) hkl hin
                  have hwy := wireVal_gate C y (k - 9) hkl hin
                  rw [h1] at hwx hwy
                  rw [hwx, hwy]
                  congr 1
                  apply List.map_congr_left
                  intro a ha
                  have halt : a < k := by have := hin a ha; omega
                  have hmemR : C.gates[k - 9]'hkl ∈ rest2 := by
                    rw [← hdrop]
                    have : C.gates[k - 9]'hkl = (C.gates.drop 2)[k - 11]'(by simp; omega) := by
                      simp only [List.getElem_drop]; congr 1; omega
                    rw [this]; exact List.getElem_mem _
                  have hanei : a ≠ i := fun heq => hnotmem _ hmemR (heq ▸ ha)
                  exact ih a halt (by omega) hanei
        have hout_eq_val : wireVal C x C.output = wireVal C y C.output :=
          hagree C.output (by omega) (by omega)
        have h1 : C.eval (List.ofFn x) = C.eval (List.ofFn y) := hout_eq_val
        rw [heval x, heval y] at h1
        exact hpmne h1

      have hread_live : ∀ w, 10 ≤ w → w < 10 + rest2.length → 1 ≤ allIns.count w := by
        intro w hw1 hw2
        have hjlt : w - 9 < C.gates.length := by omega
        have hj1 : (w - 9) + 1 < C.gates.length := by omega
        obtain ⟨k, hjk, hwin⟩ := hlive ⟨w - 9, hjlt⟩ hj1
        have h9w : 9 + (w - 9) = w := by omega
        dsimp at hjk hwin
        rw [h9w] at hwin
        have hk2 : 2 ≤ k.val := by omega
        have hmemR : C.gates.get k ∈ rest2 := by
          rw [← hdrop]
          have : C.gates.get k = (C.gates.drop 2)[k.val - 2]'(by simp; omega) := by
            simp only [List.getElem_drop, List.get_eq_getElem]; congr 1; omega
          rw [this]; exact List.getElem_mem _
        have hmem : w ∈ allIns := List.mem_flatMap.mpr ⟨C.gates.get k, hmemR, hwin⟩
        exact Nat.succ_le_of_lt (List.count_pos_iff.mpr hmem)

      let B := 10 + rest2.length
      have hall_lt : ∀ a ∈ allIns, a < B := by
        intro a ha
        obtain ⟨g, hgR, hag⟩ := List.mem_flatMap.mp ha
        obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hgR
        have hidxC : idx + 2 < C.gates.length := by omega
        have hget : rest2[idx]'hidx = C.gates.get ⟨idx + 2, hidxC⟩ := by
          simp only [List.get_eq_getElem]
          have h1 : (C.gates.drop 2)[idx]'(by rw [hdrop]; exact hidx) = C.gates[2 + idx]'(by omega) :=
            List.getElem_drop
          have h2 : rest2[idx]'hidx = (C.gates.drop 2)[idx]'(by rw [hdrop]; exact hidx) := by
            congr 1; exact hdrop.symm
          rw [h2, h1]
          congr 1; omega
        rw [hget] at hag
        have hlt1 : a < 9 + (idx + 2) := hWF ⟨idx + 2, hidxC⟩ a hag
        omega
      have hsum_eq : allIns.length = ∑ w ∈ Finset.range B, allIns.count w :=
        list_length_eq_sum_count allIns B hall_lt
      have hlen_le : allIns.length ≤ 2 * rest2.length := by
        apply list_flatMap_length_le_two_mul
        intro g hg
        have hgC : g ∈ C.gates := by rw [hgs]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg)
        exact (hfan g hgC).2
      let Req : Finset ℕ := (Finset.range B).erase 9
      have h9inB : 9 ∈ Finset.range B := Finset.mem_range.mpr (by omega)
      have hsum_split : ∑ w ∈ Finset.range B, allIns.count w =
          allIns.count 9 + ∑ w ∈ Req, allIns.count w :=
        (Finset.add_sum_erase (Finset.range B) (fun w => allIns.count w) h9inB).symm
      have hreq_ge1 : ∀ w ∈ Req, 1 ≤ allIns.count w := by
        intro w hw
        have hwne : w ≠ 9 := (Finset.mem_erase.mp hw).1
        have hwlt : w < B := Finset.mem_range.mp (Finset.mem_erase.mp hw).2
        by_cases h9 : w < 9
        · exact hread_in w h9
        · exact hread_live w (by omega) hwlt
      have hreq_card : Req.card = 9 + rest2.length := by
        rw [Finset.card_erase_of_mem h9inB, Finset.card_range]
        omega
      have hsum_excess : ∑ w ∈ Req, allIns.count w =
          Req.card + ∑ w ∈ Req, (allIns.count w - 1) := by
        have h1 : ∀ w ∈ Req, allIns.count w = 1 + (allIns.count w - 1) := fun w hw => by
          have := hreq_ge1 w hw; omega
        rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
      have hexcess_le : allIns.count 9 + ∑ w ∈ Req, (allIns.count w - 1) ≤ 1 := by
        omega

      by_cases hex0 : ∑ w ∈ Req, (allIns.count w - 1) = 0
      ·
        have hcnt_le1 : ∀ u < 8 + C.gates.length, some u ≠ (none : Option ℕ) →
            ((C.gates.drop 2).flatMap (·.inputs)).count u ≤ 1 := by
          intro u hu _
          rw [hdrop]
          change allIns.count u ≤ 1
          by_cases hu9 : u = 9
          · subst hu9; omega
          · have huReq : u ∈ Req := Finset.mem_erase.mpr ⟨hu9, Finset.mem_range.mpr (by omega)⟩
            have h0 : allIns.count u - 1 = 0 :=
              (Finset.sum_eq_zero_iff.mp hex0) u huReq
            omega
        obtain ⟨e, he_ro, _, he_eval⟩ := buildExpr_of_reach C hNF hWF hg0_val hg1_val R3 none
          (8 + C.gates.length)
          (fun _ h => by cases h) hcnt_le1
          C.output (by omega) (by omega)
          (fun _ => ⟨false, fun u => by rw [hg0_val, R3_g0_const u]⟩)
        apply Expr.not_p4_or_not_p4 e he_ro
        left
        intro u
        rw [he_eval u]
        have : wireVal C (R3.emb u) C.output = C.eval (List.ofFn (R3.emb u)) := rfl
        rw [this, heval (R3.emb u), R3.pm3_eq_p4 u]
      ·
        have hcnt9 : allIns.count 9 = 0 := by omega
        have hex1 : ∑ w ∈ Req, (allIns.count w - 1) = 1 := by omega
        obtain ⟨wstar, hwstarReq, hwstarPos⟩ : ∃ wstar ∈ Req, 0 < allIns.count wstar - 1 := by
          by_contra hall
          push Not at hall
          have hz : ∑ w ∈ Req, (allIns.count w - 1) = 0 :=
            Finset.sum_eq_zero (fun w hw => Nat.eq_zero_of_le_zero (hall w hw))
          omega
        have hwstar_ne9 : wstar ≠ 9 := (Finset.mem_erase.mp hwstarReq).1
        have hwstar_lt : wstar < 8 + C.gates.length := by
          have := Finset.mem_range.mp (Finset.mem_erase.mp hwstarReq).2
          omega
        have hcnt_other : ∀ u < 8 + C.gates.length, u ≠ wstar →
            ((C.gates.drop 2).flatMap (·.inputs)).count u ≤ 1 := by
          intro u hu hune
          rw [hdrop]
          change allIns.count u ≤ 1
          by_cases hu9 : u = 9
          · subst hu9; omega
          · have huReq : u ∈ Req := Finset.mem_erase.mpr ⟨hu9, Finset.mem_range.mpr (by omega)⟩
            have hle := Finset.add_sum_erase Req (fun w => allIns.count w - 1) hwstarReq
            have hsub : allIns.count u - 1 ≤ ∑ w ∈ Req.erase wstar, (allIns.count w - 1) :=
              Finset.single_le_sum (f := fun w => allIns.count w - 1) (fun _ _ => Nat.zero_le _)
                (Finset.mem_erase.mpr ⟨hune, huReq⟩)
            omega
        have hcnt9_drop : ((C.gates.drop 2).flatMap (·.inputs)).count 9 = 0 := by
          rw [hdrop]; exact hcnt9
        let S : Finset (Fin 9) := Finset.univ.filter (fun i : Fin 9 => i.val ∈ reach C hWF none wstar)
        have hcard_one : ∀ (R : Restr),
            (Finset.univ.filter (fun i : Fin 4 => R.V i ∈ S)).card = 1 := by
          intro R
          let A : Finset (Fin 4) := Finset.univ.filter (fun i : Fin 4 => R.V i ∈ S)
          change A.card = 1
          have hAle4 : A.card ≤ 4 := le_trans (Finset.card_le_univ A) (by simp)
          have hmemA : ∀ i : Fin 4, i ∈ A ↔ (R.V i).val ∈ reach C hWF none wstar := by
            intro i; simp [A, S]
          have h9_none : 9 ∉ reach C hWF none wstar :=
            nine_not_in_reach_of_count_zero C hWF none hcnt9_drop hwstar_ne9
          have h9_some : 9 ∉ reach C hWF (some wstar) (8 + C.gates.length) :=
            nine_not_in_reach_of_count_zero C hWF (some wstar) hcnt9_drop (by omega)
          have hdisj_so := reach_disjoint_sub_outer C hWF wstar hwstar_lt hcnt_other
          have hnot_in_outer : ∀ i ∈ A,
              (R.V i).val ∈ reach C hWF (some wstar) (8 + C.gates.length) →
              some (R.V i).val ≠ some wstar → False := by
            intro i hi hm hns
            have hne : (R.V i).val ≠ wstar := fun h => hns (congrArg some h)
            have h1 : (R.V i).val ∈ (reach C hWF none wstar).erase wstar :=
              Finset.mem_erase.mpr ⟨hne, (hmemA i).mp hi⟩
            have h2 : (R.V i).val ∈ (reach C hWF (some wstar) (8 + C.gates.length)).erase wstar :=
              Finset.mem_erase.mpr ⟨hne, hm⟩
            exact Finset.disjoint_left.mp hdisj_so h1 h2

          have hne0 : A.card ≠ 0 := by
            intro h0
            have hAempty : A = ∅ := Finset.card_eq_zero.mp h0
            have hw_const : ∀ u, wireVal C (R.emb u) wstar = wireVal C (R.emb (fun _ => false)) wstar := by
              intro u
              apply eval_depends_only_on_reach C hWF hg0_val hg1_val R none wstar (by omega)
                (fun h => False.elim (h9_none h))
              · intro i hi _
                have hiA : i ∈ A := (hmemA i).mpr hi
                rw [hAempty] at hiA
                exact absurd hiA (by simp)
              · intro _ h; cases h
            obtain ⟨e, he_ro, _, he_eval⟩ := buildExpr_of_reach C hNF hWF hg0_val hg1_val R
              (some wstar) (8 + C.gates.length)
              (fun w hw => by
                cases hw
                exact ⟨wireVal C (R.emb (fun _ => false)) wstar, hw_const⟩)
              (fun u hu hns => hcnt_other u hu (fun heq => hns (congrArg some heq)))
              (8 + C.gates.length) le_rfl (by omega)
              (fun h => False.elim (h9_some h))
            apply Expr.not_p4_or_not_p4 e he_ro
            left
            intro u
            rw [he_eval u]
            have ho : 8 + C.gates.length = C.output := by omega
            rw [ho]
            exact (heval (R.emb u)).trans (R.pm3_eq_p4 u)

          have hne4 : A.card ≠ 4 := by
            intro h4
            have hAuniv : A = Finset.univ := Finset.eq_univ_of_card A (by simpa using h4)
            have hout_det : ∀ u1 u2,
                wireVal C (R.emb u1) wstar = wireVal C (R.emb u2) wstar → p4 u1 = p4 u2 := by
              intro u1 u2 hweq
              have hval := eval_depends_only_on_reach C hWF hg0_val hg1_val R (some wstar)
                (8 + C.gates.length) (by omega) (fun h => False.elim (h9_some h)) u1 u2
                (fun i hi hni => False.elim (hnot_in_outer i (by rw [hAuniv]; exact Finset.mem_univ i) hi hni))
                (fun w hw _ => by cases hw; exact hweq)
              have ho : 8 + C.gates.length = C.output := by omega
              rw [ho] at hval
              change C.eval (List.ofFn (R.emb u1)) = C.eval (List.ofFn (R.emb u2)) at hval
              rw [heval, heval, R.pm3_eq_p4, R.pm3_eq_p4] at hval
              exact hval
            obtain ⟨e, he_ro, _, he_eval⟩ := buildExpr_of_reach C hNF hWF hg0_val hg1_val R none
              wstar
              (fun _ h => by cases h)
              (fun u hu _ => hcnt_other u (by omega) (by omega))
              wstar le_rfl (by omega)
              (fun h => False.elim (h9_none h))
            obtain ⟨u0, u1, hu01⟩ := p4_nonconst
            have hwne : wireVal C (R.emb u0) wstar ≠ wireVal C (R.emb u1) wstar :=
              fun heq => hu01 (hout_det u0 u1 heq)
            apply Expr.not_p4_or_not_p4 e he_ro
            cases h0b : wireVal C (R.emb u0) wstar <;> cases h1b : wireVal C (R.emb u1) wstar
            · exact absurd (h0b.trans h1b.symm) hwne
            · cases hp0 : p4 u0 <;> cases hp1 : p4 u1
              · exact absurd (hp0.trans hp1.symm) hu01
              · left; intro u; rw [he_eval u]
                cases hwu : wireVal C (R.emb u) wstar
                · rw [← hp0, hout_det u u0 (hwu.trans h0b.symm)]
                · rw [← hp1, hout_det u u1 (hwu.trans h1b.symm)]
              · right; intro u; rw [he_eval u]
                cases hwu : wireVal C (R.emb u) wstar
                · rw [hout_det u u0 (hwu.trans h0b.symm), hp0]; rfl
                · rw [hout_det u u1 (hwu.trans h1b.symm), hp1]; rfl
              · exact absurd (hp0.trans hp1.symm) hu01
            · cases hp0 : p4 u0 <;> cases hp1 : p4 u1
              · exact absurd (hp0.trans hp1.symm) hu01
              · right; intro u; rw [he_eval u]
                cases hwu : wireVal C (R.emb u) wstar
                · rw [hout_det u u1 (hwu.trans h1b.symm), hp1]; rfl
                · rw [hout_det u u0 (hwu.trans h0b.symm), hp0]; rfl
              · left; intro u; rw [he_eval u]
                cases hwu : wireVal C (R.emb u) wstar
                · rw [← hp1, hout_det u u1 (hwu.trans h1b.symm)]
                · rw [← hp0, hout_det u u0 (hwu.trans h0b.symm)]
              · exact absurd (hp0.trans hp1.symm) hu01
            · exact absurd (h0b.trans h1b.symm) hwne

          have hnot23 : ¬ (2 ≤ A.card ∧ A.card ≤ 3) := by
            rintro ⟨h2, h3⟩
            obtain ⟨u1, u2, u3, ⟨v12, hv12⟩, ⟨v13, hv13⟩, ⟨v23, hv23⟩⟩ := p4_no_module A h2 h3
            let h : (Fin 4 → Bool) → Bool := fun u => wireVal C (R.emb u) wstar
            have h_eq_mix : ∀ u v, h (mix A u v) = h u := by
              intro u v
              apply eval_depends_only_on_reach C hWF hg0_val hg1_val R none wstar (by omega)
                (fun h9 => False.elim (h9_none h9))
              · intro i hi _
                have hiA : i ∈ A := (hmemA i).mpr hi
                simp [mix, hiA]
              · intro _ h; cases h
            have h_det : ∀ x1 x2 v, h x1 = h x2 →
                p4 (mix A x1 v) = p4 (mix A x2 v) := by
              intro x1 x2 v heqh
              have hval := eval_depends_only_on_reach C hWF hg0_val hg1_val R (some wstar)
                (8 + C.gates.length) (by omega) (fun h9 => False.elim (h9_some h9))
                (mix A x1 v) (mix A x2 v)
                (fun i hi hni => by
                  by_cases hiA : i ∈ A
                  · exact False.elim (hnot_in_outer i hiA hi hni)
                  · simp [mix, hiA])
                (fun w hw _ => by
                  cases hw
                  exact (h_eq_mix x1 v).trans (heqh.trans (h_eq_mix x2 v).symm))
              have ho : 8 + C.gates.length = C.output := by omega
              rw [ho] at hval
              change C.eval (List.ofFn (R.emb (mix A x1 v))) =
                     C.eval (List.ofFn (R.emb (mix A x2 v))) at hval
              rw [heval, heval, R.pm3_eq_p4, R.pm3_eq_p4] at hval
              exact hval
            cases h1b : h u1 <;> cases h2b : h u2 <;> cases h3b : h u3
            · exact hv12 (h_det u1 u2 v12 (h1b.trans h2b.symm))
            · exact hv12 (h_det u1 u2 v12 (h1b.trans h2b.symm))
            · exact hv13 (h_det u1 u3 v13 (h1b.trans h3b.symm))
            · exact hv23 (h_det u2 u3 v23 (h2b.trans h3b.symm))
            · exact hv23 (h_det u2 u3 v23 (h2b.trans h3b.symm))
            · exact hv13 (h_det u1 u3 v13 (h1b.trans h3b.symm))
            · exact hv12 (h_det u1 u2 v12 (h1b.trans h2b.symm))
            · exact hv12 (h_det u1 u2 v12 (h1b.trans h2b.symm))
          omega
        exact no_hitting_set_card_one S
          (hcard_one R1) (hcard_one R2) (hcard_one R3) (hcard_one R4) (hcard_one R5)

end PEqualNP.Outside.L_meta_27627

theorem PEqualNP.Outside.L_meta_27627 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 9]⟩)) := by
  exact PEqualNP.Outside.L_meta_27627.main_proof
