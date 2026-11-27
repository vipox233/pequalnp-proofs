import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_286_aux

open PEqualNP.ProofComplexity

private def cl {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (e : Fin m) (a : Bool) : Clause (Fin n) :=
  {(left e, !a), (right e, a ^^ sign e)}

private def negWalk {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (k : ℕ) : Prop :=
  ∃ (v : ℕ → Fin n) (edge : ℕ → Fin m), v 0 = v k ∧
    Odd (((Finset.range k).filter (fun j => sign (edge j) = true)).card) ∧
    ∀ j < k, (v j = left (edge j) ∧ v (j + 1) = right (edge j)) ∨
      (v j = right (edge j) ∧ v (j + 1) = left (edge j))

private theorem foldl_xor_init (b : Bool) (l : List Bool) :
    l.foldl Bool.xor b = (b ^^ l.foldl Bool.xor false) := by
  induction l generalizing b with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (b ^^ x), ih (false ^^ x), Bool.false_xor, Bool.xor_assoc]

private theorem foldl_xor_ofFn_succ (f : ℕ → Bool) (k : ℕ) :
    (List.ofFn (fun j : Fin (k + 1) => f j.val)).foldl Bool.xor false =
      ((List.ofFn (fun j : Fin k => f j.val)).foldl Bool.xor false ^^ f k) := by
  rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

private theorem xor_count_odd_iff (f : ℕ → Bool) :
    ∀ k : ℕ, (List.ofFn (fun j : Fin k => f j.val)).foldl Bool.xor false = true ↔
      Odd (((Finset.range k).filter (fun j => f j = true)).card) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [foldl_xor_ofFn_succ, Finset.range_add_one, Finset.filter_insert]
    by_cases hfk : f k = true
    · simp only [hfk, ↓reduceIte, Bool.xor_true]
      rw [Finset.card_insert_of_notMem (by simp), Nat.odd_add_one, ← ih]
      cases (List.ofFn (fun j : Fin k => f j.val)).foldl Bool.xor false <;> simp
    · have hfk' : f k = false := Bool.eq_false_iff.mpr hfk
      simp only [hfk', Bool.false_eq_true, ↓reduceIte, Bool.xor_false]
      exact ih

private theorem val_step_xor (f : ℕ → Bool) (val : ℕ → Bool) (start : Bool)
    (h0 : val 0 = start) (hstep : ∀ j, j < k → val (j + 1) = (val j ^^ f j)) :
    ∀ t ≤ k, val t = (start ^^ (List.ofFn (fun j : Fin t => f j.val)).foldl Bool.xor false) := by
  intro t ht
  induction t with
  | zero => simp [h0]
  | succ t ih =>
    have h1 := ih (by omega)
    rw [hstep t (by omega), h1, foldl_xor_ofFn_succ, Bool.xor_assoc]

private theorem mod_add_sub_cancel {k r j : ℕ} (hr : r < k) (hj : j < k) :
    (r + (j + k - r) % k) % k = j := by
  by_cases h : r ≤ j
  · have e1 : j + k - r = (j - r) + k := by omega
    rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : j - r < k)]
    have e2 : r + (j - r) = j := by omega
    rw [e2, Nat.mod_eq_of_lt hj]
  · rw [Nat.mod_eq_of_lt (by omega : j + k - r < k)]
    have e2 : r + (j + k - r) = j + k := by omega
    rw [e2, Nat.add_mod_right, Nat.mod_eq_of_lt hj]

private theorem isResolvent_pair {V : Type} [DecidableEq V]
    {a b c : Literal V} {v : V} {s : Bool}
    (hb : b = (v, s)) (hne1 : a ≠ (v, s)) (hne2 : c ≠ (v, !s)) :
    IsResolvent ({a, b} : Clause V) ({(v, !s), c} : Clause V) ({a, c} : Clause V) ∨
    IsResolvent ({(v, !s), c} : Clause V) ({a, b} : Clause V) ({a, c} : Clause V) := by
  subst hb
  cases s
  · right
    refine ⟨v, by simp, by simp, ?_⟩
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase]
    constructor
    · rintro (rfl | rfl)
      · right; exact ⟨hne1, Or.inl rfl⟩
      · left; exact ⟨hne2, Or.inr rfl⟩
    · rintro (⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩)
      · exact absurd h2 h1
      · exact Or.inr h2
      · exact Or.inl h2
      · exact absurd h2 h1
  · left
    refine ⟨v, by simp, by simp, ?_⟩
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase]
    constructor
    · rintro (rfl | rfl)
      · left; exact ⟨hne1, Or.inl rfl⟩
      · right; exact ⟨hne2, Or.inr rfl⟩
    · rintro (⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩)
      · exact Or.inl h2
      · exact absurd h2 h1
      · exact absurd h2 h1
      · exact Or.inr h2

private theorem derive_unit_of_walk {n m : ℕ} {left right : Fin m → Fin n} {sign : Fin m → Bool}
    {g : ℕ} (hg1 : 1 ≤ g) (hmin : ∀ k < g, ¬ negWalk left right sign k)
    {H : Set (Clause (Fin n))} {root : Fin n} {start : Bool}
    {v : ℕ → Fin n} {edge : ℕ → Fin m} {val : ℕ → Bool}
    (hv0 : v 0 = root) (hvg : v g = root) (hval0 : val 0 = start) (hvalg : val g = !start)
    (hstep : ∀ j < g,
      ((v j = left (edge j) ∧ v (j + 1) = right (edge j)) ∨
        (v j = right (edge j) ∧ v (j + 1) = left (edge j))) ∧
      val (j + 1) = (val j ^^ sign (edge j)) ∧
      ({(v j, !(val j)), (v (j + 1), val (j + 1))} : Clause (Fin n)) ∈ H)
    {base : List (Clause (Fin n))} (hbase : IsDerivation H base) :
    ∃ π : List (Clause (Fin n)),
      IsDerivation H π ∧ (∀ C ∈ base, C ∈ π) ∧
      ({(root, !start)} : Clause (Fin n)) ∈ π ∧
      π.length = base.length + (2 * g - 1) := by
  have haux : ∀ k, 1 ≤ k → k ≤ g →
      ∃ π : List (Clause (Fin n)),
        IsDerivation H π ∧ (∀ C ∈ base, C ∈ π) ∧
        ({(root, !start), (v k, val k)} : Clause (Fin n)) ∈ π ∧
        π.length = base.length + (2 * k - 1) := by
    intro k hk1 hkg
    induction k with
    | zero => omega
    | succ k ih =>
      by_cases hk0 : k = 0
      · subst hk0
        have h0 := (hstep 0 (by omega)).2.2
        rw [hv0, hval0] at h0
        refine ⟨{(root, !start), (v 1, val 1)} :: base, IsDerivation.ax hbase h0,
          fun C hC => List.mem_cons_of_mem _ hC, List.mem_cons_self, by simp⟩
      · obtain ⟨π, hπ, hsub, hmem, hlen⟩ := ih (by omega) (by omega)
        have hck : ({(v k, !(val k)), (v (k + 1), val (k + 1))} : Clause (Fin n)) ∈ H :=
          (hstep k (by omega)).2.2
        have hne1 : ((root, !start) : Literal (Fin n)) ≠ (v k, val k) := by
          intro heq
          have hvk : v k = root := (Prod.mk.inj heq).1.symm
          have hvalk : val k = !start := (Prod.mk.inj heq).2.symm
          have hxor := val_step_xor (fun j => sign (edge j)) val start hval0
            (fun j hj => (hstep j (by omega)).2.1) k (by omega)
          rw [hvalk] at hxor
          have htrue : (List.ofFn (fun j : Fin k => sign (edge j.val))).foldl Bool.xor false = true := by
            revert hxor
            generalize (List.ofFn (fun j : Fin k => sign (edge j.val))).foldl Bool.xor false = x
            cases start <;> cases x <;> decide
          have hodd := (xor_count_odd_iff (fun j => sign (edge j)) k).mp htrue
          exact hmin k (by omega) ⟨v, edge, by rw [hv0, hvk], hodd, fun j hj => (hstep j (by omega)).1⟩
        have hne2 : ((v (k + 1), val (k + 1)) : Literal (Fin n)) ≠ (v k, !(val k)) := by
          intro heq
          have hv1 : v (k + 1) = v k := (Prod.mk.inj heq).1
          have hval1 : val (k + 1) = !(val k) := (Prod.mk.inj heq).2
          have hsk : sign (edge k) = true := by
            have hst := (hstep k (by omega)).2.1
            rw [hval1] at hst
            revert hst
            generalize val k = a
            generalize sign (edge k) = b
            cases a <;> cases b <;> decide
          have hneg1 : negWalk left right sign 1 := by
            refine ⟨fun _ => v k, fun _ => edge k, rfl, ?_, ?_⟩
            · simp [hsk]
            · intro j hj
              have : j = 0 := by omega
              subst this
              have hk' := (hstep k (by omega)).1
              rw [hv1] at hk'
              exact hk'
          exact hmin 1 (by omega) hneg1
        have hres := isResolvent_pair (v := v k) (s := val k) rfl hne1 hne2
        let π1 := ({(v k, !(val k)), (v (k + 1), val (k + 1))} : Clause (Fin n)) :: π
        have hπ1 : IsDerivation H π1 := IsDerivation.ax hπ hck
        have hπ2 : IsDerivation H (({(root, !start), (v (k + 1), val (k + 1))} : Clause (Fin n)) :: π1) := by
          rcases hres with hr | hr
          · exact IsDerivation.res hπ1 (List.mem_cons_of_mem _ hmem) List.mem_cons_self hr
          · exact IsDerivation.res hπ1 List.mem_cons_self (List.mem_cons_of_mem _ hmem) hr
        refine ⟨_, hπ2, fun C hC => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hsub C hC)),
          List.mem_cons_self, ?_⟩
        simp only [π1, List.length_cons, hlen]
        omega
  obtain ⟨π, hπ, hsub, hmem, hlen⟩ := haux g hg1 le_rfl
  rw [hvg, hvalg] at hmem
  have hpair : ({(root, !start), (root, !start)} : Clause (Fin n)) = {(root, !start)} := by
    ext x; simp
  rw [hpair] at hmem
  exact ⟨π, hπ, hsub, hmem, hlen⟩

private theorem backwards_dir {n m : ℕ} {left right : Fin m → Fin n} {sign : Fin m → Bool}
    {g : ℕ} (hg : negWalk left right sign g) (hmin : ∀ k < g, ¬ negWalk left right sign k)
    {H : Set (Clause (Fin n))}
    (hw : ∃ root : Fin n, ∀ start : Bool,
      ∃ (v : ℕ → Fin n) (edge : ℕ → Fin m) (val : ℕ → Bool),
        v 0 = root ∧ v g = root ∧ val 0 = start ∧ val g = !start ∧
        ∀ j < g,
          ((v j = left (edge j) ∧ v (j + 1) = right (edge j)) ∨
            (v j = right (edge j) ∧ v (j + 1) = left (edge j))) ∧
          val (j + 1) = (val j ^^ sign (edge j)) ∧
          ({(v j, !(val j)), (v (j + 1), val (j + 1))} : Clause (Fin n)) ∈ H) :
    ∃ π, IsRefutation H π ∧ π.length + 1 ≤ 4 * g := by
  have hg1 : 1 ≤ g := by
    by_contra h0
    have hg0 : g = 0 := by omega
    subst hg0
    rcases hg with ⟨_, _, _, hodd, _⟩
    simp at hodd
  obtain ⟨root, hroot⟩ := hw
  obtain ⟨vF, eF, valF, hvF0, hvFg, hvalF0, hvalFg, hsF⟩ := hroot false
  obtain ⟨vT, eT, valT, hvT0, hvTg, hvalT0, hvalTg, hsT⟩ := hroot true
  obtain ⟨π1, hπ1, _, hmemT, hlen1⟩ :=
    derive_unit_of_walk hg1 hmin hvF0 hvFg hvalF0 hvalFg hsF (IsDerivation.nil (F := H))
  obtain ⟨π2, hπ2, hsub2, hmemF, hlen2⟩ :=
    derive_unit_of_walk hg1 hmin hvT0 hvTg hvalT0 hvalTg hsT hπ1
  have hmemT2 : ({(root, true)} : Clause (Fin n)) ∈ π2 := hsub2 _ (by simpa using hmemT)
  have hmemF2 : ({(root, false)} : Clause (Fin n)) ∈ π2 := by simpa using hmemF
  have hres0 : IsResolvent ({(root, true)} : Clause (Fin n)) ({(root, false)} : Clause (Fin n)) ∅ :=
    ⟨root, by simp, by simp, by simp⟩
  refine ⟨∅ :: π2, ⟨IsDerivation.res hπ2 hmemT2 hmemF2 hres0, List.mem_cons_self⟩, ?_⟩
  simp only [List.length_cons, hlen2, hlen1, List.length_nil]
  omega

private theorem cl_sat_of_balanced {n m : ℕ} {left right : Fin m → Fin n} {sign : Fin m → Bool}
    {e : Fin m} {a : Bool} {β : Fin n → Bool}
    (h : β (right e) = (β (left e) ^^ sign e)) :
    ClauseSat β (cl left right sign e a) := by
  unfold cl ClauseSat
  by_cases h1 : β (left e) = !a
  · exact ⟨(left e, !a), by simp, h1⟩
  · refine ⟨(right e, a ^^ sign e), by simp, ?_⟩
    dsimp only
    rw [h]
    revert h1
    generalize β (left e) = x
    cases x <;> cases a <;> cases sign e <;> decide

private theorem cl_not_both_falsified {n m : ℕ} {left right : Fin m → Fin n} {sign : Fin m → Bool}
    {e : Fin m} {a : Bool} (β : Fin n → Bool) :
    ClauseSat β (cl left right sign e a) ∨ ClauseSat (fun x => !(β x)) (cl left right sign e a) := by
  unfold cl ClauseSat
  by_cases h1 : β (left e) = !a
  · left; exact ⟨(left e, !a), by simp, h1⟩
  · right; refine ⟨(left e, !a), by simp, ?_⟩
    dsimp only
    revert h1
    generalize β (left e) = x
    cases x <;> cases a <;> decide

private def SPath {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (P : Fin m → Prop) (k : ℕ) (u w : Fin n) (s : Bool) : Prop :=
  ∃ (v : ℕ → Fin n) (edge : ℕ → Fin m),
    v 0 = u ∧ v k = w ∧
    (List.ofFn (fun j : Fin k => sign (edge j.val))).foldl Bool.xor false = s ∧
    ∀ j < k, P (edge j) ∧
      ((v j = left (edge j) ∧ v (j + 1) = right (edge j)) ∨
        (v j = right (edge j) ∧ v (j + 1) = left (edge j)))

private def SReach {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (P : Fin m → Prop) (u w : Fin n) (s : Bool) : Prop :=
  ∃ k, SPath left right sign P k u w s

private theorem sreach_refl' {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (P : Fin m → Prop) (hm : 0 < m) (u : Fin n) : SReach left right sign P u u false :=
  ⟨0, fun _ => u, fun _ => ⟨0, hm⟩, rfl, rfl, rfl, fun _ hj => by omega⟩

private theorem sreach_step {n m : ℕ} {left right : Fin m → Fin n} {sign : Fin m → Bool}
    {P : Fin m → Prop} {e : Fin m} (he : P e) {u w : Fin n}
    (hinc : (u = left e ∧ w = right e) ∨ (u = right e ∧ w = left e)) :
    SReach left right sign P u w (sign e) := by
  refine ⟨1, fun j => if j = 0 then u else w, fun _ => e, rfl, by simp, by simp, ?_⟩
  intro j hj
  have hj0 : j = 0 := by omega
  subst hj0
  exact ⟨he, hinc⟩

private theorem sreach_symm {n m : ℕ} {left right : Fin m → Fin n} {sign : Fin m → Bool}
    {P : Fin m → Prop} {u w : Fin n} {s : Bool}
    (h : SReach left right sign P u w s) : SReach left right sign P w u s := by
  obtain ⟨k, v, edge, h0, hk, hxor, hstep⟩ := h
  refine ⟨k, fun j => v (k - j), fun j => edge (k - 1 - j), ?_, ?_, ?_, ?_⟩
  · simp [hk]
  · simp [h0]
  · rw [← hxor]
    have hrev : ∀ t (f : ℕ → Bool),
        (List.ofFn (fun j : Fin t => f (t - 1 - j.val))).foldl Bool.xor false =
        (List.ofFn (fun j : Fin t => f j.val)).foldl Bool.xor false := by
      intro t f
      induction t generalizing f with
      | zero => rfl
      | succ t ih =>
        have hL : (List.ofFn (fun j : Fin (t + 1) => f (t + 1 - 1 - j.val))).foldl Bool.xor false =
            (f t ^^ (List.ofFn (fun j : Fin t => f (t - 1 - j.val))).foldl Bool.xor false) := by
          rw [List.ofFn_succ, List.foldl_cons, foldl_xor_init]
          simp only [Fin.val_zero, Nat.add_sub_cancel, Nat.sub_zero, Bool.false_xor]
          congr 2
          apply congrArg List.ofFn
          funext i
          congr 1
          simp only [Fin.val_succ]
          omega
        rw [hL, foldl_xor_ofFn_succ, ih f, Bool.xor_comm]
    exact hrev k (fun j => sign (edge j))
  · intro j hj
    dsimp only
    have h1 := hstep (k - 1 - j) (by omega)
    have he1 : k - 1 - j + 1 = k - j := by omega
    have he2 : k - (j + 1) = k - 1 - j := by omega
    rw [he2]
    refine ⟨h1.1, ?_⟩
    rcases h1.2 with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · right; exact ⟨by rw [← he1]; exact hr, hl⟩
    · left; exact ⟨by rw [← he1]; exact hl, hr⟩

private theorem sreach_trans {n m : ℕ} {left right : Fin m → Fin n} {sign : Fin m → Bool}
    {P : Fin m → Prop} {u w z : Fin n} {s1 s2 : Bool}
    (h1 : SReach left right sign P u w s1) (h2 : SReach left right sign P w z s2) :
    SReach left right sign P u z (s1 ^^ s2) := by
  obtain ⟨k1, v1, e1, hv10, hv1k, hx1, hs1⟩ := h1
  obtain ⟨k2, v2, e2, hv20, hv2k, hx2, hs2⟩ := h2
  refine ⟨k1 + k2,
    fun j => if j ≤ k1 then v1 j else v2 (j - k1),
    fun j => if j < k1 then e1 j else e2 (j - k1),
    ?_, ?_, ?_, ?_⟩
  · simp [hv10]
  · by_cases hk2 : k2 = 0
    · subst hk2; simp [hv1k, ← hv20, hv2k]
    · have : ¬ k1 + k2 ≤ k1 := by omega
      simp [this, hv2k]
  · have hcat : List.ofFn (fun j : Fin (k1 + k2) => sign (if j.val < k1 then e1 j.val else e2 (j.val - k1))) =
        List.ofFn (fun j : Fin k1 => sign (e1 j.val)) ++ List.ofFn (fun j : Fin k2 => sign (e2 j.val)) := by
      apply List.ext_getElem
      · simp
      · intro i hi1 hi2
        simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn]
        split_ifs with hlt <;> simp
    rw [hcat, List.foldl_append, hx1, foldl_xor_init, hx2]
  · intro j hj
    by_cases hlt : j < k1
    · simp only [hlt, ↓reduceIte, show j ≤ k1 by omega, show j + 1 ≤ k1 by omega]
      exact hs1 j hlt
    · have hlt2 : j - k1 < k2 := by omega
      have hge1 : ¬ j + 1 ≤ k1 := by omega
      simp only [hlt, ↓reduceIte, hge1]
      have hsub : j + 1 - k1 = j - k1 + 1 := by omega
      rw [hsub]
      by_cases hjk : j = k1
      · subst hjk
        simp only [le_refl, ↓reduceIte, Nat.sub_self, zero_add]
        rw [hv1k, ← hv20]
        exact hs2 0 (by omega)
      · have hge : ¬ j ≤ k1 := by omega
        simp only [hge, ↓reduceIte]
        exact hs2 (j - k1) hlt2

private theorem exists_negWalk_of_not_balanced {n m : ℕ} {left right : Fin m → Fin n}
    {sign : Fin m → Bool} {P : Fin m → Prop} (hm : 0 < m)
    (hunbal : ¬ ∃ β : Fin n → Bool, ∀ e, P e → β (right e) = (β (left e) ^^ sign e)) :
    ∃ k u, SPath left right sign P k u u true := by
  classical
  by_contra hno
  push Not at hno
  have huniq : ∀ u w s1 s2, SReach left right sign P u w s1 → SReach left right sign P u w s2 → s1 = s2 := by
    intro u w s1 s2 h1 h2
    by_contra hne
    have htr := sreach_trans h1 (sreach_symm h2)
    have hst : (s1 ^^ s2) = true := by revert hne; cases s1 <;> cases s2 <;> decide
    rw [hst] at htr
    obtain ⟨k, hk⟩ := htr
    exact hno k u hk
  let Comp (u : Fin n) : Finset (Fin n) :=
    Finset.univ.filter (fun w => ∃ s, SReach left right sign P u w s)
  have hmemC : ∀ u, u ∈ Comp u := fun u =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ u, false, sreach_refl' left right sign P hm u⟩
  have hCeq : ∀ u w s, SReach left right sign P u w s → Comp u = Comp w := by
    intro u w s h
    ext z
    simp only [Comp, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨s', h'⟩; exact ⟨s ^^ s', sreach_trans (sreach_symm h) h'⟩
    · rintro ⟨s', h'⟩; exact ⟨s ^^ s', sreach_trans h h'⟩
  let rep (u : Fin n) : Fin n := (Comp u).min' ⟨u, hmemC u⟩
  have hrep_reach : ∀ u, ∃ s, SReach left right sign P (rep u) u s := by
    intro u
    have hmem : rep u ∈ Comp u := Finset.min'_mem _ _
    obtain ⟨s, hs⟩ := (Finset.mem_filter.mp hmem).2
    exact ⟨s, sreach_symm hs⟩
  let β : Fin n → Bool := fun u => Classical.choose (hrep_reach u)
  apply hunbal
  refine ⟨β, fun e he => ?_⟩
  have hstep := sreach_step (left := left) (right := right) (sign := sign) he (Or.inl ⟨rfl, rfl⟩)
  have hrep_eq : rep (left e) = rep (right e) := by
    dsimp only [rep]
    congr 1
    exact hCeq (left e) (right e) (sign e) hstep
  have hL : SReach left right sign P (rep (left e)) (left e) (β (left e)) :=
    Classical.choose_spec (hrep_reach (left e))
  have hR : SReach left right sign P (rep (right e)) (right e) (β (right e)) :=
    Classical.choose_spec (hrep_reach (right e))
  rw [← hrep_eq] at hR
  exact huniq (rep (left e)) (right e) (β (right e)) (β (left e) ^^ sign e) hR (sreach_trans hL hstep)

private theorem minimal_neg_cycle {n m : ℕ} {left right : Fin m → Fin n}
    {sign : Fin m → Bool} {P : Fin m → Prop}
    (hex : ∃ k u, SPath left right sign P k u u true) :
    ∃ (k : ℕ) (v : ℕ → Fin n) (edge : ℕ → Fin m),
      1 ≤ k ∧
      SPath left right sign P k (v 0) (v 0) true ∧
      v 0 = v k ∧
      Odd (((Finset.range k).filter (fun j => sign (edge j) = true)).card) ∧
      (∀ j < k, P (edge j) ∧
        ((v j = left (edge j) ∧ v (j + 1) = right (edge j)) ∨
          (v j = right (edge j) ∧ v (j + 1) = left (edge j)))) ∧
      (∀ a < k, ∀ b < k, v a = v b → a = b) ∧
      (∀ a < k, ∀ b < k, edge a = edge b → a = b) := by
  classical
  have hex' : ∃ k, ∃ u, SPath left right sign P k u u true := hex
  generalize hk_def : Nat.find hex' = k
  have hspec : ∃ u, SPath left right sign P k u u true := hk_def ▸ Nat.find_spec hex'
  have hmin_k : ∀ t < k, ¬ ∃ u, SPath left right sign P t u u true := by
    intro t ht
    rw [← hk_def] at ht
    exact Nat.find_min hex' ht
  obtain ⟨u, v, edge, hv0, hvk, hxor, hstep⟩ := hspec
  have hk1 : 1 ≤ k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    subst hk0
    simp at hxor
  have hodd : Odd (((Finset.range k).filter (fun j => sign (edge j) = true)).card) :=
    (xor_count_odd_iff (fun j => sign (edge j)) k).mp hxor
  have hv_inj : ∀ a < k, ∀ b < k, v a = v b → a = b := by
    intro a ha b hb hab
    by_contra hne
    wlog hlt : a < b generalizing a b
    · exact this b hb a ha hab.symm (Ne.symm hne) (by omega)
    let d := b - a
    let t := k - d
    have hd_lt : d < k := by omega
    have ht_lt : t < k := by omega
    let idxE : ℕ → ℕ := fun j => if j < a then j else j + d
    let s1 := (List.ofFn (fun j : Fin d => sign (edge (a + j.val)))).foldl Bool.xor false
    let s2 := (List.ofFn (fun j : Fin t => sign (edge (idxE j.val)))).foldl Bool.xor false
    have hcard :
        ((Finset.range d).filter (fun j => sign (edge (a + j)) = true)).card +
        ((Finset.range t).filter (fun j => sign (edge (idxE j)) = true)).card =
        ((Finset.range k).filter (fun j => sign (edge j) = true)).card := by
      let A := (Finset.range d).image (fun j => a + j)
      let B := (Finset.range t).image idxE
      have hA_inj : Set.InjOn (fun j => a + j) (Finset.range d) := fun _ _ _ _ h => by dsimp only at h; omega
      have hB_inj : Set.InjOn idxE (Finset.range t) := by
        intro x hx y hy hxy
        simp only [Finset.mem_coe, Finset.mem_range] at hx hy
        simp only [idxE] at hxy
        split_ifs at hxy <;> omega
      have hAB_disj : Disjoint A B := by
        rw [Finset.disjoint_left]
        intro z hzA hzB
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hzA
        obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp hzB
        simp only [Finset.mem_range] at hi hj
        simp only [idxE] at hje
        split_ifs at hje <;> omega
      have hAB_eq : A ∪ B = Finset.range k := by
        ext z
        simp only [A, B, Finset.mem_union, Finset.mem_image, Finset.mem_range]
        constructor
        · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
          · omega
          · dsimp only [idxE]; split_ifs <;> omega
        · intro hz
          by_cases hza : z < a
          · right; exact ⟨z, by omega, by simp [idxE, hza]⟩
          · by_cases hzb : z < b
            · left; exact ⟨z - a, by omega, by omega⟩
            · right; refine ⟨z - d, by omega, ?_⟩
              have : ¬ z - d < a := by omega
              simp [idxE, this]; omega
      have h1 : ((Finset.range d).filter (fun j => sign (edge (a + j)) = true)).card =
          (A.filter (fun z => sign (edge z) = true)).card := by
        rw [← Finset.card_image_of_injOn (hA_inj.mono (Finset.filter_subset _ _))]
        congr 1; ext z
        simp only [A, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨i, ⟨hi, hs⟩, rfl⟩; exact ⟨⟨i, hi, rfl⟩, hs⟩
        · rintro ⟨⟨i, hi, rfl⟩, hs⟩; exact ⟨i, ⟨hi, hs⟩, rfl⟩
      have h2 : ((Finset.range t).filter (fun j => sign (edge (idxE j)) = true)).card =
          (B.filter (fun z => sign (edge z) = true)).card := by
        rw [← Finset.card_image_of_injOn (hB_inj.mono (Finset.filter_subset _ _))]
        congr 1; ext z
        simp only [B, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨i, ⟨hi, hs⟩, rfl⟩; exact ⟨⟨i, hi, rfl⟩, hs⟩
        · rintro ⟨⟨i, hi, rfl⟩, hs⟩; exact ⟨i, ⟨hi, hs⟩, rfl⟩
      rw [h1, h2, ← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hAB_disj),
        ← Finset.filter_union, hAB_eq]
    by_cases hs1 : s1 = true
    · refine hmin_k d hd_lt ⟨v a, fun j => v (a + j), fun j => edge (a + j), rfl, ?_, hs1, ?_⟩
      · dsimp only
        have : a + d = b := by omega
        rw [this, ← hab]
      · intro j hj
        dsimp only
        have hst := hstep (a + j) (by omega)
        have : a + j + 1 = a + (j + 1) := by omega
        rw [← this]; exact hst
    · have hs2 : s2 = true := by
        by_contra hns2
        have hs1f : s1 = false := by revert hs1; generalize s1 = x; cases x <;> decide
        have hs2f : s2 = false := by revert hns2; generalize s2 = x; cases x <;> decide
        have he1 : Even (((Finset.range d).filter (fun j => sign (edge (a + j)) = true)).card) := by
          rw [← Nat.not_odd_iff_even, ← xor_count_odd_iff]; simp [s1, hs1f]
        have he2 : Even (((Finset.range t).filter (fun j => sign (edge (idxE j)) = true)).card) := by
          rw [← Nat.not_odd_iff_even, ← xor_count_odd_iff]; simp [s2, hs2f]
        have he3 : Even (((Finset.range k).filter (fun j => sign (edge j) = true)).card) := by
          rw [← hcard]; exact he1.add he2
        exact absurd hodd (Nat.not_odd_iff_even.mpr he3)
      refine hmin_k t ht_lt ⟨v (idxE 0), fun j => v (idxE j), fun j => edge (idxE j), rfl, ?_, hs2, ?_⟩
      · dsimp only
        have htV : idxE t = k := by
          dsimp only [idxE]
          have : ¬ t < a := by omega
          simp [this]; omega
        rw [htV, hvk]
        by_cases ha0 : 0 < a
        · simp [idxE, ha0, hv0]
        · have ha' : a = 0 := by omega
          have : ¬ 0 < a := by omega
          simp [idxE, this]
          have hdb : d = b := by omega
          rw [hdb, ← hab, ha', hv0]
      · intro j hj
        by_cases hja : j < a
        · have h1 := hstep j (by omega)
          simp only [idxE, hja, ↓reduceIte]
          by_cases hja1 : j + 1 < a
          · simp only [hja1, ↓reduceIte]; exact h1
          · simp only [hja1, ↓reduceIte]
            have e1 : j + 1 + d = b := by omega
            have e2 : j + 1 = a := by omega
            rw [e1, ← hab, ← e2]
            exact h1
        · have hj1 : ¬ j + 1 < a := by omega
          simp only [idxE, hja, hj1, ↓reduceIte]
          have h1 := hstep (j + d) (by omega)
          have : j + 1 + d = j + d + 1 := by omega
          rw [this]; exact h1
  have he_inj : ∀ a < k, ∀ b < k, edge a = edge b → a = b := by
    intro a ha b hb hab
    by_contra hne
    wlog hlt : a < b generalizing a b
    · exact this b hb a ha hab.symm (Ne.symm hne) (by omega)
    have hpa : ({v a, v (a + 1)} : Finset (Fin n)) = {left (edge a), right (edge a)} := by
      rcases (hstep a ha).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2]; ext z; simp [or_comm]
    have hpb : ({v b, v (b + 1)} : Finset (Fin n)) = {left (edge b), right (edge b)} := by
      rcases (hstep b hb).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2]; ext z; simp [or_comm]
    rw [hab] at hpa
    have hpeq : ({v a, v (a + 1)} : Finset (Fin n)) = {v b, v (b + 1)} := hpa.trans hpb.symm
    have hva_mem : v a ∈ ({v b, v (b + 1)} : Finset (Fin n)) := by rw [← hpeq]; simp
    have hva1_mem : v (a + 1) ∈ ({v b, v (b + 1)} : Finset (Fin n)) := by rw [← hpeq]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hva_mem hva1_mem
    have hne_ab : v a ≠ v b := fun h => hne (hv_inj a ha b hb h)
    have hva_b1 : v a = v (b + 1) := hva_mem.resolve_left hne_ab
    by_cases hb1 : b + 1 < k
    · exact absurd (hv_inj a ha (b + 1) hb1 hva_b1) (by omega)
    · have hbk : b + 1 = k := by omega
      rw [hbk, hvk, ← hv0] at hva_b1
      have ha0 : a = 0 := hv_inj a ha 0 (by omega) hva_b1
      subst ha0
      rcases hva1_mem with h1 | h1
      · have h1b : 1 = b := hv_inj 1 (by omega) b hb h1
        have hk2 : k = 2 := by omega
        subst hk2
        have hb1' : b = 1 := by omega
        subst hb1'
        have hcard2 : ((Finset.range 2).filter (fun j => sign (edge j) = true)).card =
            if sign (edge 0) = true then 2 else 0 := by
          have h01 : sign (edge 1) = sign (edge 0) := congrArg sign hab.symm
          have hr2 : Finset.range 2 = {0, 1} := by decide
          rw [hr2]
          by_cases hs0 : sign (edge 0) = true
          · simp [Finset.filter_insert, Finset.filter_singleton, hs0, h01]
          · have hs0f : sign (edge 0) = false := Bool.eq_false_iff.mpr hs0
            simp [Finset.filter_insert, Finset.filter_singleton, hs0f, h01]
        rw [hcard2] at hodd
        split_ifs at hodd
        · exact absurd hodd (by decide)
        · exact absurd hodd (by decide)
      · rw [hbk, hvk, ← hv0] at h1
        exact absurd (hv_inj 1 (by omega) 0 (by omega) h1) (by omega)
  refine ⟨k, v, edge, hk1, ⟨v, edge, rfl, by rw [hv0, hvk], hxor, hstep⟩, by rw [hv0, hvk],
    hodd, hstep, hv_inj, he_inj⟩

private theorem two_mul_g_le_card {n m : ℕ} {left right : Fin m → Fin n} {sign : Fin m → Bool}
    {g : ℕ} (hmin : ∀ k < g, ¬ negWalk left right sign k)
    {S : Finset (Clause (Fin n))}
    (hS_sub : ∀ C ∈ S, ∃ e a, C = cl left right sign e a)
    (hS_unsat : ∀ α : Fin n → Bool, ¬ ∀ C ∈ S, ClauseSat α C) :
    2 * g ≤ S.card := by
  classical
  have hS_ne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    exact hS_unsat (fun _ => false) (by simp [h])
  obtain ⟨C0, hC0⟩ := hS_ne
  obtain ⟨e0, _, _⟩ := hS_sub C0 hC0
  have hm : 0 < m := Fin.pos e0
  let eOf : {C // C ∈ S} → Fin m := fun c => Classical.choose (hS_sub c.1 c.2)
  let aOf : {C // C ∈ S} → Bool := fun c => Classical.choose (Classical.choose_spec (hS_sub c.1 c.2))
  have hclOf : ∀ c : {C // C ∈ S}, c.1 = cl left right sign (eOf c) (aOf c) :=
    fun c => Classical.choose_spec (Classical.choose_spec (hS_sub c.1 c.2))
  let isCycle (z : {C // C ∈ S} → ZMod 2) : Prop :=
    ∀ x : Fin n,
      (∑ c : {C // C ∈ S}, if left (eOf c) = x then z c else 0) +
      (∑ c : {C // C ∈ S}, if right (eOf c) = x then z c else 0) = 0
  let phi (z : {C // C ∈ S} → ZMod 2) : ZMod 2 :=
    ∑ c : {C // C ∈ S}, if sign (eOf c) = true then z c else 0
  have hcyc_add : ∀ z1 z2, isCycle z1 → isCycle z2 → isCycle (z1 + z2) := by
    intro z1 z2 h1 h2 x
    have ha : (∑ c : {C // C ∈ S}, if left (eOf c) = x then (z1 + z2) c else 0) =
        (∑ c, if left (eOf c) = x then z1 c else 0) + (∑ c, if left (eOf c) = x then z2 c else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs <;> simp
    have hb : (∑ c : {C // C ∈ S}, if right (eOf c) = x then (z1 + z2) c else 0) =
        (∑ c, if right (eOf c) = x then z1 c else 0) + (∑ c, if right (eOf c) = x then z2 c else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs <;> simp
    rw [ha, hb]
    have hx1 := h1 x
    have hx2 := h2 x
    calc _ = ((∑ c, if left (eOf c) = x then z1 c else 0) + (∑ c, if right (eOf c) = x then z1 c else 0)) +
             ((∑ c, if left (eOf c) = x then z2 c else 0) + (∑ c, if right (eOf c) = x then z2 c else 0)) := by ring
      _ = 0 + 0 := by rw [hx1, hx2]
      _ = 0 := by simp
  have hphi_add : ∀ z1 z2, phi (z1 + z2) = phi z1 + phi z2 := by
    intro z1 z2
    dsimp only [phi]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs <;> simp
  let N : Finset ({C // C ∈ S} → ZMod 2) := Finset.univ.filter (fun z => isCycle z ∧ phi z = 1)
  have hwalk_to_N : ∀ (Q : {C // C ∈ S} → Prop),
      (¬ ∃ β : Fin n → Bool, ∀ c, Q c → β (right (eOf c)) = (β (left (eOf c)) ^^ sign (eOf c))) →
      ∃ z ∈ N, ∀ c, z c = 1 → Q c := by
    intro Q hunbal
    let P : Fin m → Prop := fun e => ∃ c, Q c ∧ eOf c = e
    have hPunbal : ¬ ∃ β : Fin n → Bool, ∀ e, P e → β (right e) = (β (left e) ^^ sign e) := by
      rintro ⟨β, hβ⟩
      exact hunbal ⟨β, fun c hc => hβ (eOf c) ⟨c, hc, rfl⟩⟩
    obtain ⟨k, v, edge, hk1, _, hvk, hodd, hstep, _, he_inj⟩ :=
      minimal_neg_cycle (exists_negWalk_of_not_balanced hm hPunbal)
    have hc_ex : ∀ j : Fin k, ∃ c : {C // C ∈ S}, Q c ∧ eOf c = edge j.val :=
      fun j => (hstep j.val j.isLt).1
    let cAt : Fin k → {C // C ∈ S} := fun j => Classical.choose (hc_ex j)
    have hcAt_Q : ∀ j, Q (cAt j) := fun j => (Classical.choose_spec (hc_ex j)).1
    have hcAt_e : ∀ j, eOf (cAt j) = edge j.val := fun j => (Classical.choose_spec (hc_ex j)).2
    have hcAt_inj : Function.Injective cAt := by
      intro i j hij
      have heq : edge i.val = edge j.val := by rw [← hcAt_e i, ← hcAt_e j, hij]
      exact Fin.ext (he_inj i.val i.isLt j.val j.isLt heq)
    let z : {C // C ∈ S} → ZMod 2 := fun c => if c ∈ Finset.univ.image cAt then 1 else 0
    have hz_cycle : isCycle z := by
      intro x
      have hsum : ∀ (f : Fin m → Fin n),
          (∑ c : {C // C ∈ S}, if f (eOf c) = x then z c else 0) =
          ∑ j : Fin k, if f (edge j.val) = x then (1 : ZMod 2) else 0 := by
        intro f
        trans ∑ c ∈ Finset.univ.image cAt, if f (eOf c) = x then (1 : ZMod 2) else 0
        · rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image cAt))]
          · refine Finset.sum_congr rfl fun c hc => ?_
            dsimp only [z]; simp [hc]
          · intro c _ hc
            dsimp only [z]; simp [hc]
        · rw [Finset.sum_image (fun i _ j _ h => hcAt_inj h)]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hcAt_e j]
      rw [hsum left, hsum right, ← Finset.sum_add_distrib]
      have hpair : ∀ j : Fin k,
          ((if left (edge j.val) = x then (1 : ZMod 2) else 0) +
            if right (edge j.val) = x then (1 : ZMod 2) else 0) =
          ((if v j.val = x then (1 : ZMod 2) else 0) +
            if v (j.val + 1) = x then (1 : ZMod 2) else 0) := by
        intro j
        rcases (hstep j.val j.isLt).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]
        · rw [h1, h2, add_comm]
      simp_rw [hpair]
      rw [Finset.sum_add_distrib]
      let nxt : Fin k ≃ Fin k :=
        { toFun := fun j => ⟨(j.val + 1) % k, Nat.mod_lt _ (by omega)⟩
          invFun := fun j => ⟨(j.val + k - 1) % k, Nat.mod_lt _ (by omega)⟩
          left_inv := fun j => by
            ext; dsimp
            by_cases hj : j.val + 1 < k
            · rw [Nat.mod_eq_of_lt hj]
              have e1 : j.val + 1 + k - 1 = j.val + k := by omega
              rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
            · have e1 : j.val + 1 = k := by omega
              rw [e1, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (by omega : k - 1 < k)]
              omega
          right_inv := fun j => by
            ext; dsimp
            by_cases hj : j.val = 0
            · rw [hj, zero_add, Nat.mod_eq_of_lt (by omega : k - 1 < k)]
              have e1 : k - 1 + 1 = k := by omega
              rw [e1, Nat.mod_self]
            · have e1 : j.val + k - 1 = (j.val - 1) + k := by omega
              rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : j.val - 1 < k)]
              have e2 : j.val - 1 + 1 = j.val := by omega
              rw [e2, Nat.mod_eq_of_lt j.isLt] }
      have hvnxt : ∀ j : Fin k, v (j.val + 1) = v (nxt j).val := by
        intro j
        dsimp [nxt]
        by_cases hj : j.val + 1 < k
        · rw [Nat.mod_eq_of_lt hj]
        · have : j.val + 1 = k := by omega
          rw [this, Nat.mod_self, ← hvk]
      have hshift : (∑ j : Fin k, if v (j.val + 1) = x then (1 : ZMod 2) else 0) =
          ∑ j : Fin k, if v j.val = x then (1 : ZMod 2) else 0 := by
        simp_rw [hvnxt]
        exact Equiv.sum_comp nxt (fun j : Fin k => if v j.val = x then (1 : ZMod 2) else 0)
      rw [hshift]
      have h20 : ∀ a : ZMod 2, a + a = 0 := by intro a; fin_cases a <;> rfl
      exact h20 _
    have hz_phi : phi z = 1 := by
      dsimp only [phi]
      trans ∑ c ∈ Finset.univ.image cAt, if sign (eOf c) = true then (1 : ZMod 2) else 0
      · rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image cAt))]
        · refine Finset.sum_congr rfl fun c hc => ?_
          dsimp only [z]; simp [hc]
        · intro c _ hc
          dsimp only [z]; simp [hc]
      · rw [Finset.sum_image (fun i _ j _ h => hcAt_inj h)]
        simp_rw [hcAt_e]
        rw [Finset.sum_boole]
        have hcnt : (Finset.univ.filter (fun j : Fin k => sign (edge j.val) = true)).card =
            ((Finset.range k).filter (fun j => sign (edge j) = true)).card := by
          refine Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_
          · intro j hj; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hj ⊢
            exact ⟨j.isLt, hj⟩
          · intro i _ j _ hij; exact Fin.ext hij
          · intro j hj; simp only [Finset.mem_filter, Finset.mem_range] at hj
            exact ⟨⟨j, hj.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj.2⟩, rfl⟩
        rw [hcnt]
        obtain ⟨r, hr⟩ := hodd
        rw [hr]
        push_cast
        have h20 : (2 : ZMod 2) = 0 := rfl
        rw [h20, zero_mul, zero_add]
    refine ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz_cycle, hz_phi⟩, fun c hc => ?_⟩
    have hmem : c ∈ Finset.univ.image cAt := by
      by_contra hnot
      dsimp only [z] at hc
      simp [hnot] at hc
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hmem
    exact hcAt_Q j
  have hN_ne : N.Nonempty := by
    have hunbal : ¬ ∃ β : Fin n → Bool, ∀ c : {C // C ∈ S}, True →
        β (right (eOf c)) = (β (left (eOf c)) ^^ sign (eOf c)) := by
      rintro ⟨β, hβ⟩
      apply hS_unsat β
      intro C hCS
      change ClauseSat β (⟨C, hCS⟩ : {C // C ∈ S}).1
      rw [hclOf ⟨C, hCS⟩]
      exact cl_sat_of_balanced (hβ ⟨C, hCS⟩ trivial)
    obtain ⟨z, hz, _⟩ := hwalk_to_N (fun _ => True) hunbal
    exact ⟨z, hz⟩
  have hno_bridge : ∀ c0 : {C // C ∈ S}, ∃ z ∈ N, z c0 = 0 := by
    intro c0
    have hunbal : ¬ ∃ β : Fin n → Bool, ∀ c : {C // C ∈ S}, c ≠ c0 →
        β (right (eOf c)) = (β (left (eOf c)) ^^ sign (eOf c)) := by
      rintro ⟨β, hβ⟩
      rcases cl_not_both_falsified (left := left) (right := right) (sign := sign)
          (e := eOf c0) (a := aOf c0) β with h1 | h2
      · apply hS_unsat β
        intro C hCS
        change ClauseSat β (⟨C, hCS⟩ : {C // C ∈ S}).1
        by_cases hc : (⟨C, hCS⟩ : {C // C ∈ S}) = c0
        · rw [hc, hclOf c0]; exact h1
        · rw [hclOf ⟨C, hCS⟩]; exact cl_sat_of_balanced (hβ ⟨C, hCS⟩ hc)
      · apply hS_unsat (fun x => !(β x))
        intro C hCS
        change ClauseSat (fun x => !(β x)) (⟨C, hCS⟩ : {C // C ∈ S}).1
        by_cases hc : (⟨C, hCS⟩ : {C // C ∈ S}) = c0
        · rw [hc, hclOf c0]; exact h2
        · rw [hclOf ⟨C, hCS⟩]
          apply cl_sat_of_balanced
          have hbe := hβ ⟨C, hCS⟩ hc
          change (!(β (right (eOf ⟨C, hCS⟩)))) = ((!(β (left (eOf ⟨C, hCS⟩)))) ^^ sign (eOf ⟨C, hCS⟩))
          rw [hbe]
          cases β (left (eOf ⟨C, hCS⟩)) <;> cases sign (eOf ⟨C, hCS⟩) <;> rfl
    obtain ⟨z, hz, hzQ⟩ := hwalk_to_N (fun c => c ≠ c0) hunbal
    refine ⟨z, hz, ?_⟩
    by_contra hne0
    have h1 : z c0 = 1 := by
      revert hne0; generalize z c0 = x; intro h; fin_cases x
      · exact absurd rfl h
      · rfl
    exact hzQ c0 h1 rfl
  have hwt_ge : ∀ z ∈ N, g ≤ (Finset.univ.filter (fun c : {C // C ∈ S} => z c = 1)).card := by
    intro z hz
    obtain ⟨hz_cyc, hz_phi⟩ := (Finset.mem_filter.mp hz).2
    let Pz : Fin m → Prop := fun e => ∃ c : {C // C ∈ S}, z c = 1 ∧ eOf c = e
    have hPz_unbal : ¬ ∃ β : Fin n → Bool, ∀ e, Pz e → β (right e) = (β (left e) ^^ sign e) := by
      rintro ⟨β, hβ⟩
      let bZ : Fin n → ZMod 2 := fun x => if β x then 1 else 0
      have hterm : ∀ c : {C // C ∈ S},
          (if sign (eOf c) = true then z c else 0) =
          (bZ (left (eOf c)) + bZ (right (eOf c))) * z c := by
        intro c
        by_cases hzc : z c = 1
        · have hbe := hβ (eOf c) ⟨c, hzc, rfl⟩
          rw [hzc, mul_one]
          dsimp only [bZ]
          rw [hbe]
          cases β (left (eOf c)) <;> cases sign (eOf c) <;> decide
        · have hzc0 : z c = 0 := by
            revert hzc; generalize z c = x; intro h; fin_cases x
            · rfl
            · exact absurd rfl h
          simp [hzc0]
      have hsum1 : phi z = ∑ c : {C // C ∈ S}, (bZ (left (eOf c)) + bZ (right (eOf c))) * z c := by
        dsimp only [phi]
        exact Finset.sum_congr rfl fun c _ => hterm c
      have hsum0 : (∑ c : {C // C ∈ S}, (bZ (left (eOf c)) + bZ (right (eOf c))) * z c) = 0 := by
        have hswap : ∀ f : Fin m → Fin n,
            (∑ c : {C // C ∈ S}, bZ (f (eOf c)) * z c) =
            ∑ x : Fin n, bZ x * (∑ c : {C // C ∈ S}, if f (eOf c) = x then z c else 0) := by
          intro f
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c _ => ?_
          simp only [mul_ite, mul_zero, eq_comm (a := f (eOf c)), Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        simp_rw [add_mul]
        rw [Finset.sum_add_distrib, hswap left, hswap right, ← Finset.sum_add_distrib]
        refine Finset.sum_eq_zero fun x _ => ?_
        rw [← mul_add, hz_cyc x, mul_zero]
      rw [hsum1, hsum0] at hz_phi
      exact zero_ne_one hz_phi
    obtain ⟨k, v, edge, _, _, hvk, hodd, hstep, _, he_inj⟩ :=
      minimal_neg_cycle (exists_negWalk_of_not_balanced hm hPz_unbal)
    have hgk : g ≤ k := by
      by_contra hlt
      exact hmin k (by omega) ⟨v, edge, hvk, hodd, fun j hj => (hstep j hj).2⟩
    have hc_ex : ∀ j : Fin k, ∃ c : {C // C ∈ S}, z c = 1 ∧ eOf c = edge j.val :=
      fun j => (hstep j.val j.isLt).1
    let cAt : Fin k → {C // C ∈ S} := fun j => Classical.choose (hc_ex j)
    have hcAt_e : ∀ j, eOf (cAt j) = edge j.val := fun j => (Classical.choose_spec (hc_ex j)).2
    have hcAt_inj : Function.Injective cAt := by
      intro i j hij
      have heq : edge i.val = edge j.val := by rw [← hcAt_e i, ← hcAt_e j, hij]
      exact Fin.ext (he_inj i.val i.isLt j.val j.isLt heq)
    calc g ≤ k := hgk
      _ = (Finset.univ : Finset (Fin k)).card := (Fintype.card_fin k).symm
      _ = (Finset.univ.image cAt).card := (Finset.card_image_of_injective _ hcAt_inj).symm
      _ ≤ (Finset.univ.filter (fun c : {C // C ∈ S} => z c = 1)).card := by
          apply Finset.card_le_card
          intro c hc
          obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hc
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Classical.choose_spec (hc_ex j)).1⟩
  have hhalf : ∀ c : {C // C ∈ S}, 2 * (N.filter (fun z => z c = 1)).card ≤ N.card := by
    intro c
    by_cases hex1 : ∃ z1 ∈ N, z1 c = 1
    · obtain ⟨z1, hz1, hz1c⟩ := hex1
      obtain ⟨z0, hz0, hz0c⟩ := hno_bridge c
      let d := z1 + z0
      have hd_cyc : isCycle d := hcyc_add z1 z0 (Finset.mem_filter.mp hz1).2.1 (Finset.mem_filter.mp hz0).2.1
      have hd_phi : phi d = 0 := by
        rw [hphi_add, (Finset.mem_filter.mp hz1).2.2, (Finset.mem_filter.mp hz0).2.2]; decide
      have hdc : d c = 1 := by simp [d, hz1c, hz0c]
      have hz2 : ∀ z : {C // C ∈ S} → ZMod 2, z + d + d = z := by
        intro z; ext x; simp only [Pi.add_apply]
        generalize z x = a; generalize d x = b
        fin_cases a <;> fin_cases b <;> rfl
      have hcard_eq : (N.filter (fun z => z c = 1)).card = (N.filter (fun z => z c = 0)).card := by
        refine Finset.card_bij (fun z _ => z + d) ?_ ?_ ?_
        · intro z hz
          obtain ⟨hzN, hzc⟩ := Finset.mem_filter.mp hz
          obtain ⟨hzc1, hzp1⟩ := (Finset.mem_filter.mp hzN).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            hcyc_add z d hzc1 hd_cyc, by rw [hphi_add, hzp1, hd_phi, add_zero]⟩, ?_⟩
          simp only [Pi.add_apply, hzc, hdc]; decide
        · intro a _ b _ hab
          have : a + d + d = b + d + d := congrArg (· + d) hab
          rw [hz2 a, hz2 b] at this; exact this
        · intro z hz
          obtain ⟨hzN, hzc⟩ := Finset.mem_filter.mp hz
          obtain ⟨hzc1, hzp1⟩ := (Finset.mem_filter.mp hzN).2
          refine ⟨z + d, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            hcyc_add z d hzc1 hd_cyc, by rw [hphi_add, hzp1, hd_phi, add_zero]⟩, ?_⟩, hz2 z⟩
          simp only [Pi.add_apply, hzc, hdc]; decide
      have hsum : (N.filter (fun z => z c = 1)).card + (N.filter (fun z => z c = 0)).card = N.card := by
        rw [← Finset.card_union_of_disjoint]
        · congr 1; ext z; simp only [Finset.mem_union, Finset.mem_filter]
          constructor
          · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
          · intro h
            generalize z c = x
            fin_cases x
            · right; exact ⟨h, rfl⟩
            · left; exact ⟨h, rfl⟩
        · rw [Finset.disjoint_left]; intro z h1 h2
          have h1' := (Finset.mem_filter.mp h1).2
          have h2' := (Finset.mem_filter.mp h2).2
          rw [h1'] at h2'; exact one_ne_zero h2'
      omega
    · have hempty : N.filter (fun z => z c = 1) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro z hz hzc; exact hex1 ⟨z, hz, hzc⟩
      simp [hempty]
  have hdouble :
      ∑ z ∈ N, (Finset.univ.filter (fun c : {C // C ∈ S} => z c = 1)).card =
      ∑ c : {C // C ∈ S}, (N.filter (fun z => z c = 1)).card := by
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  have h1 : N.card * g ≤ ∑ z ∈ N, (Finset.univ.filter (fun c : {C // C ∈ S} => z c = 1)).card := by
    calc N.card * g = ∑ _z ∈ N, g := by simp
      _ ≤ ∑ z ∈ N, (Finset.univ.filter (fun c : {C // C ∈ S} => z c = 1)).card :=
          Finset.sum_le_sum (fun z hz => hwt_ge z hz)
  have h2 : 2 * (∑ c : {C // C ∈ S}, (N.filter (fun z => z c = 1)).card) ≤ S.card * N.card := by
    rw [Finset.mul_sum]
    calc ∑ c : {C // C ∈ S}, 2 * (N.filter (fun z => z c = 1)).card
        ≤ ∑ _c : {C // C ∈ S}, N.card := Finset.sum_le_sum (fun c _ => hhalf c)
      _ = Fintype.card {C // C ∈ S} * N.card := by simp
      _ = S.card * N.card := by rw [Fintype.card_coe]
  have hNpos : 0 < N.card := Finset.card_pos.mpr hN_ne
  have hmul : (2 * g) * N.card ≤ S.card * N.card := by
    calc (2 * g) * N.card = 2 * (N.card * g) := by ring
      _ ≤ 2 * ∑ z ∈ N, (Finset.univ.filter (fun c : {C // C ∈ S} => z c = 1)).card :=
          Nat.mul_le_mul_left 2 h1
      _ = 2 * ∑ c : {C // C ∈ S}, (N.filter (fun z => z c = 1)).card := by rw [hdouble]
      _ ≤ S.card * N.card := h2
  exact Nat.le_of_mul_le_mul_right hmul hNpos

private theorem derivation_witness {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {π : List (Clause V)} (h : IsDerivation F π) :
    ∃ step : Fin π.length → Option (Fin π.length × Fin π.length),
      ∀ i : Fin π.length,
        match step i with
        | none => π[i] ∈ F
        | some (j, k) => i.val < j.val ∧ i.val < k.val ∧ IsResolvent π[j] π[k] π[i] := by
  induction h with
  | nil => exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | @ax π C hπ hCF ih =>
    obtain ⟨step, hstep⟩ := ih
    refine ⟨fun i =>
      if hi : i.val = 0 then none
      else (step ⟨i.val - 1, by have := i.isLt; simp at this; omega⟩).map
        (fun p => (⟨p.1.val + 1, by simp⟩, ⟨p.2.val + 1, by simp⟩)), ?_⟩
    intro i
    by_cases hi : i.val = 0
    · simp only [hi, ↓reduceDIte]
      have hi0 : i = ⟨0, by simp⟩ := Fin.ext hi
      subst hi0
      exact hCF
    · simp only [hi, ↓reduceDIte]
      let i' : Fin π.length := ⟨i.val - 1, by have := i.isLt; simp at this; omega⟩
      have h' := hstep i'
      have hi_eq : (C :: π)[i] = π[i'] := by
        have heq : i = i'.succ := Fin.ext (by simp [i']; omega)
        rw [heq]; rfl
      cases hs : step i' with
      | none =>
        rw [hs] at h'
        simpa [hi_eq] using h'
      | some p =>
        rw [hs] at h'
        dsimp only [Option.map_some]
        refine ⟨by simp [i'] at h' ⊢; omega, by simp [i'] at h' ⊢; omega, ?_⟩
        rw [hi_eq]
        exact h'.2.2
  | @res π C D R hπ hC hD hR ih =>
    obtain ⟨step, hstep⟩ := ih
    obtain ⟨j0, hj0_lt, hj0_eq⟩ := List.getElem_of_mem hC
    obtain ⟨k0, hk0_lt, hk0_eq⟩ := List.getElem_of_mem hD
    let j : Fin (R :: π).length := ⟨j0 + 1, Nat.succ_lt_succ hj0_lt⟩
    let k : Fin (R :: π).length := ⟨k0 + 1, Nat.succ_lt_succ hk0_lt⟩
    refine ⟨fun i =>
      if hi : i.val = 0 then some (j, k)
      else (step ⟨i.val - 1, by have := i.isLt; simp at this; omega⟩).map
        (fun p => (⟨p.1.val + 1, by simp⟩, ⟨p.2.val + 1, by simp⟩)), ?_⟩
    intro i
    by_cases hi : i.val = 0
    · simp only [hi, ↓reduceDIte]
      have hi0 : i = ⟨0, by simp⟩ := Fin.ext hi
      subst hi0
      refine ⟨by simp [j], by simp [k], ?_⟩
      simpa [j, k, hj0_eq, hk0_eq] using hR
    · simp only [hi, ↓reduceDIte]
      let i' : Fin π.length := ⟨i.val - 1, by have := i.isLt; simp at this; omega⟩
      have h' := hstep i'
      have hi_eq : (R :: π)[i] = π[i'] := by
        have heq : i = i'.succ := Fin.ext (by simp [i']; omega)
        rw [heq]; rfl
      cases hs : step i' with
      | none =>
        rw [hs] at h'
        simpa [hi_eq] using h'
      | some p =>
        rw [hs] at h'
        dsimp only [Option.map_some]
        refine ⟨by simp [i'] at h' ⊢; omega, by simp [i'] at h' ⊢; omega, ?_⟩
        rw [hi_eq]
        exact h'.2.2

private theorem resolvent_sound {V : Type} [DecidableEq V] {a : V → Bool}
    {C D R : Clause V} (hres : IsResolvent C D R) (hC : ClauseSat a C) (hD : ClauseSat a D) :
    ClauseSat a R := by
  obtain ⟨v, _, _, rfl⟩ := hres
  by_cases hav : a v = true
  · obtain ⟨l, hlD, hla⟩ := hD
    have hne : l ≠ (v, false) := by intro heq; subst heq; simp [hav] at hla
    exact ⟨l, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne, hlD⟩), hla⟩
  · obtain ⟨l, hlC, hla⟩ := hC
    have hne : l ≠ (v, true) := by intro heq; subst heq; exact hav hla
    exact ⟨l, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hlC⟩), hla⟩

private theorem biUnion_pairwise_disjoint_of_card_eq {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → Finset β)
    (heq : (s.biUnion f).card = ∑ a ∈ s, (f a).card) :
    ∀ a ∈ s, ∀ b ∈ s, a ≠ b → Disjoint (f a) (f b) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro a ha; simp at ha
  | @insert x s hx ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hx] at heq
    have hle1 : (f x ∪ s.biUnion f).card ≤ (f x).card + (s.biUnion f).card := Finset.card_union_le _ _
    have hle2 : (s.biUnion f).card ≤ ∑ a ∈ s, (f a).card := Finset.card_biUnion_le
    have hsub : (s.biUnion f).card = ∑ a ∈ s, (f a).card := by omega
    have hu : (f x ∪ s.biUnion f).card = (f x).card + (s.biUnion f).card := by omega
    have hdisj_x : Disjoint (f x) (s.biUnion f) := by
      have hi := Finset.card_union_add_card_inter (f x) (s.biUnion f)
      have h0 : (f x ∩ s.biUnion f).card = 0 := by omega
      exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp h0)
    have ih' := ih hsub
    intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with rfl | ha' <;> rcases Finset.mem_insert.mp hb with rfl | hb'
    · exact absurd rfl hab
    · exact hdisj_x.mono_right (Finset.subset_biUnion_of_mem f hb')
    · exact (hdisj_x.mono_right (Finset.subset_biUnion_of_mem f ha')).symm
    · exact ih' a ha' b hb' hab

private theorem walk_of_unit_core {n m : ℕ} {left right : Fin m → Fin n} {sign : Fin m → Bool}
    {g : ℕ} (hmin : ∀ k < g, ¬ negWalk left right sign k)
    {H : Set (Clause (Fin n))} (hH : H ⊆ {C | ∃ e a, C = cl left right sign e a})
    (root : Fin n) (start : Bool)
    {T : Finset (Clause (Fin n))} (hTH : ∀ C ∈ T, C ∈ H) (hTcard : T.card = g)
    (hTunsat : ∀ α : Fin n → Bool, α root = start → ∃ C ∈ T, ¬ ClauseSat α C) :
    ∃ (v : ℕ → Fin n) (edge : ℕ → Fin m) (val : ℕ → Bool),
      v 0 = root ∧ v g = root ∧ val 0 = start ∧ val g = !start ∧
      ∀ j < g,
        ((v j = left (edge j) ∧ v (j + 1) = right (edge j)) ∨
          (v j = right (edge j) ∧ v (j + 1) = left (edge j))) ∧
        val (j + 1) = (val j ^^ sign (edge j)) ∧
        ({(v j, !(val j)), (v (j + 1), val (j + 1))} : Clause (Fin n)) ∈ H := by
  classical
  have hTne : T.Nonempty := by
    obtain ⟨C, hC, _⟩ := hTunsat (fun _ => start) rfl
    exact ⟨C, hC⟩
  obtain ⟨C0, hC0⟩ := hTne
  obtain ⟨e0, _, _⟩ := hH (hTH C0 hC0)
  have hm : 0 < m := Fin.pos e0
  let eOf : {C // C ∈ T} → Fin m := fun c => Classical.choose (hH (hTH c.1 c.2))
  let aOf : {C // C ∈ T} → Bool := fun c => Classical.choose (Classical.choose_spec (hH (hTH c.1 c.2)))
  have hclOf : ∀ c : {C // C ∈ T}, c.1 = cl left right sign (eOf c) (aOf c) :=
    fun c => Classical.choose_spec (Classical.choose_spec (hH (hTH c.1 c.2)))
  let PT : Fin m → Prop := fun e => ∃ c : {C // C ∈ T}, eOf c = e
  have hPT_unbal : ¬ ∃ β : Fin n → Bool, ∀ e, PT e → β (right e) = (β (left e) ^^ sign e) := by
    rintro ⟨β, hβ⟩
    let β' : Fin n → Bool := if β root = start then β else fun x => !(β x)
    have hβ'r : β' root = start := by
      dsimp only [β']
      split_ifs with h
      · exact h
      · dsimp only; revert h; generalize β root = x; cases x <;> cases start <;> decide
    have hβ'bal : ∀ e, PT e → β' (right e) = (β' (left e) ^^ sign e) := by
      intro e he
      dsimp only [β']
      split_ifs
      · exact hβ e he
      · change (!(β (right e))) = ((!(β (left e))) ^^ sign e)
        rw [hβ e he]; cases β (left e) <;> cases sign e <;> rfl
    obtain ⟨C, hCT, hnot⟩ := hTunsat β' hβ'r
    apply hnot
    change ClauseSat β' (⟨C, hCT⟩ : {C // C ∈ T}).1
    rw [hclOf ⟨C, hCT⟩]
    exact cl_sat_of_balanced (hβ'bal (eOf ⟨C, hCT⟩) ⟨⟨C, hCT⟩, rfl⟩)
  obtain ⟨k, v0, e0w, hk1, _, hvk, hodd, hstep, hv_inj, he_inj⟩ :=
    minimal_neg_cycle (exists_negWalk_of_not_balanced hm hPT_unbal)
  have hgk : g ≤ k := by
    by_contra hlt
    exact hmin k (by omega) ⟨v0, e0w, hvk, hodd, fun j hj => (hstep j hj).2⟩
  let cAt : Fin k → {C // C ∈ T} := fun j => Classical.choose (hstep j.val j.isLt).1
  have hcAt_e : ∀ j, eOf (cAt j) = e0w j.val := fun j => Classical.choose_spec (hstep j.val j.isLt).1
  have hcAt_inj : Function.Injective cAt := by
    intro i j hij
    exact Fin.ext (he_inj i.val i.isLt j.val j.isLt (by rw [← hcAt_e i, ← hcAt_e j, hij]))
  have hkg : k ≤ g := by
    calc k = (Finset.univ : Finset (Fin k)).card := (Fintype.card_fin k).symm
      _ = (Finset.univ.image cAt).card := (Finset.card_image_of_injective _ hcAt_inj).symm
      _ ≤ Fintype.card {C // C ∈ T} := Finset.card_le_univ _
      _ = T.card := Fintype.card_coe T
      _ = g := hTcard
  have hkeq : k = g := le_antisymm hkg hgk
  subst hkeq
  have hsurj : ∀ c : {C // C ∈ T}, ∃ j : Fin k, cAt j = c := by
    have himg : (Finset.univ.image cAt) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_image_of_injective _ hcAt_inj, Finset.card_univ, Fintype.card_fin, Fintype.card_coe, hTcard]
    intro c
    have hc : c ∈ Finset.univ.image cAt := by rw [himg]; exact Finset.mem_univ c
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hc
    exact ⟨j, rfl⟩
  have hroot_on : ∃ r0 : Fin k, v0 r0.val = root := by
    by_contra hnot
    push Not at hnot
    let w0 : ℕ → Bool := fun j =>
      (List.ofFn (fun i : Fin j => sign (e0w i.val))).foldl Bool.xor false
    have hw0_step : ∀ j, w0 (j + 1) = (w0 j ^^ sign (e0w j)) := by
      intro j
      exact foldl_xor_ofFn_succ (fun i => sign (e0w i)) j
    let β0 : Fin n → Bool := fun x =>
      if h : ∃ j : Fin k, v0 j.val = x then w0 (Classical.choose h).val else false
    have hβ0_v : ∀ j : Fin k, β0 (v0 j.val) = w0 j.val := by
      intro j
      have hex : ∃ i : Fin k, v0 i.val = v0 j.val := ⟨j, rfl⟩
      simp only [β0, hex, ↓reduceDIte]
      have heq := hv_inj (Classical.choose hex).val (Classical.choose hex).isLt j.val j.isLt
        (Classical.choose_spec hex)
      rw [heq]
    have hβ0_sat : ∀ j : Fin k, j.val + 1 < k →
        β0 (v0 (j.val + 1)) = (β0 (v0 j.val) ^^ sign (e0w j.val)) := by
      intro j hj
      rw [hβ0_v ⟨j.val + 1, hj⟩, hβ0_v j, hw0_step]
    let eLast : Fin k := ⟨k - 1, by omega⟩
    have hcl_last := cl_not_both_falsified (left := left) (right := right) (sign := sign)
      (e := eOf (cAt eLast)) (a := aOf (cAt eLast)) β0
    let α : Fin n → Bool := fun x =>
      if x = root then start
      else if ClauseSat β0 (cAt eLast).1 then β0 x else !(β0 x)
    have hα_root : α root = start := by simp [α]
    have hα_cyc : ∀ x, (∃ j : Fin k, v0 j.val = x) →
        α x = if ClauseSat β0 (cAt eLast).1 then β0 x else !(β0 x) := by
      intro x ⟨j, hj⟩
      have hxr : x ≠ root := by rw [← hj]; exact hnot j
      simp [α, hxr]
    obtain ⟨C, hCT, hnotC⟩ := hTunsat α hα_root
    obtain ⟨j, hj⟩ := hsurj ⟨C, hCT⟩
    have hCeq : C = (cAt j).1 := by rw [hj]
    rw [hCeq] at hnotC
    apply hnotC
    by_cases hjl : j = eLast
    · subst hjl
      have hinc := (hstep eLast.val eLast.isLt).2
      rw [← hcAt_e eLast] at hinc
      have hL_on : ∃ i : Fin k, v0 i.val = left (eOf (cAt eLast)) := by
        rcases hinc with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact ⟨eLast, h1⟩
        · refine ⟨⟨0, by omega⟩, ?_⟩
          have : eLast.val + 1 = k := by simp [eLast]; omega
          rw [this, ← hvk] at h2; exact h2
      have hR_on : ∃ i : Fin k, v0 i.val = right (eOf (cAt eLast)) := by
        rcases hinc with ⟨_, h2⟩ | ⟨h1, _⟩
        · refine ⟨⟨0, by omega⟩, ?_⟩
          have : eLast.val + 1 = k := by simp [eLast]; omega
          rw [this, ← hvk] at h2; exact h2
        · exact ⟨eLast, h1⟩
      have hαL := hα_cyc _ hL_on
      have hαR := hα_cyc _ hR_on
      rw [hclOf (cAt eLast)]
      by_cases hsat0 : ClauseSat β0 (cAt eLast).1
      · have hαL' : α (left (eOf (cAt eLast))) = β0 (left (eOf (cAt eLast))) := by simpa [hsat0] using hαL
        have hαR' : α (right (eOf (cAt eLast))) = β0 (right (eOf (cAt eLast))) := by simpa [hsat0] using hαR
        rw [hclOf (cAt eLast)] at hsat0
        obtain ⟨l, hl, hla⟩ := hsat0
        simp only [cl, Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with rfl | rfl
        · exact ⟨(left (eOf (cAt eLast)), !(aOf (cAt eLast))), by simp [cl], hαL'.trans hla⟩
        · exact ⟨(right (eOf (cAt eLast)), aOf (cAt eLast) ^^ sign (eOf (cAt eLast))), by simp [cl],
            hαR'.trans hla⟩
      · have hαL' : α (left (eOf (cAt eLast))) = !(β0 (left (eOf (cAt eLast)))) := by simpa [hsat0] using hαL
        have hαR' : α (right (eOf (cAt eLast))) = !(β0 (right (eOf (cAt eLast)))) := by simpa [hsat0] using hαR
        have hsat1 : ClauseSat (fun x => !(β0 x)) (cl left right sign (eOf (cAt eLast)) (aOf (cAt eLast))) := by
          rw [hclOf (cAt eLast)] at hsat0
          exact hcl_last.resolve_left hsat0
        obtain ⟨l, hl, hla⟩ := hsat1
        simp only [cl, Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with rfl | rfl
        · exact ⟨(left (eOf (cAt eLast)), !(aOf (cAt eLast))), by simp [cl], hαL'.trans hla⟩
        · exact ⟨(right (eOf (cAt eLast)), aOf (cAt eLast) ^^ sign (eOf (cAt eLast))), by simp [cl],
            hαR'.trans hla⟩
    · have hjlt : j.val + 1 < k := by
        have : j.val ≠ k - 1 := fun h => hjl (Fin.ext h)
        omega
      rw [hclOf (cAt j)]
      apply cl_sat_of_balanced
      have hinc := (hstep j.val j.isLt).2
      rw [← hcAt_e j] at hinc
      have hbal0 := hβ0_sat j hjlt
      rw [← hcAt_e j] at hbal0
      have hα1 := hα_cyc (v0 j.val) ⟨j, rfl⟩
      have hα2 := hα_cyc (v0 (j.val + 1)) ⟨⟨j.val + 1, hjlt⟩, rfl⟩
      rcases hinc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2, hα1, hα2]
        split_ifs
        · exact hbal0
        · rw [hbal0]; cases β0 (v0 j.val) <;> cases sign (eOf (cAt j)) <;> rfl
      · rw [← h1, ← h2, hα1, hα2]
        split_ifs
        · rw [hbal0]; cases β0 (v0 j.val) <;> cases sign (eOf (cAt j)) <;> rfl
        · rw [hbal0]; cases β0 (v0 j.val) <;> cases sign (eOf (cAt j)) <;> rfl
  obtain ⟨r0, hr0⟩ := hroot_on
  let v : ℕ → Fin n := fun j => v0 ((r0.val + j) % k)
  let edge : ℕ → Fin m := fun j => e0w ((r0.val + j) % k)
  let val : ℕ → Bool := fun j =>
    start ^^ (List.ofFn (fun i : Fin j => sign (edge i.val))).foldl Bool.xor false
  have hv_0 : v 0 = root := by simp [v, Nat.mod_eq_of_lt r0.isLt, hr0]
  have hv_k : v k = root := by simp [v, Nat.add_mod_right, Nat.mod_eq_of_lt r0.isLt, hr0]
  have hval_0 : val 0 = start := by simp [val]
  have hval_step : ∀ j, val (j + 1) = (val j ^^ sign (edge j)) := by
    intro j
    dsimp only [val]
    rw [foldl_xor_ofFn_succ (fun i => sign (edge i)) j, Bool.xor_assoc]
  have hodd_rot : Odd (((Finset.range k).filter (fun j => sign (edge j) = true)).card) := by
    have hcard : ((Finset.range k).filter (fun j => sign (edge j) = true)).card =
        ((Finset.range k).filter (fun j => sign (e0w j) = true)).card := by
      refine Finset.card_bij (fun j _ => (r0.val + j) % k) ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
        exact ⟨Nat.mod_lt _ (by omega), hj.2⟩
      · intro a ha b hb hab
        simp only [Finset.mem_filter, Finset.mem_range] at ha hb
        by_cases h1 : r0.val + a < k <;> by_cases h2 : r0.val + b < k
        · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hab; omega
        · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hab; omega
        · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h2] at hab; omega
        · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hab; omega
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_range] at hj
        have hmod := mod_add_sub_cancel r0.isLt hj.1
        refine ⟨(j + k - r0.val) % k, ?_, hmod⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ (by omega)), by simp [edge, hmod, hj.2]⟩
    rw [hcard]; exact hodd
  have hval_k : val k = !start := by
    dsimp only [val]
    rw [(xor_count_odd_iff (fun j => sign (edge j)) k).mpr hodd_rot, Bool.xor_true]
  have hv_inj' : ∀ a < k, ∀ b < k, v a = v b → a = b := by
    intro a ha b hb hab
    have hmod := hv_inj ((r0.val + a) % k) (Nat.mod_lt _ (by omega))
      ((r0.val + b) % k) (Nat.mod_lt _ (by omega)) hab
    by_cases h1 : r0.val + a < k <;> by_cases h2 : r0.val + b < k
    · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hmod; omega
    · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hmod; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h2] at hmod; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hmod; omega
  have hinc' : ∀ j < k,
      (v j = left (edge j) ∧ v (j + 1) = right (edge j)) ∨
      (v j = right (edge j) ∧ v (j + 1) = left (edge j)) := by
    intro j hj
    let idx := (r0.val + j) % k
    have hidx : idx < k := Nat.mod_lt _ (by omega)
    have hst := (hstep idx hidx).2
    have hnext : v (j + 1) = v0 (idx + 1) := by
      dsimp only [v, idx]
      by_cases h1 : (r0.val + j) % k + 1 < k
      · have h2 : (r0.val + (j + 1)) % k = (r0.val + j) % k + 1 := by
          rw [show r0.val + (j + 1) = (r0.val + j) + 1 by omega, Nat.add_mod]
          have hk2 : 1 < k := by omega
          rw [Nat.mod_eq_of_lt hk2, Nat.mod_eq_of_lt h1]
        rw [h2]
      · have h2 : (r0.val + j) % k + 1 = k := by omega
        have h3 : (r0.val + (j + 1)) % k = 0 := by
          have : (r0.val + (j + 1)) % k = ((r0.val + j) % k + 1) % k := by
            rw [show r0.val + (j + 1) = (r0.val + j) + 1 by omega]
            exact (Nat.mod_add_mod _ _ _).symm
          rw [this, h2, Nat.mod_self]
        rw [h3, h2, ← hvk]
    rw [hnext]
    exact hst
  refine ⟨v, edge, val, hv_0, hv_k, hval_0, hval_k, fun j hj => ⟨hinc' j hj, hval_step j, ?_⟩⟩
  let α : Fin n → Bool := fun x =>
    if h : ∃ i : Fin k, v i.val = x then
      let i := (Classical.choose h).val
      if i ≤ j then val i else !(val i)
    else false
  have hα_v : ∀ i : Fin k, α (v i.val) = if i.val ≤ j then val i.val else !(val i.val) := by
    intro i
    have hex : ∃ i' : Fin k, v i'.val = v i.val := ⟨i, rfl⟩
    simp only [α, hex, ↓reduceDIte]
    have heq := hv_inj' (Classical.choose hex).val (Classical.choose hex).isLt i.val i.isLt
      (Classical.choose_spec hex)
    rw [heq]
  have hα_root : α root = start := by
    have h0 := hα_v ⟨0, by omega⟩
    simp only [hv_0, Nat.zero_le, ↓reduceIte, hval_0] at h0
    exact h0
  obtain ⟨C, hCT, hnotC⟩ := hTunsat α hα_root
  obtain ⟨idx0, hidx0⟩ := hsurj ⟨C, hCT⟩
  have hCeq : C = (cAt idx0).1 := by rw [hidx0]
  let i : Fin k := ⟨(idx0.val + k - r0.val) % k, Nat.mod_lt _ (by omega)⟩
  have hi_mod : (r0.val + i.val) % k = idx0.val := mod_add_sub_cancel r0.isLt idx0.isLt
  have he_eq : eOf (cAt idx0) = edge i.val := by
    rw [hcAt_e idx0]
    dsimp only [edge]
    rw [hi_mod]
  have hij : i.val = j := by
    by_contra hne
    apply hnotC
    rw [hCeq, hclOf (cAt idx0), he_eq]
    apply cl_sat_of_balanced
    have hbal_i : α (v (i.val + 1)) = (α (v i.val) ^^ sign (edge i.val)) := by
      by_cases hilt : i.val < j
      · have h1 := hα_v i
        have h2 := hα_v ⟨i.val + 1, by omega⟩
        simp only [show i.val ≤ j by omega, show i.val + 1 ≤ j by omega, ↓reduceIte] at h1 h2
        rw [h1, h2, hval_step]
      · have higt : j < i.val := by omega
        have h1 := hα_v i
        simp only [show ¬ i.val ≤ j by omega, ↓reduceIte] at h1
        by_cases hi1 : i.val + 1 < k
        · have h2 := hα_v ⟨i.val + 1, hi1⟩
          simp only [show ¬ i.val + 1 ≤ j by omega, ↓reduceIte] at h2
          rw [h1, h2, hval_step]
          cases val i.val <;> cases sign (edge i.val) <;> rfl
        · have hik : i.val + 1 = k := by omega
          have hst_val : start = !(val k) := by rw [hval_k, Bool.not_not]
          have hvk_eq : val k = val (i.val + 1) := congrArg val hik.symm
          rw [hik, hv_k, hα_root, h1, hst_val, hvk_eq, hval_step]
          cases val i.val <;> cases sign (edge i.val) <;> rfl
    rcases hinc' i.val i.isLt with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · rw [← hl, ← hr]; exact hbal_i
    · rw [← hl, ← hr]
      rw [hbal_i]
      cases α (v i.val) <;> cases sign (edge i.val) <;> rfl
  have hα_vj : α (v j) = val j := by
    have h1 := hα_v ⟨j, hj⟩
    simpa using h1
  have hα_vj1 : α (v (j + 1)) = !(val (j + 1)) := by
    by_cases hj1 : j + 1 < k
    · have h2 := hα_v ⟨j + 1, hj1⟩
      simp only [show ¬ j + 1 ≤ j by omega, ↓reduceIte] at h2
      exact h2
    · have hjk : j + 1 = k := by omega
      rw [hjk, hv_k, hα_root, hval_k, Bool.not_not]
  have hC_eq : C = {(v j, !(val j)), (v (j + 1), val (j + 1))} := by
    rw [hCeq, hclOf (cAt idx0), he_eq, hij] at hnotC ⊢
    rcases hinc' j hj with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · unfold cl at hnotC ⊢
      rw [← hl, ← hr] at hnotC ⊢
      have ha : aOf (cAt idx0) = val j := by
        by_contra hne
        apply hnotC
        refine ⟨(v j, !(aOf (cAt idx0))), by simp, ?_⟩
        dsimp only
        rw [hα_vj]
        revert hne; generalize aOf (cAt idx0) = x; generalize val j = y
        cases x <;> cases y <;> decide
      rw [ha, ← hval_step j]
    · unfold cl at hnotC ⊢
      rw [← hl, ← hr] at hnotC ⊢
      have ha : aOf (cAt idx0) = !(val (j + 1)) := by
        by_contra hne
        apply hnotC
        refine ⟨(v (j + 1), !(aOf (cAt idx0))), by simp, ?_⟩
        dsimp only
        rw [hα_vj1]
        revert hne; generalize aOf (cAt idx0) = x; generalize val (j + 1) = y
        cases x <;> cases y <;> decide
      rw [ha, Bool.not_not]
      have hxb : (!(val (j + 1)) ^^ sign (edge j)) = !(val j) := by
        rw [hval_step j]
        cases val j <;> cases sign (edge j) <;> rfl
      rw [hxb]
      ext z; simp [or_comm]
  rw [← hC_eq]
  exact hTH C hCT

private theorem forwards_dir {n m : ℕ} {left right : Fin m → Fin n} {sign : Fin m → Bool}
    {g : ℕ} (_hg : negWalk left right sign g) (hmin : ∀ k < g, ¬ negWalk left right sign k)
    {H : Set (Clause (Fin n))} (hH : H ⊆ {C | ∃ e a, C = cl left right sign e a})
    {π : List (Clause (Fin n))} (href : IsRefutation H π) (hlen : π.length + 1 ≤ 4 * g) :
    ∃ root : Fin n, ∀ start : Bool,
      ∃ (v : ℕ → Fin n) (edge : ℕ → Fin m) (val : ℕ → Bool),
        v 0 = root ∧ v g = root ∧ val 0 = start ∧ val g = !start ∧
        ∀ j < g,
          ((v j = left (edge j) ∧ v (j + 1) = right (edge j)) ∨
            (v j = right (edge j) ∧ v (j + 1) = left (edge j))) ∧
          val (j + 1) = (val j ^^ sign (edge j)) ∧
          ({(v j, !(val j)), (v (j + 1), val (j + 1))} : Clause (Fin n)) ∈ H := by
  classical
  obtain ⟨hπ, hempty⟩ := href
  obtain ⟨step, hstep⟩ := derivation_witness hπ
  obtain ⟨r0, hr0_lt, hr0_eq⟩ := List.getElem_of_mem hempty
  let r : Fin π.length := ⟨r0, hr0_lt⟩
  let Closed (rt : Fin π.length) (U : Finset (Fin π.length)) : Prop :=
    rt ∈ U ∧ ∀ i ∈ U, ∀ j k, step i = some (j, k) → j ∈ U ∧ k ∈ U
  have hexU : ∀ rt, ∃ c, ∃ U : Finset (Fin π.length), Closed rt U ∧ U.card = c :=
    fun rt => ⟨Finset.univ.card, Finset.univ,
      ⟨Finset.mem_univ rt, fun _ _ _ _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩⟩, rfl⟩
  let U := Classical.choose (Nat.find_spec (hexU r))
  have hU_spec := Classical.choose_spec (Nat.find_spec (hexU r))
  have hU_closed : Closed r U := hU_spec.1
  have hU_min : ∀ V : Finset (Fin π.length), Closed r V → U.card ≤ V.card := by
    intro V hV
    rw [hU_spec.2]
    exact Nat.find_min' (hexU r) ⟨V, hV, rfl⟩
  let Uax := U.filter (fun i => (step i).isNone)
  let Ures := U.filter (fun i => (step i).isSome)
  have hpart : Uax.card + Ures.card = U.card := by
    have hdisj : Disjoint Uax Ures := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      have ha := (Finset.mem_filter.mp h1).2
      have hr := (Finset.mem_filter.mp h2).2
      cases h : step i <;> simp [h] at ha hr
    have hunion : Uax ∪ Ures = U := by
      ext i; simp only [Uax, Ures, Finset.mem_union, Finset.mem_filter]
      cases step i <;> simp
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  let par (i : Fin π.length) : Finset (Fin π.length) :=
    match step i with | none => ∅ | some (j, k) => {j, k}
  have hcover_gen : ∀ rt (W : Finset (Fin π.length)),
      Closed rt W → (∀ V, Closed rt V → W.card ≤ V.card) →
      W.erase rt ⊆ (W.filter (fun i => (step i).isSome)).biUnion par := by
    intro rt W hWc hWm u hu
    obtain ⟨hne, huW⟩ := Finset.mem_erase.mp hu
    by_contra hnot
    have hce : Closed rt (W.erase u) := by
      refine ⟨Finset.mem_erase.mpr ⟨Ne.symm hne, hWc.1⟩, ?_⟩
      intro i hi j k hsi
      have hiW := Finset.mem_of_mem_erase hi
      obtain ⟨hjW, hkW⟩ := hWc.2 i hiW j k hsi
      have hiRes : i ∈ W.filter (fun i => (step i).isSome) := Finset.mem_filter.mpr ⟨hiW, by simp [hsi]⟩
      have hju : j ≠ u := fun heq => hnot (Finset.mem_biUnion.mpr ⟨i, hiRes, by simp [par, hsi, heq]⟩)
      have hku : k ≠ u := fun heq => hnot (Finset.mem_biUnion.mpr ⟨i, hiRes, by simp [par, hsi, heq]⟩)
      exact ⟨Finset.mem_erase.mpr ⟨hju, hjW⟩, Finset.mem_erase.mpr ⟨hku, hkW⟩⟩
    have hle := hWm (W.erase u) hce
    have hlt := Finset.card_erase_lt_of_mem huW
    omega
  have hcover := hcover_gen r U hU_closed hU_min
  have hbound_erase : (U.erase r).card ≤ 2 * Ures.card := by
    calc (U.erase r).card
        ≤ (Ures.biUnion par).card := Finset.card_le_card hcover
      _ ≤ ∑ i ∈ Ures, (par i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ Ures, 2 := by
          apply Finset.sum_le_sum; intro i _
          dsimp only [par]; cases step i with | none => simp | some p => exact Finset.card_le_two
      _ = 2 * Ures.card := by simp [mul_comm]
  have hsound : ∀ (rt : Fin π.length) (W : Finset (Fin π.length)), Closed rt W →
      ∀ α : Fin n → Bool,
        (∀ i ∈ W, (step i).isNone = true → ClauseSat α π[i]) → ClauseSat α π[rt] := by
    intro rt W hWc α hax
    have hsat : ∀ d : ℕ, ∀ i : Fin π.length, π.length - 1 - i.val ≤ d → i ∈ W → ClauseSat α π[i] := by
      intro d
      induction d with
      | zero =>
        intro i hd hiW
        have hsi := hstep i
        cases h : step i with
        | none => exact hax i hiW (by simp [h])
        | some p => rw [h] at hsi; omega
      | succ d ih =>
        intro i hd hiW
        have hsi := hstep i
        cases h : step i with
        | none => exact hax i hiW (by simp [h])
        | some p =>
          rw [h] at hsi
          obtain ⟨hij, hik, hres⟩ := hsi
          obtain ⟨hjW, hkW⟩ := hWc.2 i hiW p.1 p.2 h
          exact resolvent_sound hres (ih p.1 (by omega) hjW) (ih p.2 (by omega) hkW)
    exact hsat π.length rt (by omega) hWc.1
  let S : Finset (Clause (Fin n)) := Uax.image (fun i => π[i])
  have hS_H : ∀ C ∈ S, C ∈ H := by
    intro C hC
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hC
    have hnone := (Finset.mem_filter.mp hi).2
    have hsi := hstep i
    cases h : step i with
    | none => rw [h] at hsi; exact hsi
    | some _ => simp [h] at hnone
  have hS_unsat : ∀ α : Fin n → Bool, ¬ ∀ C ∈ S, ClauseSat α C := by
    intro α hα
    have hsat := hsound r U hU_closed α (fun i hi hnone =>
      hα π[i] (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hnone⟩, rfl⟩))
    have hrempty : π[r] = ∅ := hr0_eq
    rw [hrempty] at hsat
    obtain ⟨l, hl, _⟩ := hsat
    exact Finset.notMem_empty l hl
  have h2g : 2 * g ≤ S.card := two_mul_g_le_card hmin (fun C hC => hH (hS_H C hC)) hS_unsat
  have hSUax : S.card ≤ Uax.card := Finset.card_image_le
  have hr_card : (U.erase r).card = U.card - 1 := Finset.card_erase_of_mem hU_closed.1
  have hU_pos : 1 ≤ U.card := Finset.one_le_card.mpr ⟨r, hU_closed.1⟩
  have hU_le : U.card ≤ π.length := by
    calc U.card ≤ (Finset.univ : Finset (Fin π.length)).card := Finset.card_le_univ U
      _ = π.length := Fintype.card_fin π.length
  have hUax_eq : Uax.card = 2 * g := by omega
  have hUres_eq : Ures.card = 2 * g - 1 := by omega
  have hU_eq : U.card = 4 * g - 1 := by omega
  have hbi_eq : (Ures.biUnion par).card = ∑ i ∈ Ures, (par i).card := by
    have h1 : (U.erase r).card ≤ (Ures.biUnion par).card := Finset.card_le_card hcover
    have h2 : (Ures.biUnion par).card ≤ ∑ i ∈ Ures, (par i).card := Finset.card_biUnion_le
    have h3 : ∑ i ∈ Ures, (par i).card ≤ 2 * Ures.card := by
      calc ∑ i ∈ Ures, (par i).card ≤ ∑ _i ∈ Ures, 2 := by
            apply Finset.sum_le_sum; intro i _
            dsimp only [par]; cases step i with | none => simp | some p => exact Finset.card_le_two
        _ = 2 * Ures.card := by simp [mul_comm]
    omega
  have hpar_disj := biUnion_pairwise_disjoint_of_card_eq Ures par hbi_eq
  have hr_not_none : (step r).isNone = false := by
    by_contra h
    have hnone : step r = none := by cases hs : step r <;> simp_all
    have hrH := hstep r
    rw [hnone] at hrH
    obtain ⟨e, a, heq⟩ := hH hrH
    have hrempty : π[r] = ∅ := hr0_eq
    rw [hrempty] at heq
    have : (left e, !a) ∈ (∅ : Clause (Fin n)) := by rw [heq]; simp [cl]
    exact Finset.notMem_empty _ this
  obtain ⟨rT, rF, hr_step⟩ : ∃ rT rF, step r = some (rT, rF) := by
    cases hs : step r with
    | none => simp [hs] at hr_not_none
    | some p => exact ⟨p.1, p.2, rfl⟩
  have hr_spec := hstep r
  rw [hr_step] at hr_spec
  obtain ⟨hr_ltT, hr_ltF, hr_res⟩ := hr_spec
  have hr_empty : π[r] = ∅ := hr0_eq
  rw [hr_empty] at hr_res
  obtain ⟨root, hrootT, hrootF, hroot_eq⟩ := hr_res
  have hπT : π[rT] = {(root, true)} := by
    ext l
    simp only [Finset.mem_singleton]
    constructor
    · intro hl
      by_contra hne
      have : l ∈ (∅ : Clause (Fin n)) := by
        rw [hroot_eq]; exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hl⟩)
      exact Finset.notMem_empty l this
    · rintro rfl; exact hrootT
  have hπF : π[rF] = {(root, false)} := by
    ext l
    simp only [Finset.mem_singleton]
    constructor
    · intro hl
      by_contra hne
      have : l ∈ (∅ : Clause (Fin n)) := by
        rw [hroot_eq]; exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne, hl⟩)
      exact Finset.notMem_empty l this
    · rintro rfl; exact hrootF
  let UT := Classical.choose (Nat.find_spec (hexU rT))
  have hUT_spec := Classical.choose_spec (Nat.find_spec (hexU rT))
  have hUT_closed : Closed rT UT := hUT_spec.1
  have hUT_min : ∀ V, Closed rT V → UT.card ≤ V.card := fun V hV => by
    rw [hUT_spec.2]; exact Nat.find_min' (hexU rT) ⟨V, hV, rfl⟩
  let UF := Classical.choose (Nat.find_spec (hexU rF))
  have hUF_spec := Classical.choose_spec (Nat.find_spec (hexU rF))
  have hUF_closed : Closed rF UF := hUF_spec.1
  have hUF_min : ∀ V, Closed rF V → UF.card ≤ V.card := fun V hV => by
    rw [hUF_spec.2]; exact Nat.find_min' (hexU rF) ⟨V, hV, rfl⟩
  have hUT_sub_U : UT ⊆ U := by
    have hClosed_inter : Closed rT (UT ∩ U) := by
      refine ⟨Finset.mem_inter.mpr ⟨hUT_closed.1, (hU_closed.2 r hU_closed.1 rT rF hr_step).1⟩, ?_⟩
      intro i hi j k hsi
      obtain ⟨hi1, hi2⟩ := Finset.mem_inter.mp hi
      obtain ⟨hj1, hk1⟩ := hUT_closed.2 i hi1 j k hsi
      obtain ⟨hj2, hk2⟩ := hU_closed.2 i hi2 j k hsi
      exact ⟨Finset.mem_inter.mpr ⟨hj1, hj2⟩, Finset.mem_inter.mpr ⟨hk1, hk2⟩⟩
    have hle := hUT_min (UT ∩ U) hClosed_inter
    have hsub := Finset.inter_subset_left (s₁ := UT) (s₂ := U)
    have heq := Finset.eq_of_subset_of_card_le hsub hle
    rw [← heq]; exact Finset.inter_subset_right
  have hUF_sub_U : UF ⊆ U := by
    have hClosed_inter : Closed rF (UF ∩ U) := by
      refine ⟨Finset.mem_inter.mpr ⟨hUF_closed.1, (hU_closed.2 r hU_closed.1 rT rF hr_step).2⟩, ?_⟩
      intro i hi j k hsi
      obtain ⟨hi1, hi2⟩ := Finset.mem_inter.mp hi
      obtain ⟨hj1, hk1⟩ := hUF_closed.2 i hi1 j k hsi
      obtain ⟨hj2, hk2⟩ := hU_closed.2 i hi2 j k hsi
      exact ⟨Finset.mem_inter.mpr ⟨hj1, hj2⟩, Finset.mem_inter.mpr ⟨hk1, hk2⟩⟩
    have hle := hUF_min (UF ∩ U) hClosed_inter
    have hsub := Finset.inter_subset_left (s₁ := UF) (s₂ := U)
    have heq := Finset.eq_of_subset_of_card_le hsub hle
    rw [← heq]; exact Finset.inter_subset_right
  have hge_of_min : ∀ rt (W : Finset (Fin π.length)),
      Closed rt W → (∀ V, Closed rt V → W.card ≤ V.card) →
      ∀ u ∈ W, rt.val ≤ u.val := by
    intro rt W hWc hWm u hu
    by_contra hlt
    have hce : Closed rt (W.filter (fun i => rt.val ≤ i.val)) := by
      refine ⟨Finset.mem_filter.mpr ⟨hWc.1, le_rfl⟩, ?_⟩
      intro i hi j k hsi
      obtain ⟨hiW, hige⟩ := Finset.mem_filter.mp hi
      obtain ⟨hjW, hkW⟩ := hWc.2 i hiW j k hsi
      have hsi' := hstep i
      rw [hsi] at hsi'
      exact ⟨Finset.mem_filter.mpr ⟨hjW, by omega⟩, Finset.mem_filter.mpr ⟨hkW, by omega⟩⟩
    have hle := hWm _ hce
    have hlt' : (W.filter (fun i => rt.val ≤ i.val)).card < W.card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.filter_subset _ _, fun heq => ?_⟩
      have : u ∈ W.filter (fun i => rt.val ≤ i.val) := by rw [heq]; exact hu
      have := (Finset.mem_filter.mp this).2
      omega
    omega
  have hr_Ures : r ∈ Ures := Finset.mem_filter.mpr ⟨hU_closed.1, by simp [hr_step]⟩
  have hUT_UF_disj : Disjoint UT UF := by
    rw [Finset.disjoint_left]
    by_contra hnot
    push Not at hnot
    have hex : ∃ k, ∃ u : Fin π.length, u ∈ UT ∧ u ∈ UF ∧ u.val = k := by
      obtain ⟨u, hu1, hu2⟩ := hnot; exact ⟨u.val, u, hu1, hu2, rfl⟩
    obtain ⟨u, huT, huF, huval⟩ := Nat.find_spec hex
    have hrTF_ne : rT ≠ rF := by
      intro heq
      have hsum_le : ∑ i ∈ Ures.erase r, (par i).card ≤ 2 * (Ures.erase r).card := by
        calc ∑ i ∈ Ures.erase r, (par i).card ≤ ∑ _i ∈ Ures.erase r, 2 := by
              apply Finset.sum_le_sum; intro i _
              dsimp only [par]; cases step i with | none => simp | some p => exact Finset.card_le_two
          _ = 2 * (Ures.erase r).card := by simp [mul_comm]
      have hsum_eq := Finset.add_sum_erase Ures (fun i => (par i).card) hr_Ures
      have her : (Ures.erase r).card = Ures.card - 1 := Finset.card_erase_of_mem hr_Ures
      have h1 : (U.erase r).card ≤ (Ures.biUnion par).card := Finset.card_le_card hcover
      have hpar1 : (par r).card = 1 := by simp [par, hr_step, heq]
      omega
    have hne_rT : u ≠ rT := by
      intro heq
      rw [heq] at huF
      have hcovF := hcover_gen rF UF hUF_closed hUF_min (Finset.mem_erase.mpr ⟨hrTF_ne, huF⟩)
      obtain ⟨j, hjF, hjpar⟩ := Finset.mem_biUnion.mp hcovF
      have hjUres : j ∈ Ures := Finset.mem_filter.mpr ⟨hUF_sub_U (Finset.mem_filter.mp hjF).1, (Finset.mem_filter.mp hjF).2⟩
      have hjne : j ≠ r := by
        have := hge_of_min rF UF hUF_closed hUF_min j (Finset.mem_filter.mp hjF).1
        intro hjr; rw [hjr] at this; omega
      have hdisj := hpar_disj j hjUres r hr_Ures hjne
      exact Finset.disjoint_left.mp hdisj hjpar (by simp [par, hr_step])
    have hne_rF : u ≠ rF := by
      intro heq
      rw [heq] at huT
      have hcovT := hcover_gen rT UT hUT_closed hUT_min (Finset.mem_erase.mpr ⟨Ne.symm hrTF_ne, huT⟩)
      obtain ⟨j, hjT, hjpar⟩ := Finset.mem_biUnion.mp hcovT
      have hjUres : j ∈ Ures := Finset.mem_filter.mpr ⟨hUT_sub_U (Finset.mem_filter.mp hjT).1, (Finset.mem_filter.mp hjT).2⟩
      have hjne : j ≠ r := by
        have := hge_of_min rT UT hUT_closed hUT_min j (Finset.mem_filter.mp hjT).1
        intro hjr; rw [hjr] at this; omega
      have hdisj := hpar_disj j hjUres r hr_Ures hjne
      exact Finset.disjoint_left.mp hdisj hjpar (by simp [par, hr_step])
    have hcovT := hcover_gen rT UT hUT_closed hUT_min (Finset.mem_erase.mpr ⟨hne_rT, huT⟩)
    have hcovF := hcover_gen rF UF hUF_closed hUF_min (Finset.mem_erase.mpr ⟨hne_rF, huF⟩)
    obtain ⟨j1, hj1, hj1par⟩ := Finset.mem_biUnion.mp hcovT
    obtain ⟨j2, hj2, hj2par⟩ := Finset.mem_biUnion.mp hcovF
    have hj1U : j1 ∈ Ures := Finset.mem_filter.mpr ⟨hUT_sub_U (Finset.mem_filter.mp hj1).1, (Finset.mem_filter.mp hj1).2⟩
    have hj2U : j2 ∈ Ures := Finset.mem_filter.mpr ⟨hUF_sub_U (Finset.mem_filter.mp hj2).1, (Finset.mem_filter.mp hj2).2⟩
    have hj12 : j1 = j2 := by
      by_contra hne
      exact Finset.disjoint_left.mp (hpar_disj j1 hj1U j2 hj2U hne) hj1par hj2par
    subst hj12
    have hj1_lt : j1.val < u.val := by
      have hsi := hstep j1
      cases hs : step j1 with
      | none => simp [par, hs] at hj1par
      | some p =>
        rw [hs] at hsi
        simp [par, hs] at hj1par
        rcases hj1par with rfl | rfl <;> omega
    exact Nat.find_min hex (by omega) ⟨j1, (Finset.mem_filter.mp hj1).1, (Finset.mem_filter.mp hj2).1, rfl⟩
  let UaxT := UT.filter (fun i => (step i).isNone)
  let UaxF := UF.filter (fun i => (step i).isNone)
  let ST := UaxT.image (fun i => π[i])
  let SF := UaxF.image (fun i => π[i])
  have hST_H : ∀ C ∈ ST, C ∈ H := by
    intro C hC
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hC
    have hnone := (Finset.mem_filter.mp hi).2
    have hsi := hstep i
    cases h : step i with
    | none => rw [h] at hsi; exact hsi
    | some _ => simp [h] at hnone
  have hSF_H : ∀ C ∈ SF, C ∈ H := by
    intro C hC
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hC
    have hnone := (Finset.mem_filter.mp hi).2
    have hsi := hstep i
    cases h : step i with
    | none => rw [h] at hsi; exact hsi
    | some _ => simp [h] at hnone
  have hST_unsat : ∀ α : Fin n → Bool, α root = false → ∃ C ∈ ST, ¬ ClauseSat α C := by
    intro α hα
    by_contra hall
    push Not at hall
    have hsat := hsound rT UT hUT_closed α (fun i hi hnone =>
      hall π[i] (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hnone⟩, rfl⟩))
    rw [hπT] at hsat
    obtain ⟨l, hl, hla⟩ := hsat
    simp only [Finset.mem_singleton] at hl
    subst hl
    simp [hα] at hla
  have hSF_unsat : ∀ α : Fin n → Bool, α root = true → ∃ C ∈ SF, ¬ ClauseSat α C := by
    intro α hα
    by_contra hall
    push Not at hall
    have hsat := hsound rF UF hUF_closed α (fun i hi hnone =>
      hall π[i] (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hnone⟩, rfl⟩))
    rw [hπF] at hsat
    obtain ⟨l, hl, hla⟩ := hsat
    simp only [Finset.mem_singleton] at hl
    subst hl
    simp [hα] at hla
  have hg_le_core : ∀ (T : Finset (Clause (Fin n))) (start : Bool),
      (∀ C ∈ T, C ∈ H) →
      (∀ α : Fin n → Bool, α root = start → ∃ C ∈ T, ¬ ClauseSat α C) →
      g ≤ T.card := by
    intro T start hTH hTu
    obtain ⟨C0, hC0, _⟩ := hTu (fun _ => start) rfl
    obtain ⟨e0, _, _⟩ := hH (hTH C0 hC0)
    have hm : 0 < m := Fin.pos e0
    let eOf : {C // C ∈ T} → Fin m := fun c => Classical.choose (hH (hTH c.1 c.2))
    let PT : Fin m → Prop := fun e => ∃ c : {C // C ∈ T}, eOf c = e
    have hPT_unbal : ¬ ∃ β : Fin n → Bool, ∀ e, PT e → β (right e) = (β (left e) ^^ sign e) := by
      rintro ⟨β, hβ⟩
      let β' : Fin n → Bool := if β root = start then β else fun x => !(β x)
      have hβ'r : β' root = start := by
        dsimp only [β']; split_ifs with h
        · exact h
        · dsimp only; revert h; generalize β root = x; cases x <;> cases start <;> decide
      obtain ⟨C, hCT, hnot⟩ := hTu β' hβ'r
      apply hnot
      have hcl := Classical.choose_spec (Classical.choose_spec (hH (hTH C hCT)))
      rw [hcl]
      apply cl_sat_of_balanced
      dsimp only [β']; split_ifs
      · exact hβ (eOf ⟨C, hCT⟩) ⟨⟨C, hCT⟩, rfl⟩
      · change (!(β (right (eOf ⟨C, hCT⟩)))) = ((!(β (left (eOf ⟨C, hCT⟩)))) ^^ sign (eOf ⟨C, hCT⟩))
        rw [hβ (eOf ⟨C, hCT⟩) ⟨⟨C, hCT⟩, rfl⟩]
        cases β (left (eOf ⟨C, hCT⟩)) <;> cases sign (eOf ⟨C, hCT⟩) <;> rfl
    obtain ⟨k, v0, e0w, _, _, hvk, hodd, hstep', _, he_inj⟩ :=
      minimal_neg_cycle (exists_negWalk_of_not_balanced hm hPT_unbal)
    have hgk : g ≤ k := by
      by_contra hlt
      exact hmin k (by omega) ⟨v0, e0w, hvk, hodd, fun j hj => (hstep' j hj).2⟩
    let cAt : Fin k → {C // C ∈ T} := fun j => Classical.choose (hstep' j.val j.isLt).1
    have hcAt_e : ∀ j, eOf (cAt j) = e0w j.val := fun j => Classical.choose_spec (hstep' j.val j.isLt).1
    have hcAt_inj : Function.Injective cAt := by
      intro i j hij
      exact Fin.ext (he_inj i.val i.isLt j.val j.isLt (by rw [← hcAt_e i, ← hcAt_e j, hij]))
    calc g ≤ k := hgk
      _ = (Finset.univ : Finset (Fin k)).card := (Fintype.card_fin k).symm
      _ = (Finset.univ.image cAt).card := (Finset.card_image_of_injective _ hcAt_inj).symm
      _ ≤ Fintype.card {C // C ∈ T} := Finset.card_le_univ _
      _ = T.card := Fintype.card_coe T
  have hgT : g ≤ ST.card := hg_le_core ST false hST_H hST_unsat
  have hgF : g ≤ SF.card := hg_le_core SF true hSF_H hSF_unsat
  have hST_le : ST.card ≤ UaxT.card := Finset.card_image_le
  have hSF_le : SF.card ≤ UaxF.card := Finset.card_image_le
  have hUaxTF_sum : UaxT.card + UaxF.card ≤ Uax.card := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hUT_UF_disj)]
    apply Finset.card_le_card
    intro i hi
    rcases Finset.mem_union.mp hi with h1 | h2
    · exact Finset.mem_filter.mpr ⟨hUT_sub_U (Finset.mem_filter.mp h1).1, (Finset.mem_filter.mp h1).2⟩
    · exact Finset.mem_filter.mpr ⟨hUF_sub_U (Finset.mem_filter.mp h2).1, (Finset.mem_filter.mp h2).2⟩
  have hST_eq : ST.card = g := by omega
  have hSF_eq : SF.card = g := by omega
  refine ⟨root, fun start => ?_⟩
  cases start
  · exact walk_of_unit_core hmin hH root false hST_H hST_eq hST_unsat
  · exact walk_of_unit_core hmin hH root true hSF_H hSF_eq hSF_unsat

end PEqualNP.Outside.L_pcx_286_aux

theorem PEqualNP.Outside.L_pcx_286 : (∀ (n m : ℕ) (left right : Fin m → Fin n) (sign : Fin m → Bool),
  let cl := fun (e : Fin m) (a : Bool) =>
    ({(left e, !a), (right e, a ^^ sign e)} : PEqualNP.ProofComplexity.Clause (Fin n))
  let negative := fun k : ℕ =>
    ∃ (v : ℕ → Fin n) (edge : ℕ → Fin m), v 0 = v k ∧
      Odd (((Finset.range k).filter (fun j => sign (edge j) = true)).card) ∧
      ∀ j < k, (v j = left (edge j) ∧ v (j+1) = right (edge j)) ∨
        (v j = right (edge j) ∧ v (j+1) = left (edge j))
  ∀ g : ℕ, negative g → (∀ k < g, ¬ negative k) →
    ∀ H : Set (PEqualNP.ProofComplexity.Clause (Fin n)), H ⊆ {C | ∃ e a, C = cl e a} →
  ((∃ π, PEqualNP.ProofComplexity.IsRefutation H π ∧ π.length+1 ≤ 4*g) ↔ ∃ root : Fin n, ∀ start : Bool,
        ∃ (v : ℕ → Fin n) (edge : ℕ → Fin m) (val : ℕ → Bool),
          v 0 = root ∧ v g = root ∧ val 0 = start ∧ val g = !start ∧
          ∀ j < g,
            ((v j = left (edge j) ∧ v (j+1) = right (edge j)) ∨
              (v j = right (edge j) ∧ v (j+1) = left (edge j))) ∧
            val (j+1) = (val j ^^ sign (edge j)) ∧
            ({(v j, !(val j)), (v (j+1), val (j+1))} : PEqualNP.ProofComplexity.Clause (Fin n)) ∈ H)) := by
  intro n m left right sign cl negative g hg hmin H hH
  constructor
  · rintro ⟨π, href, hlen⟩
    exact PEqualNP.Outside.L_pcx_286_aux.forwards_dir hg hmin hH href hlen
  · intro hw
    exact PEqualNP.Outside.L_pcx_286_aux.backwards_dir hg hmin hw
