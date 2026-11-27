import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_843_aux

def runDef {s : ℕ} (z : Fin s) (n : Fin s → Bool → Option (Fin s)) (b : ℕ) (w : Fin b → Bool) :
    Option (Fin s) :=
  (List.ofFn w).foldl (fun (x : Option (Fin s)) (bit : Bool) => x.bind (fun i => n i bit)) (some z)

def runFrom {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (x : Option (Fin s)) (L : List Bool) :
    Option (Fin s) :=
  L.foldl (fun (y : Option (Fin s)) (bit : Bool) => y.bind (fun i => n i bit)) x

lemma runFrom_none {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (L : List Bool) :
    runFrom n none L = none := by
  induction L with
  | nil => rfl
  | cons a t ih => exact ih

lemma runFrom_append {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (x : Option (Fin s))
    (L1 L2 : List Bool) :
    runFrom n x (L1 ++ L2) = runFrom n (runFrom n x L1) L2 := by
  dsimp only [runFrom]
  exact List.foldl_append

lemma runDef_eq_runFrom {s : ℕ} (z : Fin s) (n : Fin s → Bool → Option (Fin s)) (b : ℕ)
    (w : Fin b → Bool) :
    runDef z n b w = runFrom n (some z) (List.ofFn w) := rfl

lemma list_ofFn_split {b k : ℕ} (hk : k ≤ b) (w : Fin b → Bool) :
    List.ofFn w =
      List.ofFn (fun i : Fin k => w ⟨i.val, lt_of_lt_of_le i.isLt hk⟩) ++
      List.ofFn (fun i : Fin (b - k) => w ⟨k + i.val, by omega⟩) := by
  apply List.ext_getElem
  · simp [hk]
  · intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn]
    split_ifs with hi
    · simp
    · congr 1
      apply Fin.ext
      dsimp only
      omega

lemma runDef_prefix_isSome {s : ℕ} (z : Fin s) (n : Fin s → Bool → Option (Fin s))
    {b k : ℕ} (hk : k ≤ b) (w : Fin b → Bool)
    (h : (runDef z n b w).isSome = true) :
    (runDef z n k (fun i : Fin k => w ⟨i.val, lt_of_lt_of_le i.isLt hk⟩)).isSome = true := by
  rw [runDef_eq_runFrom, list_ofFn_split hk w, runFrom_append] at h
  cases hpref : runFrom n (some z) (List.ofFn fun i : Fin k => w ⟨i.val, lt_of_lt_of_le i.isLt hk⟩) with
  | none =>
    rw [hpref, runFrom_none] at h
    simp at h
  | some y =>
    change (runFrom n (some z) _).isSome = true
    rw [hpref]
    rfl

lemma runDef_succ {s : ℕ} (z : Fin s) (n : Fin s → Bool → Option (Fin s))
    (b : ℕ) (w : Fin (b + 1) → Bool) :
    runDef z n (b + 1) w =
      (runDef z n b (fun i : Fin b => w i.castSucc)).bind (fun x => n x (w (Fin.last b))) := by
  rw [runDef_eq_runFrom, runDef_eq_runFrom, List.ofFn_succ']
  have h : List.ofFn w = List.ofFn (fun i : Fin b => w i.castSucc) ++ [w (Fin.last b)] := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn, List.getElem_singleton]
      split_ifs with hi
      · rfl
      · congr 1
        apply Fin.ext
        dsimp only [Fin.last]
        simp only [List.length_ofFn] at h1
        omega
  rw [← List.ofFn_succ', h, runFrom_append]
  rfl

lemma runFrom_repeat {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (x : Fin s) (L : List Bool)
    (hcyc : runFrom n (some x) L = some x) (m : ℕ) :
    runFrom n (some x) (List.flatten (List.replicate m L)) = some x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, List.flatten_cons, runFrom_append, hcyc, ih]

lemma list_ofFn_get {b : ℕ} (L : List Bool) (hL : L.length = b) :
    List.ofFn (fun i : Fin b => L[i.val]'(by omega)) = L := by
  apply List.ext_getElem
  · simp [hL]
  · intro i h1 h2
    simp

lemma prefix_eq_of_extend {s : ℕ} (z : Fin s) (n : Fin s → Bool → Option (Fin s))
    (h1 : ∀ B : ℕ, ∃ b ≥ B,
      ((Finset.univ : Finset (Fin b → Bool)).filter (fun w => (runDef z n b w).isSome)).card = 1)
    (u : ℕ → Bool)
    (hu : ∀ b : ℕ, (runDef z n b (fun i : Fin b => u i.val)).isSome = true)
    (d : ℕ) (w : Fin d → Bool)
    (hext : ∀ B : ℕ, ∃ (b : ℕ) (hb : d ≤ b) (hbB : B ≤ b) (W : Fin b → Bool),
      (runDef z n b W).isSome = true ∧ ∀ i : Fin d, W ⟨i.val, lt_of_lt_of_le i.isLt hb⟩ = w i) :
    ∀ i : Fin d, w i = u i.val := by
  obtain ⟨b, hbd, _, W, hW, hW_pref⟩ := hext d
  obtain ⟨N, hNb, hN1⟩ := h1 b
  obtain ⟨M, hMd, hMN, W2, hW2, hW2_pref⟩ := hext N
  have hW2N : (runDef z n N (fun i : Fin N => W2 ⟨i.val, lt_of_lt_of_le i.isLt hMN⟩)).isSome = true :=
    runDef_prefix_isSome z n hMN W2 hW2
  have huN : (runDef z n N (fun i : Fin N => u i.val)).isSome = true := hu N
  have hmem1 : (fun i : Fin N => W2 ⟨i.val, lt_of_lt_of_le i.isLt hMN⟩) ∈
      (Finset.univ : Finset (Fin N → Bool)).filter (fun w => (runDef z n N w).isSome) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hW2N⟩
  have hmem2 : (fun i : Fin N => u i.val) ∈
      (Finset.univ : Finset (Fin N → Bool)).filter (fun w => (runDef z n N w).isSome) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, huN⟩
  have heq : (fun i : Fin N => W2 ⟨i.val, lt_of_lt_of_le i.isLt hMN⟩) =
      (fun i : Fin N => u i.val) :=
    Finset.card_le_one_iff.mp (le_of_eq hN1) hmem1 hmem2
  intro i
  have h1' := hW2_pref i
  have h2' := congrFun heq ⟨i.val, lt_of_lt_of_le i.isLt (le_trans hbd hNb)⟩
  dsimp only at h2'
  rw [← h1', h2']

lemma det_eq_zero_of_row_dep {R : Type} [Fintype R] [DecidableEq R]
    (M : Matrix R R ℤ) (w : R → ℤ) (hw : w ≠ 0)
    (hdep : ∀ k : R, ∑ i : R, w i * M i k = 0) :
    M.det = 0 := by
  have hmul : M.transpose.mulVec w = 0 := by
    ext k
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply]
    have := hdep k
    convert this using 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hadj := congrArg (fun v => M.transpose.adjugate.mulVec v) hmul
  rw [Matrix.mulVec_zero, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.det_transpose,
    Matrix.smul_mulVec, Matrix.one_mulVec] at hadj
  have hex : ∃ i : R, w i ≠ 0 := by
    by_contra hall
    apply hw
    ext i
    by_contra hne
    exact hall ⟨i, hne⟩
  obtain ⟨i, hi⟩ := hex
  have h0 : M.det * w i = 0 := by
    have := congrFun hadj i
    simpa [Pi.smul_apply, smul_eq_mul] using this
  exact (mul_eq_zero.mp h0).resolve_right hi

end PEqualNP.Outside.L_lib_843_aux

open PEqualNP.Outside.L_lib_843_aux in
theorem PEqualNP.Outside.L_lib_843 : (∀ (s : ℕ) (z : Fin s) (n : Fin s → Bool → Option (Fin s)),
  let run := fun (b : ℕ) (w : Fin b → Bool) =>
    (List.ofFn w).foldl (fun (x : Option (Fin s)) (bit : Bool) =>
      x.bind (fun i => n i bit)) (some z)
  let live := fun b : ℕ =>
    ((Finset.univ : Finset (Fin b → Bool)).filter (fun w => (run b w).isSome)).card
  (∀ B : ℕ, ∃ b ≥ B, live b = 1) →
    ∃ l : ℕ, 0 < l ∧ l ≤ s ∧
      (∃ (a : Fin l ↪ Fin s) (c : Fin l → Bool),
        (∃ (b : ℕ) (w : Fin b → Bool) (j : Fin l), run b w = some (a j)) ∧
        ∀ i : Fin l, ∃ j : Fin l, j.val = (i.val+1) % l ∧ n (a i) (c i) = some (a j)) ∧
      (∀ b, live b ≤ 2^(s-l)) ∧
      ∀ (g : Fin s → Bool → ℤ) (v : Fin s → ℝ),
        (∀ i, 2*v i = ∑ bit : Bool, (n i bit).elim (g i bit : ℝ) v) →
        ∃ m : ℤ, ((2^(s-l)*(2^l-1) : ℕ) : ℝ)*v z = m) := by
  classical
  intro s z n run live h1
  have hrun_eq : run = runDef z n := rfl
  have h1' : ∀ B : ℕ, ∃ b ≥ B,
      ((Finset.univ : Finset (Fin b → Bool)).filter (fun w => (runDef z n b w).isSome)).card = 1 :=
    h1
  have h_ex_u : ∃ u : ℕ → Bool, ∀ b : ℕ, (runDef z n b (fun i : Fin b => u i.val)).isSome = true := by
    let pickB : ℕ → ℕ := fun t => Classical.choose (h1' (t + 1))
    have hpickB_ge : ∀ t, t + 1 ≤ pickB t := fun t => (Classical.choose_spec (h1' (t + 1))).1
    have hpickB_card : ∀ t,
        ((Finset.univ : Finset (Fin (pickB t) → Bool)).filter (fun w => (runDef z n (pickB t) w).isSome)).card = 1 :=
      fun t => (Classical.choose_spec (h1' (t + 1))).2
    have hpick_w : ∀ t, ∃ w : Fin (pickB t) → Bool, (runDef z n (pickB t) w).isSome = true := by
      intro t
      have hpos : 0 < ((Finset.univ : Finset (Fin (pickB t) → Bool)).filter (fun w => (runDef z n (pickB t) w).isSome)).card := by
        rw [hpickB_card t]; omega
      obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
      exact ⟨w, (Finset.mem_filter.mp hw).2⟩
    let wOf : ∀ t, Fin (pickB t) → Bool := fun t => Classical.choose (hpick_w t)
    have hwOf : ∀ t, (runDef z n (pickB t) (wOf t)).isSome = true :=
      fun t => Classical.choose_spec (hpick_w t)
    let u : ℕ → Bool := fun t => wOf t ⟨t, hpickB_ge t⟩
    refine ⟨u, fun b => ?_⟩
    obtain ⟨N, hNb, hN1⟩ := h1' b
    have hNpos : 0 < ((Finset.univ : Finset (Fin N → Bool)).filter (fun w => (runDef z n N w).isSome)).card := by
      rw [hN1]; omega
    obtain ⟨WN, hWN⟩ := Finset.card_pos.mp hNpos
    have hWN_live : (runDef z n N WN).isSome = true := (Finset.mem_filter.mp hWN).2
    have hagree : ∀ t : Fin b, WN ⟨t.val, lt_of_lt_of_le t.isLt hNb⟩ = u t.val := by
      intro t
      obtain ⟨M, hMge, hM1⟩ := h1' (max N (pickB t.val))
      have hMpos : 0 < ((Finset.univ : Finset (Fin M → Bool)).filter (fun w => (runDef z n M w).isSome)).card := by
        rw [hM1]; omega
      obtain ⟨WM, hWM⟩ := Finset.card_pos.mp hMpos
      have hWM_live : (runDef z n M WM).isSome = true := (Finset.mem_filter.mp hWM).2
      have hMN : N ≤ M := le_trans (le_max_left _ _) hMge
      have hMP : pickB t.val ≤ M := le_trans (le_max_right _ _) hMge
      have hprefN : (fun i : Fin N => WM ⟨i.val, lt_of_lt_of_le i.isLt hMN⟩) = WN :=
        Finset.card_le_one_iff.mp (le_of_eq hN1)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, runDef_prefix_isSome z n hMN WM hWM_live⟩)
          hWN
      have hprefP : (fun i : Fin (pickB t.val) => WM ⟨i.val, lt_of_lt_of_le i.isLt hMP⟩) = wOf t.val :=
        Finset.card_le_one_iff.mp (le_of_eq (hpickB_card t.val))
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, runDef_prefix_isSome z n hMP WM hWM_live⟩)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwOf t.val⟩)
      have h1_t := congrFun hprefN ⟨t.val, lt_of_lt_of_le t.isLt hNb⟩
      have h2_t := congrFun hprefP ⟨t.val, hpickB_ge t.val⟩
      dsimp only at h1_t h2_t
      rw [← h1_t, h2_t]
    have hpref_eq : (fun i : Fin b => u i.val) = (fun i : Fin b => WN ⟨i.val, lt_of_lt_of_le i.isLt hNb⟩) := by
      ext t; exact (hagree t).symm
    rw [hpref_eq]
    exact runDef_prefix_isSome z n hNb WN hWN_live
  obtain ⟨u, hu⟩ := h_ex_u
  let st : ℕ → Fin s := fun t => Option.get _ (hu t)
  have hst_run : ∀ t : ℕ, runDef z n t (fun i : Fin t => u i.val) = some (st t) :=
    fun t => (Option.some_get (hu t)).symm
  have hst_zero : st 0 = z := by
    have h0 := hst_run 0
    dsimp only [runDef] at h0
    simp only [List.ofFn_zero, List.foldl_nil] at h0
    exact (Option.some.inj h0).symm
  have hst_step : ∀ t : ℕ, n (st t) (u t) = some (st (t + 1)) := by
    intro t
    have h1_s := hst_run (t + 1)
    rw [runDef_succ] at h1_s
    change (runDef z n t (fun i : Fin t => u i.val)).bind (fun x => n x (u t)) = some (st (t + 1)) at h1_s
    rw [hst_run t] at h1_s
    exact h1_s
  have hex_rep : ∃ q : ℕ, ∃ p < q, st p = st q := by
    have hnot_inj : ¬ Function.Injective (fun i : Fin (s + 1) => st i.val) := by
      intro hinj
      have := Fintype.card_le_of_injective _ hinj
      simp at this
    rw [Function.Injective] at hnot_inj
    push Not at hnot_inj
    obtain ⟨i1, i2, heq, hne⟩ := hnot_inj
    have hne_val : i1.val ≠ i2.val := fun h => hne (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hne_val with hlt | hgt
    · exact ⟨i2.val, i1.val, hlt, heq⟩
    · exact ⟨i1.val, i2.val, hgt, heq.symm⟩
  let q := Nat.find hex_rep
  have hq_spec : ∃ p < q, st p = st q := Nat.find_spec hex_rep
  have hq_min : ∀ q' < q, ∀ p' < q', st p' ≠ st q' := by
    intro q' hq' p' hp' heq
    exact Nat.find_min hex_rep hq' ⟨p', hp', heq⟩
  have hq_le : q ≤ s := by
    by_contra hgt
    have hinj : Function.Injective (fun i : Fin (s + 1) => st i.val) := by
      intro i1 i2 heq
      by_contra hne
      have hne_val : i1.val ≠ i2.val := fun h => hne (Fin.ext h)
      rcases Nat.lt_or_gt_of_ne hne_val with hlt | hgt'
      · exact hq_min i2.val (by omega) i1.val hlt heq
      · exact hq_min i1.val (by omega) i2.val hgt' heq.symm
    have := Fintype.card_le_of_injective _ hinj
    simp at this
  obtain ⟨p, hpq, hst_pq⟩ := hq_spec
  let l := q - p
  have hl_pos : 0 < l := by omega
  have hl_le : l ≤ s := by omega
  let a : Fin l ↪ Fin s :=
    ⟨fun i => st (p + i.val), by
      intro i1 i2 h12
      by_contra hne
      have hne_val : i1.val ≠ i2.val := fun h => hne (Fin.ext h)
      rcases Nat.lt_or_gt_of_ne hne_val with hlt | hgt
      · exact hq_min (p + i2.val) (by omega) (p + i1.val) (by omega) h12
      · exact hq_min (p + i1.val) (by omega) (p + i2.val) (by omega) h12.symm⟩
  let c : Fin l → Bool := fun i => u (p + i.val)
  have ha_step : ∀ i : Fin l, ∃ j : Fin l, j.val = (i.val + 1) % l ∧ n (a i) (c i) = some (a j) := by
    intro i
    let j : Fin l := ⟨(i.val + 1) % l, Nat.mod_lt _ hl_pos⟩
    refine ⟨j, rfl, ?_⟩
    change n (st (p + i.val)) (u (p + i.val)) = some (st (p + j.val))
    rw [hst_step]
    congr 1
    by_cases hlt : i.val + 1 < l
    · have hjv : j.val = i.val + 1 := Nat.mod_eq_of_lt hlt
      rw [hjv, Nat.add_assoc]
    · have hi_last : i.val + 1 = l := by omega
      have hjv : j.val = 0 := by dsimp only [j]; rw [hi_last, Nat.mod_self]
      have hq_eq : p + i.val + 1 = q := by omega
      rw [hjv, add_zero, hq_eq, hst_pq]
  have ha_reach : ∃ (b : ℕ) (w : Fin b → Bool) (j : Fin l), run b w = some (a j) := by
    refine ⟨p, fun i : Fin p => u i.val, ⟨0, hl_pos⟩, ?_⟩
    rw [hrun_eq, hst_run p]
    rfl
  have hst_periodic : ∀ t : ℕ, st (p + t) = a ⟨t % l, Nat.mod_lt _ hl_pos⟩ := by
    intro t
    have hcycle_list : ∀ k : ℕ, ∃ j : Fin l, j.val = k % l ∧
        runFrom n (some (a ⟨0, hl_pos⟩)) (List.ofFn fun i : Fin k => c ⟨i.val % l, Nat.mod_lt _ hl_pos⟩) =
          some (a j) := by
      intro k
      induction k with
      | zero =>
        refine ⟨⟨0, hl_pos⟩, by simp, rfl⟩
      | succ k ih =>
        obtain ⟨jk, hjk, hrun_k⟩ := ih
        obtain ⟨j', hj', hstep_j⟩ := ha_step jk
        refine ⟨j', ?_, ?_⟩
        · rw [hj', hjk]
          calc (k % l + 1) % l = (k % l + 1 % l) % l := by rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
            _ = (k + 1) % l := (Nat.add_mod k 1 l).symm
        · have hlist : List.ofFn (fun i : Fin (k + 1) => c ⟨i.val % l, Nat.mod_lt _ hl_pos⟩) =
              List.ofFn (fun i : Fin k => c ⟨i.val % l, Nat.mod_lt _ hl_pos⟩) ++
                [c ⟨k % l, Nat.mod_lt _ hl_pos⟩] := by
            apply List.ext_getElem
            · simp
            · intro i h1_l h2_l
              simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn, List.getElem_singleton]
              split_ifs with hi
              · rfl
              · have hik : i = k := by simp only [List.length_ofFn] at h1_l; omega
                subst hik; rfl
          rw [hlist, runFrom_append, hrun_k]
          dsimp only [runFrom]
          simp only [List.foldl_cons, List.foldl_nil, Option.bind_some]
          have hjk_fin : (⟨k % l, Nat.mod_lt _ hl_pos⟩ : Fin l) = jk := Fin.ext hjk.symm
          rw [hjk_fin, hstep_j]
    have hext_cyc : ∀ B : ℕ, ∃ (b : ℕ) (hb : p + t ≤ b) (hbB : B ≤ b) (W : Fin b → Bool),
        (runDef z n b W).isSome = true ∧
        ∀ i : Fin (p + t), W ⟨i.val, lt_of_lt_of_le i.isLt hb⟩ =
          if hi : i.val < p then u i.val else c ⟨(i.val - p) % l, Nat.mod_lt _ hl_pos⟩ := by
      intro B
      let b := max (p + t) B
      let W : Fin b → Bool := fun i =>
        if i.val < p then u i.val else c ⟨(i.val - p) % l, Nat.mod_lt _ hl_pos⟩
      refine ⟨b, le_max_left _ _, le_max_right _ _, W, ?_, fun i => by dsimp only [W]; split_ifs <;> rfl⟩
      rw [runDef_eq_runFrom, list_ofFn_split (by omega : p ≤ b) W, runFrom_append]
      have hp_eq : List.ofFn (fun i : Fin p => W ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩) =
          List.ofFn (fun i : Fin p => u i.val) := by
        congr 1; ext i; dsimp only [W]; rw [if_pos i.isLt]
      rw [hp_eq]
      have hrunp : runFrom n (some z) (List.ofFn fun i : Fin p => u i.val) = some (a ⟨0, hl_pos⟩) := by
        rw [← runDef_eq_runFrom, hst_run p]; rfl
      rw [hrunp]
      have hsuf_eq : List.ofFn (fun i : Fin (b - p) => W ⟨p + i.val, by omega⟩) =
          List.ofFn (fun i : Fin (b - p) => c ⟨i.val % l, Nat.mod_lt _ hl_pos⟩) := by
        congr 1; ext i; dsimp only [W]
        have hnot : ¬ p + i.val < p := by omega
        rw [if_neg hnot]
        congr 1; apply Fin.ext; dsimp only; rw [Nat.add_sub_cancel_left]
      rw [hsuf_eq]
      obtain ⟨j, _, hrun_j⟩ := hcycle_list (b - p)
      rw [hrun_j]
      rfl
    have hpref_u := prefix_eq_of_extend z n h1' u hu (p + t)
      (fun i : Fin (p + t) => if i.val < p then u i.val else c ⟨(i.val - p) % l, Nat.mod_lt _ hl_pos⟩)
      hext_cyc
    have hrun_eq' : runDef z n (p + t) (fun i : Fin (p + t) => u i.val) =
        some (a ⟨t % l, Nat.mod_lt _ hl_pos⟩) := by
      have hfun : (fun i : Fin (p + t) => u i.val) =
          (fun i : Fin (p + t) => if i.val < p then u i.val else c ⟨(i.val - p) % l, Nat.mod_lt _ hl_pos⟩) := by
        ext i; exact (hpref_u i).symm
      rw [hfun, runDef_eq_runFrom, list_ofFn_split (by omega : p ≤ p + t), runFrom_append]
      have hp_eq : List.ofFn (fun i : Fin p =>
          if (⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩ : Fin (p + t)).val < p then u i.val
          else c ⟨(i.val - p) % l, Nat.mod_lt _ hl_pos⟩) = List.ofFn (fun i : Fin p => u i.val) := by
        congr 1; ext i; dsimp only; rw [if_pos i.isLt]
      rw [hp_eq]
      have hrunp : runFrom n (some z) (List.ofFn fun i : Fin p => u i.val) = some (a ⟨0, hl_pos⟩) := by
        rw [← runDef_eq_runFrom, hst_run p]; rfl
      rw [hrunp]
      have hsuf : List.ofFn (fun i : Fin (p + t - p) =>
          if (⟨p + i.val, by omega⟩ : Fin (p + t)).val < p then u (p + i.val)
          else c ⟨(p + i.val - p) % l, Nat.mod_lt _ hl_pos⟩) =
          List.ofFn (fun i : Fin t => c ⟨i.val % l, Nat.mod_lt _ hl_pos⟩) := by
        apply List.ext_getElem
        · simp
        · intro i h1_l h2_l
          simp only [List.getElem_ofFn]
          have hnot : ¬ p + i < p := by omega
          rw [if_neg hnot]
          congr 1; apply Fin.ext; dsimp only; rw [Nat.add_sub_cancel_left]
      rw [hsuf]
      obtain ⟨j, hj, hrun_j⟩ := hcycle_list t
      rw [hrun_j]
      congr 2
      exact Fin.ext hj
    rw [hst_run (p + t)] at hrun_eq'
    exact Option.some.inj hrun_eq'
  have hu_periodic : ∀ t : ℕ, u (p + t) = c ⟨t % l, Nat.mod_lt _ hl_pos⟩ := by
    intro t
    have hcycle_list : ∀ k : ℕ, ∃ j : Fin l, j.val = k % l ∧
        runFrom n (some (a ⟨0, hl_pos⟩)) (List.ofFn fun i : Fin k => c ⟨i.val % l, Nat.mod_lt _ hl_pos⟩) =
          some (a j) := by
      intro k
      induction k with
      | zero => refine ⟨⟨0, hl_pos⟩, by simp, rfl⟩
      | succ k ih =>
        obtain ⟨jk, hjk, hrun_k⟩ := ih
        obtain ⟨j', hj', hstep_j⟩ := ha_step jk
        refine ⟨j', ?_, ?_⟩
        · rw [hj', hjk]
          calc (k % l + 1) % l = (k % l + 1 % l) % l := by rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
            _ = (k + 1) % l := (Nat.add_mod k 1 l).symm
        · have hlist : List.ofFn (fun i : Fin (k + 1) => c ⟨i.val % l, Nat.mod_lt _ hl_pos⟩) =
              List.ofFn (fun i : Fin k => c ⟨i.val % l, Nat.mod_lt _ hl_pos⟩) ++
                [c ⟨k % l, Nat.mod_lt _ hl_pos⟩] := by
            apply List.ext_getElem
            · simp
            · intro i h1_l h2_l
              simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn, List.getElem_singleton]
              split_ifs with hi
              · rfl
              · have hik : i = k := by simp only [List.length_ofFn] at h1_l; omega
                subst hik; rfl
          rw [hlist, runFrom_append, hrun_k]
          dsimp only [runFrom]
          simp only [List.foldl_cons, List.foldl_nil, Option.bind_some]
          have hjk_fin : (⟨k % l, Nat.mod_lt _ hl_pos⟩ : Fin l) = jk := Fin.ext hjk.symm
          rw [hjk_fin, hstep_j]
    have hext_cyc : ∀ B : ℕ, ∃ (b : ℕ) (hb : p + t + 1 ≤ b) (hbB : B ≤ b) (W : Fin b → Bool),
        (runDef z n b W).isSome = true ∧
        ∀ i : Fin (p + t + 1), W ⟨i.val, lt_of_lt_of_le i.isLt hb⟩ =
          if i.val < p then u i.val else c ⟨(i.val - p) % l, Nat.mod_lt _ hl_pos⟩ := by
      intro B
      let b := max (p + t + 1) B
      let W : Fin b → Bool := fun i =>
        if i.val < p then u i.val else c ⟨(i.val - p) % l, Nat.mod_lt _ hl_pos⟩
      refine ⟨b, le_max_left _ _, le_max_right _ _, W, ?_, fun i => rfl⟩
      rw [runDef_eq_runFrom, list_ofFn_split (by omega : p ≤ b) W, runFrom_append]
      have hp_eq : List.ofFn (fun i : Fin p => W ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩) =
          List.ofFn (fun i : Fin p => u i.val) := by
        congr 1; ext i; dsimp only [W]; rw [if_pos i.isLt]
      rw [hp_eq]
      have hrunp : runFrom n (some z) (List.ofFn fun i : Fin p => u i.val) = some (a ⟨0, hl_pos⟩) := by
        rw [← runDef_eq_runFrom, hst_run p]; rfl
      rw [hrunp]
      have hsuf_eq : List.ofFn (fun i : Fin (b - p) => W ⟨p + i.val, by omega⟩) =
          List.ofFn (fun i : Fin (b - p) => c ⟨i.val % l, Nat.mod_lt _ hl_pos⟩) := by
        congr 1; ext i; dsimp only [W]
        have hnot : ¬ p + i.val < p := by omega
        rw [if_neg hnot]
        congr 1; apply Fin.ext; dsimp only; rw [Nat.add_sub_cancel_left]
      rw [hsuf_eq]
      obtain ⟨j, _, hrun_j⟩ := hcycle_list (b - p)
      rw [hrun_j]; rfl
    have hpref := prefix_eq_of_extend z n h1' u hu (p + t + 1)
      (fun i : Fin (p + t + 1) => if i.val < p then u i.val else c ⟨(i.val - p) % l, Nat.mod_lt _ hl_pos⟩)
      hext_cyc
    have hpt := hpref ⟨p + t, by omega⟩
    dsimp only at hpt
    have hnot : ¬ p + t < p := by omega
    rw [if_neg hnot] at hpt
    have hsub : p + t - p = t := by omega
    rw [← hpt]
    congr 1; apply Fin.ext; dsimp only; rw [hsub]
  have hreach_cycle_is_u : ∀ (d : ℕ) (w : Fin d → Bool) (j : Fin l),
      runDef z n d w = some (a j) → ∀ i : Fin d, w i = u i.val := by
    intro d w j hdw
    apply prefix_eq_of_extend z n h1' u hu d w
    intro B
    let m := B + 1
    let b := d + m
    let W : Fin b → Bool := fun i =>
      if hi : i.val < d then w ⟨i.val, hi⟩ else c ⟨(j.val + (i.val - d)) % l, Nat.mod_lt _ hl_pos⟩
    refine ⟨b, by omega, by omega, W, ?_, fun i => by dsimp only [W]; rw [dif_pos i.isLt]⟩
    rw [runDef_eq_runFrom, list_ofFn_split (by omega : d ≤ b) W, runFrom_append]
    have hpref : List.ofFn (fun i : Fin d => W ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩) = List.ofFn w := by
      congr 1; ext i; dsimp only [W]; rw [dif_pos i.isLt]
    rw [hpref, ← runDef_eq_runFrom, hdw]
    have hwalk : ∀ k : ℕ, ∃ j' : Fin l, j'.val = (j.val + k) % l ∧
        runFrom n (some (a j)) (List.ofFn fun i : Fin k => c ⟨(j.val + i.val) % l, Nat.mod_lt _ hl_pos⟩) =
          some (a j') := by
      intro k
      induction k with
      | zero =>
        refine ⟨j, ?_, rfl⟩
        rw [add_zero, Nat.mod_eq_of_lt j.isLt]
      | succ k ih =>
        obtain ⟨jk, hjk, hrun_k⟩ := ih
        obtain ⟨j', hj', hstep_j⟩ := ha_step jk
        refine ⟨j', ?_, ?_⟩
        · rw [hj', hjk]
          calc ((j.val + k) % l + 1) % l = ((j.val + k) % l + 1 % l) % l := by
                rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
            _ = (j.val + k + 1) % l := (Nat.add_mod (j.val + k) 1 l).symm
            _ = (j.val + (k + 1)) % l := by rw [Nat.add_assoc]
        · have hlist : List.ofFn (fun i : Fin (k + 1) => c ⟨(j.val + i.val) % l, Nat.mod_lt _ hl_pos⟩) =
              List.ofFn (fun i : Fin k => c ⟨(j.val + i.val) % l, Nat.mod_lt _ hl_pos⟩) ++
                [c ⟨(j.val + k) % l, Nat.mod_lt _ hl_pos⟩] := by
            apply List.ext_getElem
            · simp
            · intro i h1_l h2_l
              simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn, List.getElem_singleton]
              split_ifs with hi
              · rfl
              · have hik : i = k := by simp only [List.length_ofFn] at h1_l; omega
                subst hik; rfl
          rw [hlist, runFrom_append, hrun_k]
          dsimp only [runFrom]
          simp only [List.foldl_cons, List.foldl_nil, Option.bind_some]
          have hjk_fin : (⟨(j.val + k) % l, Nat.mod_lt _ hl_pos⟩ : Fin l) = jk := Fin.ext hjk.symm
          rw [hjk_fin, hstep_j]
    have hsuf : List.ofFn (fun i : Fin (b - d) => W ⟨d + i.val, by omega⟩) =
        List.ofFn (fun i : Fin (b - d) => c ⟨(j.val + i.val) % l, Nat.mod_lt _ hl_pos⟩) := by
      congr 1; ext i; dsimp only [W]
      have hnot : ¬ d + i.val < d := by omega
      rw [dif_neg hnot]
      congr 1; apply Fin.ext; dsimp only; rw [Nat.add_sub_cancel_left]
    rw [hsuf]
    obtain ⟨j', _, hrun_j'⟩ := hwalk (b - d)
    rw [hrun_j']; rfl
  have hlive_bound : ∀ b : ℕ, live b ≤ 2 ^ (s - l) := by
    intro b
    by_cases hble : b ≤ s - l
    · calc live b ≤ (Finset.univ : Finset (Fin b → Bool)).card := Finset.card_filter_le _ _
        _ = 2 ^ b := by simp
        _ ≤ 2 ^ (s - l) := Nat.pow_le_pow_right (by omega) hble
    · let k := b - (s - l)
      have hkb : k + (s - l) = b := by omega
      have hall_agree : ∀ w : Fin b → Bool, (runDef z n b w).isSome = true →
          ∀ t : Fin k, w ⟨t.val, by omega⟩ = u t.val := by
        intro w hw
        by_contra hnot
        have hex_diff : ∃ t : ℕ, ∃ (ht : t < k), w ⟨t, by omega⟩ ≠ u t := by
          by_contra hnone
          apply hnot
          intro t
          by_contra hne
          exact hnone ⟨t.val, t.isLt, hne⟩
        let t0 := Nat.find hex_diff
        have ht0_spec := Nat.find_spec hex_diff
        have ht0_lt : t0 < k := ht0_spec.1
        have ht0_ne : w ⟨t0, by omega⟩ ≠ u t0 := ht0_spec.2
        let m := b - t0
        have hm_ge : s - l + 1 ≤ m := by omega
        have hpref_live : ∀ r : Fin m, (runDef z n (t0 + 1 + r.val)
            (fun i : Fin (t0 + 1 + r.val) => w ⟨i.val, by have := r.isLt; omega⟩)).isSome = true :=
          fun r => runDef_prefix_isSome z n (by have := r.isLt; omega : t0 + 1 + r.val ≤ b) w hw
        let y : Fin m → Fin s := fun r => Option.get _ (hpref_live r)
        have hy_run : ∀ r : Fin m, runDef z n (t0 + 1 + r.val)
            (fun i : Fin (t0 + 1 + r.val) => w ⟨i.val, by omega⟩) = some (y r) :=
          fun r => (Option.some_get (hpref_live r)).symm
        have hy_not_C : ∀ r : Fin m, ∀ j : Fin l, y r ≠ a j := by
          intro r j heq
          have hr := hy_run r
          rw [heq] at hr
          have hagr := hreach_cycle_is_u (t0 + 1 + r.val)
            (fun i : Fin (t0 + 1 + r.val) => w ⟨i.val, by omega⟩) j hr ⟨t0, by omega⟩
          exact ht0_ne hagr
        have hy_inj : Function.Injective y := by
          intro r1 r2 h12
          by_contra hne
          have hne_val : r1.val ≠ r2.val := fun h => hne (Fin.ext h)
          have hcyc_contra : ∀ (a1 a2 : Fin m), a1.val < a2.val → y a1 = y a2 → False := by
            intro a1 a2 hlt heq
            let d1 := t0 + 1 + a1.val
            let d2 := t0 + 1 + a2.val
            let Lcyc : List Bool := List.ofFn (fun i : Fin (a2.val - a1.val) => w ⟨d1 + i.val, by omega⟩)
            have hLcyc_pos : 0 < Lcyc.length := by simp [Lcyc]; omega
            have hLcyc_run : runFrom n (some (y a1)) Lcyc = some (y a1) := by
              have h2 := hy_run a2
              rw [runDef_eq_runFrom, list_ofFn_split (by omega : d1 ≤ d2), runFrom_append] at h2
              have hp1 : List.ofFn (fun i : Fin d1 => w ⟨i.val, by omega⟩) =
                  List.ofFn (fun i : Fin d1 => w ⟨i.val, by omega⟩) := rfl
              rw [← runDef_eq_runFrom, hy_run a1] at h2
              have hsuf : List.ofFn (fun i : Fin (d2 - d1) => w ⟨d1 + i.val, by omega⟩) = Lcyc := by
                apply List.ext_getElem
                · simp [Lcyc]; omega
                · intro i h1_l h2_l; simp [Lcyc]
              rw [hsuf, ← heq] at h2
              exact h2
            have hext_w : ∀ B : ℕ, ∃ (b' : ℕ) (hb' : d1 ≤ b') (hbB : B ≤ b') (W : Fin b' → Bool),
                (runDef z n b' W).isSome = true ∧
                ∀ i : Fin d1, W ⟨i.val, lt_of_lt_of_le i.isLt hb'⟩ = w ⟨i.val, by omega⟩ := by
              intro B
              let Lrep := List.ofFn (fun i : Fin d1 => w ⟨i.val, by omega⟩) ++
                List.flatten (List.replicate (B + 1) Lcyc)
              have hlen : d1 ≤ Lrep.length := by simp [Lrep]
              have hlenB : B ≤ Lrep.length := by
                have hflat : (List.flatten (List.replicate (B + 1) Lcyc)).length = (B + 1) * Lcyc.length := by
                  simp
                have : Lrep.length = d1 + (B + 1) * Lcyc.length := by simp [Lrep, hflat]
                have : B + 1 ≤ (B + 1) * Lcyc.length := Nat.le_mul_of_pos_right _ hLcyc_pos
                omega
              let W : Fin Lrep.length → Bool := fun i => Lrep[i.val]
              refine ⟨Lrep.length, hlen, hlenB, W, ?_, ?_⟩
              · rw [runDef_eq_runFrom, list_ofFn_get Lrep rfl, runFrom_append, ← runDef_eq_runFrom,
                  hy_run a1, runFrom_repeat n (y a1) Lcyc hLcyc_run (B + 1)]
                rfl
              · intro i
                dsimp only [W, Lrep]
                rw [List.getElem_append_left (by simp)]
                simp
            have hagr := prefix_eq_of_extend z n h1' u hu d1 (fun i : Fin d1 => w ⟨i.val, by omega⟩)
              hext_w ⟨t0, by omega⟩
            exact ht0_ne hagr
          rcases Nat.lt_or_gt_of_ne hne_val with hlt | hgt
          · exact hcyc_contra r1 r2 hlt h12
          · exact hcyc_contra r2 r1 hgt h12.symm
        let Yset : Finset (Fin s) := Finset.univ.image y
        let Cset : Finset (Fin s) := Finset.univ.image a
        have hdisj : Disjoint Yset Cset := by
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          rw [Finset.mem_image] at hx1 hx2
          obtain ⟨r, _, rfl⟩ := hx1
          obtain ⟨j, _, heq⟩ := hx2
          exact hy_not_C r j heq.symm
        have hcard_le : (Yset ∪ Cset).card ≤ Fintype.card (Fin s) := Finset.card_le_univ _
        rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hy_inj,
          Finset.card_image_of_injective _ a.injective, Finset.card_univ, Finset.card_univ,
          Fintype.card_fin, Fintype.card_fin, Fintype.card_fin] at hcard_le
        omega
      let S := (Finset.univ : Finset (Fin b → Bool)).filter (fun w => (runDef z n b w).isSome)
      have hinj : Set.InjOn (fun (w : Fin b → Bool) (i : Fin (s - l)) => w ⟨k + i.val, by omega⟩) (S : Set (Fin b → Bool)) := by
        intro w1 hw1 w2 hw2 h12
        rw [Finset.mem_coe, Finset.mem_filter] at hw1 hw2
        ext idx
        by_cases hlt : idx.val < k
        · have h1_w := hall_agree w1 hw1.2 ⟨idx.val, hlt⟩
          have h2_w := hall_agree w2 hw2.2 ⟨idx.val, hlt⟩
          exact h1_w.trans h2_w.symm
        · have h12_i := congrFun h12 ⟨idx.val - k, by have := idx.isLt; omega⟩
          dsimp only at h12_i
          have hfin : (⟨k + (idx.val - k), by have := idx.isLt; omega⟩ : Fin b) = idx :=
            Fin.ext (by dsimp only; omega)
          rw [hfin] at h12_i
          exact h12_i
      calc live b = (S.image (fun (w : Fin b → Bool) (i : Fin (s - l)) => w ⟨k + i.val, by omega⟩)).card :=
            (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.univ : Finset (Fin (s - l) → Bool)).card := Finset.card_le_univ _
        _ = 2 ^ (s - l) := by simp
  refine ⟨l, hl_pos, hl_le, ⟨a, c, ha_reach, ha_step⟩, hlive_bound, ?_⟩
  intro g v hv
  let Rset : Finset (Fin s) := Finset.univ.filter (fun x : Fin s => ∃ (b : ℕ) (w : Fin b → Bool), runDef z n b w = some x)
  have hz_mem : z ∈ Rset := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ z, 0, Fin.elim0, rfl⟩
  have hC_sub : Finset.univ.image a ⊆ Rset := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨j, _, rfl⟩ := hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, p + j.val, fun i : Fin (p + j.val) => u i.val, ?_⟩
    rw [hst_run (p + j.val), hst_periodic j.val]
    congr 2
    exact Fin.ext (Nat.mod_eq_of_lt j.isLt)
  have hR_closed : ∀ x ∈ Rset, ∀ (bit : Bool) (y : Fin s), n x bit = some y → y ∈ Rset := by
    intro x hx bit y hxy
    rw [Finset.mem_filter] at hx ⊢
    obtain ⟨_, b, w, hbw⟩ := hx
    let w' : Fin (b + 1) → Bool := fun i => if hi : i.val < b then w ⟨i.val, hi⟩ else bit
    refine ⟨Finset.mem_univ y, b + 1, w', ?_⟩
    rw [runDef_succ]
    have hpref : (fun i : Fin b => w' i.castSucc) = w := by
      ext i; dsimp only [w', Fin.castSucc, Fin.castAdd, Fin.castLE]; rw [dif_pos i.isLt]
    have hlast : w' (Fin.last b) = bit := by
      dsimp only [w', Fin.last]; rw [dif_neg (by omega)]
    rw [hpref, hlast, hbw]
    exact hxy
  let R := {x : Fin s // x ∈ Rset}
  let M : Matrix R R ℤ := fun i k =>
    (if i = k then (2 : ℤ) else 0) -
      ∑ bit : Bool, if n i.1 bit = some k.1 then (1 : ℤ) else 0
  let rhs : R → ℤ := fun i =>
    ∑ bit : Bool, if (n i.1 bit).isNone then g i.1 bit else 0
  have hM_mulVec : (M.map (Int.castRingHom ℝ)).mulVec (fun k : R => v k.1) =
      fun i : R => (rhs i : ℝ) := by
    ext i
    simp only [Matrix.mulVec, dotProduct]
    have hterm : ∀ k : R, (M.map (Int.castRingHom ℝ)) i k * v k.1 =
        ((if i = k then (2 : ℤ) else 0 : ℤ) : ℝ) * v k.1 -
        (∑ bit : Bool, ((if n i.1 bit = some k.1 then (1 : ℤ) else 0 : ℤ) : ℝ)) * v k.1 := by
      intro k
      change (((if i = k then (2 : ℤ) else 0) -
        ∑ bit : Bool, if n i.1 bit = some k.1 then (1 : ℤ) else 0 : ℤ) : ℝ) * v k.1 = _
      rw [Int.cast_sub, Int.cast_sum, sub_mul]
    have h1_i : ∑ k : R, ((if i = k then (2 : ℤ) else 0 : ℤ) : ℝ) * v k.1 = 2 * v i.1 := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hki; simp [Ne.symm hki]
      · intro h; exact absurd (Finset.mem_univ i) h
    have h2_i : ∑ k : R, (∑ bit : Bool, ((if n i.1 bit = some k.1 then (1 : ℤ) else 0 : ℤ) : ℝ)) * v k.1 =
        ∑ bit : Bool, match n i.1 bit with | none => 0 | some y => v y := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro bit _
      cases hnb : n i.1 bit with
      | none => simp
      | some y =>
        have hyR : y ∈ Rset := hR_closed i.1 i.2 bit y hnb
        rw [Finset.sum_eq_single ⟨y, hyR⟩]
        · simp
        · intro k _ hky
          have hne : y ≠ k.1 := fun h => hky (Subtype.ext h.symm)
          simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, h1_i, h2_i]
    have hvi := hv i.1
    have hrhs_eq : (∑ bit : Bool, (n i.1 bit).elim (g i.1 bit : ℝ) v) =
        (∑ bit : Bool, match n i.1 bit with | none => 0 | some y => v y) +
        (rhs i : ℝ) := by
      dsimp only [rhs]
      rw [Int.cast_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro bit _
      cases hnb : n i.1 bit with
      | none => simp only [Option.elim, Option.isNone_none, ↓reduceIte, zero_add]
      | some y => simp only [Option.elim, Option.isNone_some, Bool.false_eq_true, ↓reduceIte, Int.cast_zero, add_zero]
    linarith
  let Mpol : (R → Bool) → Matrix R R ℤ := fun π i k =>
    (if i = k then (1 : ℤ) else 0) - (if n i.1 (π i) = some k.1 then 1 else 0)
  have hM_det_sum : M.det = ∑ π : R → Bool, (Mpol π).det := by
    have hM_entry : ∀ i k : R, M i k = ∑ bit : Bool,
        ((if i = k then (1 : ℤ) else 0) - (if n i.1 bit = some k.1 then 1 else 0)) := by
      intro i k
      dsimp only [M]
      rw [Finset.sum_sub_distrib]
      congr 1
      rw [Fintype.sum_bool]
      split_ifs <;> ring
    rw [← Matrix.det_transpose, Matrix.det_apply]
    simp only [Matrix.transpose_apply]
    simp_rw [hM_entry, Fintype.prod_sum, Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro π _
    rw [← Matrix.det_transpose, Matrix.det_apply]
    rfl
  have hpol_cycle : ∀ (π : R → Bool) (x0 : R) (k : ℕ), 0 < k →
      (∃ path : Fin (k + 1) → R, path 0 = x0 ∧ path (Fin.last k) = x0 ∧
        ∀ t : Fin k, n (path t.castSucc).1 (π (path t.castSucc)) = some (path t.succ).1) →
      ∀ j : Fin l, π ⟨a j, hC_sub (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)⟩ = c j := by
    intro π x0 k hk ⟨path, hp0, hpk, hstep⟩
    obtain ⟨_, d, w, hdw⟩ := Finset.mem_filter.mp x0.2
    let Lcyc : List Bool := List.ofFn (fun t : Fin k => π (path t.castSucc))
    have hLcyc_len : Lcyc.length = k := by simp [Lcyc]
    have hLcyc_run : runFrom n (some x0.1) Lcyc = some x0.1 := by
      have hwalk : ∀ m : ℕ, (hm : m ≤ k) →
          runFrom n (some x0.1) (List.ofFn fun t : Fin m => π (path ⟨t.val, by omega⟩)) =
            some (path ⟨m, by omega⟩).1 := by
        intro m
        induction m with
        | zero => intro _; rw [← hp0]; rfl
        | succ m ih =>
          intro hm
          have hlist : List.ofFn (fun t : Fin (m + 1) => π (path ⟨t.val, by omega⟩)) =
              List.ofFn (fun t : Fin m => π (path ⟨t.val, by omega⟩)) ++ [π (path ⟨m, by omega⟩)] := by
            apply List.ext_getElem
            · simp
            · intro i h1_l h2_l
              simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn, List.getElem_singleton]
              split_ifs with hi
              · rfl
              · have him : i = m := by simp only [List.length_ofFn] at h1_l; omega
                subst him; rfl
          rw [hlist, runFrom_append, ih (by omega)]
          dsimp only [runFrom]
          simp only [List.foldl_cons, List.foldl_nil, Option.bind_some]
          exact hstep ⟨m, by omega⟩
      have hwk := hwalk k (le_refl k)
      have hfin : (⟨k, by omega⟩ : Fin (k + 1)) = Fin.last k := rfl
      rw [hfin, hpk] at hwk
      exact hwk
    have hwalk_state : ∀ m : ℕ,
        runFrom n (some z) (List.ofFn w ++ List.ofFn (fun t : Fin m => Lcyc[t.val % k]'(by rw [hLcyc_len]; exact Nat.mod_lt _ hk))) =
          some (path ⟨m % k, Nat.lt_succ_of_lt (Nat.mod_lt _ hk)⟩).1 := by
      intro m
      induction m with
      | zero =>
        simp only [List.ofFn_zero, List.append_nil, Nat.zero_mod]
        rw [← runDef_eq_runFrom, hdw, ← hp0]
        rfl
      | succ m ih =>
        have hlist : List.ofFn (fun t : Fin (m + 1) => Lcyc[t.val % k]'(by rw [hLcyc_len]; exact Nat.mod_lt _ hk)) =
            List.ofFn (fun t : Fin m => Lcyc[t.val % k]'(by rw [hLcyc_len]; exact Nat.mod_lt _ hk)) ++ [Lcyc[m % k]'(by rw [hLcyc_len]; exact Nat.mod_lt _ hk)] := by
          apply List.ext_getElem
          · simp
          · intro i h1_l h2_l
            simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn, List.getElem_singleton]
            split_ifs with hi
            · rfl
            · have him : i = m := by simp only [List.length_ofFn] at h1_l; omega
              subst him; rfl
        rw [hlist, ← List.append_assoc, runFrom_append, ih]
        dsimp only [runFrom]
        simp only [List.foldl_cons, List.foldl_nil, Option.bind_some]
        have hLget : Lcyc[m % k]'(by rw [hLcyc_len]; exact Nat.mod_lt _ hk) = π (path ⟨m % k, Nat.lt_succ_of_lt (Nat.mod_lt _ hk)⟩) := by
          simp [Lcyc]
        rw [hLget]
        have hst_m := hstep ⟨m % k, Nat.mod_lt _ hk⟩
        dsimp only [Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ] at hst_m
        rw [hst_m]
        congr 2
        by_cases hlt : m % k + 1 < k
        · have hmod : (m + 1) % k = m % k + 1 := by
            have hk2 : 1 < k := by omega
            calc (m + 1) % k = (m % k + 1 % k) % k := Nat.add_mod m 1 k
              _ = (m % k + 1) % k := by rw [Nat.mod_eq_of_lt hk2]
              _ = m % k + 1 := Nat.mod_eq_of_lt hlt
          congr 1
          exact Fin.ext hmod.symm
        · have hlast : m % k + 1 = k := by
            have := Nat.mod_lt m hk; omega
          have hmod : (m + 1) % k = 0 := by
            have hdvd : k ∣ m + 1 := by
              refine ⟨m / k + 1, ?_⟩
              calc m + 1 = k * (m / k) + m % k + 1 := by rw [Nat.div_add_mod]
                _ = k * (m / k) + k := by omega
                _ = k * (m / k + 1) := by ring
            exact Nat.mod_eq_zero_of_dvd hdvd
          have hfin1 : (⟨m % k + 1, by have := Nat.mod_lt m hk; omega⟩ : Fin (k + 1)) = Fin.last k := Fin.ext hlast
          have hfin0 : (⟨(m + 1) % k, Nat.lt_succ_of_lt (Nat.mod_lt _ hk)⟩ : Fin (k + 1)) = 0 := Fin.ext hmod
          rw [hfin1, hfin0, hpk, hp0]
    have hext_path : ∀ m : ℕ, ∀ B : ℕ, ∃ (b' : ℕ) (hb' : d + m ≤ b') (hbB : B ≤ b') (W : Fin b' → Bool),
        (runDef z n b' W).isSome = true ∧
        ∀ i : Fin (d + m), W ⟨i.val, lt_of_lt_of_le i.isLt hb'⟩ =
          if hi : i.val < d then w ⟨i.val, hi⟩ else Lcyc[(i.val - d) % k]'(by rw [hLcyc_len]; exact Nat.mod_lt _ hk) := by
      intro m B
      let m' := max m B
      let b' := d + m'
      let W : Fin b' → Bool := fun i =>
        if hi : i.val < d then w ⟨i.val, hi⟩ else Lcyc[(i.val - d) % k]'(by rw [hLcyc_len]; exact Nat.mod_lt _ hk)
      refine ⟨b', by omega, by omega, W, ?_, fun i => rfl⟩
      rw [runDef_eq_runFrom, list_ofFn_split (by omega : d ≤ b') W]
      have hp1 : List.ofFn (fun i : Fin d => W ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩) = List.ofFn w := by
        congr 1; ext i; dsimp only [W]; rw [dif_pos i.isLt]
      have hp2 : List.ofFn (fun i : Fin (b' - d) => W ⟨d + i.val, by omega⟩) =
          List.ofFn (fun t : Fin m' => Lcyc[t.val % k]'(by rw [hLcyc_len]; exact Nat.mod_lt _ hk)) := by
        apply List.ext_getElem
        · simp [b']
        · intro i h1_l h2_l
          simp only [List.getElem_ofFn, W]
          have hnot : ¬ d + i < d := by omega
          rw [dif_neg hnot]
          congr 1; rw [Nat.add_sub_cancel_left]
      rw [hp1, hp2, hwalk_state m']
      rfl
    intro j
    let t := (d + 1) * l + j.val
    let m := p + t - d
    have hdl : d + 1 ≤ (d + 1) * l := Nat.le_mul_of_pos_right _ hl_pos
    have hdm : d + m = p + t := by omega
    have hpref := prefix_eq_of_extend z n h1' u hu (d + (m + 1))
      (fun i : Fin (d + (m + 1)) =>
        if hi : i.val < d then w ⟨i.val, hi⟩ else Lcyc[(i.val - d) % k]'(by rw [hLcyc_len]; exact Nat.mod_lt _ hk))
      (hext_path (m + 1))
    have hbit_u : u (p + t) = π (path ⟨m % k, Nat.lt_succ_of_lt (Nat.mod_lt _ hk)⟩) := by
      have hpt := hpref ⟨d + m, by omega⟩
      dsimp only at hpt
      have hnot : ¬ d + m < d := by omega
      rw [dif_neg hnot] at hpt
      have hsub : d + m - d = m := by omega
      rw [← hdm, ← hpt]
      have hLget : Lcyc[(d + m - d) % k]'(by rw [hLcyc_len]; exact Nat.mod_lt _ hk) =
          π (path ⟨m % k, Nat.lt_succ_of_lt (Nat.mod_lt _ hk)⟩) := by
        simp [Lcyc, hsub]
      exact hLget
    have hst_eq : st (p + t) = (path ⟨m % k, Nat.lt_succ_of_lt (Nat.mod_lt _ hk)⟩).1 := by
      have hrun_m : runDef z n (d + m) (fun i : Fin (d + m) => u i.val) =
          some (path ⟨m % k, Nat.lt_succ_of_lt (Nat.mod_lt _ hk)⟩).1 := by
        have hfun : (fun i : Fin (d + m) => u i.val) =
            (fun i : Fin (d + m) => if hi : i.val < d then w ⟨i.val, hi⟩
              else Lcyc[(i.val - d) % k]'(by rw [hLcyc_len]; exact Nat.mod_lt _ hk)) := by
          ext i
          exact (hpref ⟨i.val, by omega⟩).symm
        rw [hfun, runDef_eq_runFrom, list_ofFn_split (by omega : d ≤ d + m)]
        have hp1 : List.ofFn (fun i : Fin d =>
            if hi : (⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩ : Fin (d + m)).val < d then w ⟨i.val, hi⟩
            else Lcyc[(i.val - d) % k]'(by rw [hLcyc_len]; exact Nat.mod_lt _ hk)) = List.ofFn w := by
          congr 1; ext i; dsimp only; rw [dif_pos i.isLt]
        have hp2 : List.ofFn (fun i : Fin (d + m - d) =>
            if hi : (⟨d + i.val, by omega⟩ : Fin (d + m)).val < d then w ⟨d + i.val, hi⟩
            else Lcyc[(d + i.val - d) % k]'(by rw [hLcyc_len]; exact Nat.mod_lt _ hk)) =
            List.ofFn (fun t : Fin m => Lcyc[t.val % k]'(by rw [hLcyc_len]; exact Nat.mod_lt _ hk)) := by
          apply List.ext_getElem
          · simp
          · intro i h1_l h2_l
            simp only [List.getElem_ofFn]
            have hnot : ¬ d + i < d := by omega
            rw [dif_neg hnot]
            congr 1; rw [Nat.add_sub_cancel_left]
        rw [hp1, hp2, hwalk_state m]
      rw [hdm, hst_run (p + t)] at hrun_m
      exact Option.some.inj hrun_m
    have ht_mod : t % l = j.val := by
      dsimp only [t]
      rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt j.isLt]
    have hpath_eq : path ⟨m % k, Nat.lt_succ_of_lt (Nat.mod_lt _ hk)⟩ =
        ⟨a j, hC_sub (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)⟩ := by
      apply Subtype.ext
      rw [← hst_eq, hst_periodic t]
      congr 1
      exact Fin.ext ht_mod
    have hcj : c j = u (p + t) := by
      rw [hu_periodic t]
      congr 1
      exact Fin.ext ht_mod.symm
    rw [← hpath_eq, ← hbit_u, hcj]
  have hpol_det : ∀ π : R → Bool, (Mpol π).det =
      if ∀ j : Fin l, π ⟨a j, hC_sub (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)⟩ = c j
      then 0 else 1 := by
    intro π
    by_cases hcyc : ∀ j : Fin l, π ⟨a j, hC_sub (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)⟩ = c j
    · rw [if_pos hcyc]
      let w : R → ℤ := fun x => if x.1 ∈ Finset.univ.image a then 1 else 0
      apply det_eq_zero_of_row_dep (Mpol π) w
      · intro hw0
        have hx := congrFun hw0 ⟨a ⟨0, hl_pos⟩, hC_sub (Finset.mem_image.mpr ⟨⟨0, hl_pos⟩, Finset.mem_univ _, rfl⟩)⟩
        have hmem : a ⟨0, hl_pos⟩ ∈ Finset.univ.image a := Finset.mem_image.mpr ⟨⟨0, hl_pos⟩, Finset.mem_univ _, rfl⟩
        simp [w, hmem] at hx
      · intro k
        have hsum_C : ∑ i : R, w i * Mpol π i k =
            ∑ j : Fin l, Mpol π ⟨a j, hC_sub (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)⟩ k := by
          have hfilt : ∑ i : R, w i * Mpol π i k =
              ∑ i ∈ Finset.univ.filter (fun i : R => i.1 ∈ Finset.univ.image a), Mpol π i k := by
            rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : R => i.1 ∈ Finset.univ.image a)]
            have h1_s : ∑ i ∈ Finset.univ.filter (fun i : R => i.1 ∈ Finset.univ.image a), w i * Mpol π i k =
                ∑ i ∈ Finset.univ.filter (fun i : R => i.1 ∈ Finset.univ.image a), Mpol π i k := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.mem_filter] at hi
              dsimp only [w]
              rw [if_pos hi.2, one_mul]
            have h2_s : ∑ i ∈ Finset.univ.filter (fun i : R => ¬ i.1 ∈ Finset.univ.image a), w i * Mpol π i k = 0 := by
              apply Finset.sum_eq_zero
              intro i hi
              rw [Finset.mem_filter] at hi
              dsimp only [w]
              rw [if_neg hi.2, zero_mul]
            rw [h1_s, h2_s, add_zero]
          rw [hfilt]
          symm
          refine Finset.sum_bij (fun j _ => ⟨a j, hC_sub (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)⟩)
            ?_ ?_ ?_ (fun _ _ => rfl)
          · intro j _
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩
          · intro j1 _ j2 _ h12
            exact a.injective (congrArg Subtype.val h12)
          · intro i hi
            rw [Finset.mem_filter, Finset.mem_image] at hi
            obtain ⟨j, _, hj⟩ := hi.2
            exact ⟨j, Finset.mem_univ j, Subtype.ext hj⟩
        rw [hsum_C]
        dsimp only [Mpol]
        rw [Finset.sum_sub_distrib, sub_eq_zero]
        let rot : Fin l ≃ Fin l :=
          { toFun := fun j => ⟨(j.val + 1) % l, Nat.mod_lt _ hl_pos⟩
            invFun := fun j => ⟨(j.val + l - 1) % l, Nat.mod_lt _ hl_pos⟩
            left_inv := fun j => by
              apply Fin.ext; dsimp only
              by_cases hlt : j.val + 1 < l
              · rw [Nat.mod_eq_of_lt hlt]
                have h1_v : j.val + 1 + l - 1 = j.val + l := by omega
                rw [h1_v, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
              · have hlast : j.val + 1 = l := by omega
                rw [hlast, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (by omega)]
                omega
            right_inv := fun j => by
              apply Fin.ext; dsimp only
              by_cases h0 : j.val = 0
              · have h1_v : (0 + l - 1) % l = l - 1 := by
                  rw [zero_add, Nat.mod_eq_of_lt (by omega)]
                rw [h0, h1_v, show l - 1 + 1 = l by omega, Nat.mod_self]
              · have hjlt := j.isLt
                have h1_v : (j.val + l - 1) % l = j.val - 1 := by
                  rw [show j.val + l - 1 = (j.val - 1) + l by omega, Nat.add_mod_right,
                    Nat.mod_eq_of_lt (by omega)]
                rw [h1_v, show j.val - 1 + 1 = j.val by omega, Nat.mod_eq_of_lt hjlt] }
        rw [← Equiv.sum_comp rot]
        apply Finset.sum_congr rfl
        intro j _
        obtain ⟨j', hj', hstep_j⟩ := ha_step j
        have hrot_eq : rot j = j' := Fin.ext hj'.symm
        rw [hrot_eq, hcyc j, hstep_j]
        have hiff : (⟨a j', hC_sub (Finset.mem_image.mpr ⟨j', Finset.mem_univ j', rfl⟩)⟩ : R) = k ↔
            some (a j') = some k.1 := by
          constructor
          · intro h; rw [← h]
          · intro h; exact Subtype.ext (Option.some.inj h)
        by_cases h : (⟨a j', hC_sub (Finset.mem_image.mpr ⟨j', Finset.mem_univ j', rfl⟩)⟩ : R) = k
        · rw [if_pos h, if_pos (hiff.mp h)]
        · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]
    · rw [if_neg hcyc, ← Matrix.det_transpose, Matrix.det_apply]
      rw [Finset.sum_eq_single (1 : Equiv.Perm R)]
      · simp only [Equiv.Perm.sign_one, one_smul, Equiv.Perm.coe_one, id_eq, Matrix.transpose_apply]
        apply Finset.prod_eq_one
        intro i _
        dsimp only [Mpol]
        rw [if_pos rfl]
        have hno_self : n i.1 (π i) ≠ some i.1 := by
          intro hself
          apply hcyc
          exact hpol_cycle π i 1 (by omega) ⟨fun _ => i, rfl, rfl, fun _ => hself⟩
        rw [if_neg hno_self, sub_zero]
      · intro σ _ hσ1
        have hex_mv : ∃ x0 : R, σ x0 ≠ x0 := by
          by_contra hall
          apply hσ1
          apply Equiv.ext
          intro x
          simp only [Equiv.Perm.coe_one, id_eq]
          by_contra hne
          exact hall ⟨x, hne⟩
        obtain ⟨x0, hx0⟩ := hex_mv
        have hprod0 : ∏ i : R, (Mpol π).transpose (σ i) i = 0 := by
          by_contra hne0
          have hall_ne : ∀ i : R, Mpol π i (σ i) ≠ 0 := by
            intro i hi
            apply hne0
            exact Finset.prod_eq_zero (Finset.mem_univ i) hi
          have horb_ne : ∀ t : ℕ, σ ((σ ^ t) x0) ≠ (σ ^ t) x0 := by
            intro t heq
            have h1_o : (σ ^ t) (σ x0) = (σ ^ t) x0 := by
              have hcomm : σ ((σ ^ t) x0) = (σ ^ t) (σ x0) := by
                change (σ * σ ^ t) x0 = (σ ^ t * σ) x0
                rw [pow_mul_comm']
              rw [← hcomm, heq]
            exact hx0 ((σ ^ t).injective h1_o)
          have horb_step : ∀ t : ℕ, n ((σ ^ t) x0).1 (π ((σ ^ t) x0)) = some ((σ ^ (t + 1)) x0).1 := by
            intro t
            have hne := hall_ne ((σ ^ t) x0)
            dsimp only [Mpol] at hne
            have hne_i : (σ ^ t) x0 ≠ σ ((σ ^ t) x0) := (horb_ne t).symm
            rw [if_neg hne_i, zero_sub, neg_ne_zero] at hne
            have hsome : n ((σ ^ t) x0).1 (π ((σ ^ t) x0)) = some (σ ((σ ^ t) x0)).1 := by
              by_contra hnot
              rw [if_neg hnot] at hne
              exact hne rfl
            have hpow : σ ((σ ^ t) x0) = (σ ^ (t + 1)) x0 := by
              rw [pow_succ']
              rfl
            rw [← hpow]
            exact hsome
          let k := orderOf σ
          have hk_pos : 0 < k := orderOf_pos σ
          have hpow_k : (σ ^ k) x0 = x0 := by
            rw [pow_orderOf_eq_one]
            rfl
          apply hcyc
          exact hpol_cycle π x0 k hk_pos ⟨fun t : Fin (k + 1) => (σ ^ t.val) x0, rfl, hpow_k, fun t => horb_step t.val⟩
        rw [hprod0, smul_zero]
      · intro h; exact absurd (Finset.mem_univ 1) h
  have hM_det_val : M.det = ((2 ^ (Rset.card - l) * (2 ^ l - 1) : ℕ) : ℤ) := by
    rw [hM_det_sum]
    simp_rw [hpol_det]
    have hC_card : (Finset.univ.image a).card = l := by
      rw [Finset.card_image_of_injective _ a.injective, Finset.card_univ, Fintype.card_fin]
    have hl_le_R : l ≤ Rset.card := by
      rw [← hC_card]
      exact Finset.card_le_card hC_sub
    have hbad_card : ((Finset.univ : Finset (R → Bool)).filter (fun π =>
        ∀ j : Fin l, π ⟨a j, hC_sub (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)⟩ = c j)).card =
        2 ^ (Rset.card - l) := by
      let Rrest : Finset R := Finset.univ.filter (fun x : R => x.1 ∉ Finset.univ.image a)
      have hRrest_card : Rrest.card = Rset.card - l := by
        have hcomp : (Finset.univ.filter (fun x : R => x.1 ∈ Finset.univ.image a)).card = l := by
          trans (Finset.univ.image a).card
          · refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
            · intro x hx; exact (Finset.mem_filter.mp hx).2
            · intro x1 _ x2 _ h12; exact Subtype.ext h12
            · intro y hy
              exact ⟨⟨y, hC_sub hy⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩, rfl⟩
          · exact hC_card
        have hsum_c := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset R))
          (p := fun x : R => x.1 ∈ Finset.univ.image a)
        rw [hcomp, Finset.card_univ, Fintype.card_coe] at hsum_c
        change l + Rrest.card = Rset.card at hsum_c
        omega
      have hcard_fun : Fintype.card ({x : R // x ∈ Rrest} → Bool) = 2 ^ (Rset.card - l) := by
        rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, hRrest_card]
      rw [← hcard_fun, ← Finset.card_univ]
      refine Finset.card_bij (fun π _ => fun x : {x : R // x ∈ Rrest} => π x.1) ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro π1 hπ1 π2 hπ2 h12
        rw [Finset.mem_filter] at hπ1 hπ2
        ext x
        by_cases hxC : x.1 ∈ Finset.univ.image a
        · rw [Finset.mem_image] at hxC
          obtain ⟨j, _, hj⟩ := hxC
          have hx_eq : x = ⟨a j, hC_sub (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)⟩ := Subtype.ext hj.symm
          rw [hx_eq, hπ1.2 j, hπ2.2 j]
        · have hxR : x ∈ Rrest := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxC⟩
          exact congrFun h12 ⟨x, hxR⟩
      · intro f _
        let π : R → Bool := fun x =>
          if hxC : x.1 ∈ Finset.univ.image a then
            c (Classical.choose (Finset.mem_image.mp hxC))
          else
            f ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxC⟩⟩
        refine ⟨π, Finset.mem_filter.mpr ⟨Finset.mem_univ π, ?_⟩, ?_⟩
        · intro j
          have hxC : a j ∈ Finset.univ.image a := Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
          dsimp only [π]
          rw [dif_pos hxC]
          have hch : Classical.choose (Finset.mem_image.mp hxC) = j :=
            a.injective (Classical.choose_spec (Finset.mem_image.mp hxC)).2
          rw [hch]
        · ext ⟨x, hx⟩
          have hnotC : x.1 ∉ Finset.univ.image a := (Finset.mem_filter.mp hx).2
          dsimp only [π]
          rw [dif_neg hnotC]
    have hsum_count : (∑ π : R → Bool, if (∀ j : Fin l, π ⟨a j, hC_sub (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)⟩ = c j) then (0 : ℤ) else 1) =
        (((Finset.univ : Finset (R → Bool)).card -
          ((Finset.univ : Finset (R → Bool)).filter (fun π =>
            ∀ j : Fin l, π ⟨a j, hC_sub (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)⟩ = c j)).card : ℕ) : ℤ) := by
      have hcard_f : (Finset.univ.filter (fun π : R → Bool =>
          ¬ ∀ j : Fin l, π ⟨a j, hC_sub (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)⟩ = c j)).card =
          (Finset.univ : Finset (R → Bool)).card -
          ((Finset.univ : Finset (R → Bool)).filter (fun π =>
            ∀ j : Fin l, π ⟨a j, hC_sub (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)⟩ = c j)).card := by
        have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (R → Bool)))
          (p := fun π => ∀ j : Fin l, π ⟨a j, hC_sub (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)⟩ = c j)
        omega
      rw [← hcard_f, Finset.card_filter, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro π _
      split_ifs <;> simp
    rw [hsum_count, hbad_card, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
    congr 1
    have hpow : 2 ^ Rset.card = 2 ^ (Rset.card - l) * 2 ^ l := by
      rw [← pow_add, Nat.sub_add_cancel hl_le_R]
    rw [hpow, Nat.mul_sub_left_distrib, mul_one]
  have hcramer : ((M.det : ℤ) : ℝ) * v z = (((M.adjugate.mulVec rhs) ⟨z, hz_mem⟩ : ℤ) : ℝ) := by
    have hadj := congrArg (fun u => (M.adjugate.map (Int.castRingHom ℝ)).mulVec u) hM_mulVec
    have hsmul : (M.det • (1 : Matrix R R ℤ)).map (Int.castRingHom ℝ) = ((M.det : ℤ) : ℝ) • 1 := by
      ext i k
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Int.coe_castRingHom]
      by_cases h : i = k <;> simp [h]
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.adjugate_mul, hsmul, Matrix.smul_mulVec,
      Matrix.one_mulVec] at hadj
    have hz_eq := congrFun hadj ⟨z, hz_mem⟩
    simp only [Pi.smul_apply, smul_eq_mul] at hz_eq
    have hrhs_cast : ((M.adjugate.map (Int.castRingHom ℝ)).mulVec (fun i : R => (rhs i : ℝ))) ⟨z, hz_mem⟩ =
        (((M.adjugate.mulVec rhs) ⟨z, hz_mem⟩ : ℤ) : ℝ) := by
      simp [Matrix.mulVec, dotProduct]
    rw [hrhs_cast] at hz_eq
    exact hz_eq
  have hR_le_s : Rset.card ≤ s := by
    have := Finset.card_le_univ Rset
    simpa using this
  have hC_card : (Finset.univ.image a).card = l := by
    rw [Finset.card_image_of_injective _ a.injective, Finset.card_univ, Fintype.card_fin]
  have hl_le_R : l ≤ Rset.card := by
    rw [← hC_card]
    exact Finset.card_le_card hC_sub
  refine ⟨((2 ^ (s - Rset.card) : ℕ) : ℤ) * (M.adjugate.mulVec rhs) ⟨z, hz_mem⟩, ?_⟩
  have hmul : (2 ^ (s - Rset.card) : ℕ) * (2 ^ (Rset.card - l) * (2 ^ l - 1)) =
      2 ^ (s - l) * (2 ^ l - 1) := by
    rw [← mul_assoc, ← pow_add]
    have hexp : s - Rset.card + (Rset.card - l) = s - l := by omega
    rw [hexp]
  rw [← hmul, Nat.cast_mul, mul_assoc]
  have hdet_r : (((2 ^ (Rset.card - l) * (2 ^ l - 1) : ℕ) : ℤ) : ℝ) = ((M.det : ℤ) : ℝ) := by
    rw [hM_det_val]
  have h1_r : ((2 ^ (Rset.card - l) * (2 ^ l - 1) : ℕ) : ℝ) * v z =
      (((M.adjugate.mulVec rhs) ⟨z, hz_mem⟩ : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, hdet_r, hcramer]
  rw [h1_r]
  push_cast
  ring
