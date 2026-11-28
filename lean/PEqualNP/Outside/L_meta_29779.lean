import PEqualNP.Defs
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Push
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin

namespace PEqualNP.Outside.L_meta_29779.Period

theorem mod_one {p d : ℕ} (hd : 1 < d) (h : 2^p % d = 1) :
    2^p ≡ 1 [MOD d] := by
  change _ = 1 % d
  simpa [Nat.mod_eq_of_lt hd] using h

theorem singleton_width {d e g p : ℕ} (hd : 1 < d) (he : 0 < e) (hed : e < d)
    (hg : 0 < g) (hpow : 2^p % d = 1) (k : ℕ) :
    ((2^(p*k)*(g*e) % (g*d)) + g*e - 1) / (g*e) = 1 := by
  have eq : 2^(p*k) ≡ 1 [MOD d] := by simpa [pow_mul] using (mod_one hd hpow).pow k
  have er : 2^(p*k) * (g*e) ≡ g*e [MOD g*d] := by
    simpa [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using (eq.mul_right e).mul_left' g
  have less : g*e < g*d := Nat.mul_lt_mul_of_pos_left hed hg
  change _ % _ = _ % _ at er
  rw [Nat.mod_eq_of_lt less] at er
  rw [er]
  have pos : 0 < g*e := Nat.mul_pos hg he
  apply Nat.div_eq_of_lt_le (k := 1) <;> omega

theorem width_mod {d e g p : ℕ} (hd : 1 < d) (hpow : 2^p % d = 1) (b : ℕ) :
    ((2^(b%p)*(g*e) % (g*d)) + g*e - 1)/(g*e) =
    ((2^b*(g*e) % (g*d)) + g*e - 1)/(g*e) := by
  have many : 2^(p*(b/p)) ≡ 1 [MOD d] := by
    simpa [pow_mul] using (mod_one hd hpow).pow (b/p)
  have h := many.mul_left (2^(b%p))
  rw [← pow_add, Nat.mod_add_div, Nat.mul_one] at h
  have eq : 2^b*(g*e) ≡ 2^(b%p)*(g*e) [MOD g*d] := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using (h.mul_right e).mul_left' g
  change _ % _ = _ % _ at eq
  rw [eq]

theorem divides_period {d p l : ℕ} (hd : 1 < d) (hp : 0 < p) (hpow : 2^p % d = 1)
    (minimal : ∀ h, 0 < h → h < p → 2^h % d ≠ 1) (hl : 2^l ≡ 1 [MOD d]) : p ∣ l := by
  have many : 2^(p*(l / p)) ≡ 1 [MOD d] := by
    simpa [pow_mul] using (mod_one hd hpow).pow (l/p)
  have rem : 2^l ≡ 2^(l % p) [MOD d] := by
    have key := many.mul_left (2^(l%p))
    rwa [← pow_add, Nat.mod_add_div, Nat.mul_one] at key
  have eq := rem.symm.trans hl
  change _ = 1 % d at eq
  rw [Nat.mod_eq_of_lt hd] at eq
  apply Nat.dvd_of_mod_eq_zero
  by_contra h
  exact minimal _ (Nat.pos_of_ne_zero h) (Nat.mod_lt _ hp) eq

theorem denominator_period {d e g p k l : ℕ} (hd : 1 < d) (hg : 0 < g)
    (cop : d.Coprime e) (hp : 0 < p) (hpow : 2^p % d = 1)
    (minimal : ∀ h, 0 < h → h < p → 2^h % d ≠ 1) (v : ℝ)
    (mass : ((g*d : ℕ) : ℝ) * v = (g*e : ℕ))
    (integral : ∃ m : ℤ, ((2^k*(2^l-1) : ℕ) : ℝ)*v = m) : p ∣ l := by
  obtain ⟨m, hm⟩ := integral
  push_cast at mass
  have gv : (g : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hg
  have dv : (d : ℝ)*v = e := by
    apply mul_left_cancel₀ gv
    simpa [mul_assoc] using mass
  let K : ℕ := 2^k*(2^l-1)
  change (K : ℝ)*v = m at hm
  have eq : (K : ℝ) * e = d * (m : ℝ) := by rw [← dv, ← hm]; ring
  have eqz : ((K * e : ℕ) : ℤ) = (d : ℤ)*m := by exact_mod_cast eq
  have dz : (d : ℤ) ∣ ((K * e : ℕ) : ℤ) := ⟨m, eqz⟩
  have divK : d ∣ K := cop.dvd_of_dvd_mul_right (Int.natCast_dvd_natCast.mp dz)
  have hprod : 2*2^(p-1) ≡ 1 [MOD d] := by
    have pe : p-1+1=p := by omega
    simpa [← pow_succ', pe] using mod_one hd hpow
  have dcop : d.Coprime (2^k) := ((Nat.coprime_of_mul_modEq_one _ hprod).symm).pow_right k
  have dl : d ∣ 2^l - 1 := dcop.dvd_of_dvd_mul_left divK
  exact divides_period hd hp hpow minimal ((Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).mpr dl).symm

end PEqualNP.Outside.L_meta_29779.Period

namespace PEqualNP.Outside.L_meta_29779.CycleAux

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

theorem cycleCore : (∀ (s : ℕ) (z : Fin s) (n : Fin s → Bool → Option (Fin s)),
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

end PEqualNP.Outside.L_meta_29779.CycleAux

namespace PEqualNP.Outside.L_meta_29779.Tail

section

variable {s : ℕ} (n : Fin s → Bool → Option (Fin s))

def Absorbs := ∃ c : Fin s → Bool, ∀ i : Fin s,
  (fun x : Option (Fin s) => x.bind (fun j => n j (c j)))^[s] (some i) = none

def Ends (r : Fin s → Bool → ℝ) (x : Fin s → ℝ) (i : Fin s) (b : Bool) : ℝ :=
  (n i b).elim (r i b) x

def Solves (r : Fin s → Bool → ℝ) (x : Fin s → ℝ) : Prop :=
  ∀ i, 2 * x i = Ends n r x i false + Ends n r x i true

theorem minimumLaw (hn : Absorbs n) (x : Fin s → ℝ)
    (h : ∀ i, (n i false).elim 0 x + (n i true).elim 0 x ≤ 2 * x i) :
    ∀ i, 0 ≤ x i := by
  classical
  intro start
  obtain ⟨i, _, hmin⟩ := Finset.exists_min_image Finset.univ x ⟨start, Finset.mem_univ _⟩
  have hle (j) : x i ≤ x j := hmin _ (Finset.mem_univ j)
  suffices 0 ≤ x i by exact this.trans (hle start)
  by_contra! hi
  obtain ⟨c, hc⟩ := hn
  let F := fun o : Option (Fin s) => o.bind (fun j => n j (c j))
  have hb (o : Option (Fin s)) : x i ≤ o.elim 0 x := by cases o <;> simp [hi.le, hle]
  have step (o : Option (Fin s)) (ho : o.elim 0 x = x i) : (F o).elim 0 x = x i := by
    cases o with
    | none => exact ho
    | some j =>
      change x j = x i at ho
      have hj := h j
      rw [ho] at hj
      have h₀ := hb (n j false)
      have h₁ := hb (n j true)
      change (n j (c j)).elim 0 x = x i
      cases c j <;> linarith
  have rep (k : ℕ) : (F^[k] (some i)).elim 0 x = x i := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply']; exact step _ ih
  have he := rep s
  rw [show F^[s] (some i) = none from hc i] at he
  exact hi.ne (by simpa using he.symm)

def drift : (Fin s → ℝ) →ₗ[ℝ] (Fin s → ℝ) where
  toFun x i := 2 * x i - (n i false).elim 0 x - (n i true).elim 0 x
  map_add' x y := by
    ext i
    cases h₀ : n i false <;> cases h₁ : n i true <;> simp [h₀, h₁] <;> ring
  map_smul' a x := by
    ext i
    cases h₀ : n i false <;> cases h₁ : n i true <;> simp [h₀, h₁] <;> ring

theorem uniqueDrift (hn : Absorbs n) : Function.Injective (drift n) := by
  apply (LinearMap.ker_eq_bot.mp ?_)
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have hz (i) : 2 * x i = (n i false).elim 0 x + (n i true).elim 0 x := by
    have h := congrFun hx i
    change 2 * x i - _ - _ = 0 at h
    linarith
  have hp := minimumLaw n hn x (fun i => (hz i).ge)
  have hm := minimumLaw n hn (fun j => -x j) (fun i => by
    specialize hz i
    cases h₀ : n i false <;> cases h₁ : n i true <;> simp [h₀, h₁] at hz ⊢ <;> linarith)
  ext i
  exact le_antisymm (neg_nonneg.mp (hm i)) (hp i)

def boundary (r : Fin s → Bool → ℝ) (i : Fin s) : ℝ :=
  (n i false).elim (r i false) (fun _ => 0) + (n i true).elim (r i true) (fun _ => 0)

theorem solves_iff (r : Fin s → Bool → ℝ) (x : Fin s → ℝ) :
    Solves n r x ↔ drift n x = boundary n r := by
  constructor
  · intro h
    ext i
    specialize h i
    change 2 * x i - _ - _ = _
    cases h₀ : n i false <;> cases h₁ : n i true <;>
      simp [Ends, boundary, h₀, h₁] at h ⊢ <;> linarith
  · intro h i
    have hh := congrFun h i
    change 2 * x i - _ - _ = _ at hh
    cases h₀ : n i false <;> cases h₁ : n i true <;>
      simp [Ends, boundary, h₀, h₁] at hh ⊢ <;> linarith

noncomputable def mean (hn : Absorbs n) : (Fin s → Bool → ℝ) →ₗ[ℝ] (Fin s → ℝ) :=
  (LinearEquiv.ofBijective (drift n)
    ⟨uniqueDrift n hn, LinearMap.surjective_of_injective (uniqueDrift n hn)⟩).symm.toLinearMap.comp
      ({
        toFun := boundary n
        map_add' := by
          intro x y
          ext i
          cases h₀ : n i false <;> cases h₁ : n i true <;> simp [boundary, h₀, h₁] <;> ring
        map_smul' := by
          intro a x
          ext i
          cases h₀ : n i false <;> cases h₁ : n i true <;> simp [boundary, h₀, h₁] <;> ring } :
        (Fin s → Bool → ℝ) →ₗ[ℝ] (Fin s → ℝ))

theorem mean_solves (hn : Absorbs n) (r) : Solves n r (mean n hn r) := by
  rw [solves_iff]
  exact (LinearEquiv.ofBijective (drift n)
    ⟨uniqueDrift n hn, LinearMap.surjective_of_injective (uniqueDrift n hn)⟩).apply_symm_apply _

theorem eqMean (hn : Absorbs n) {r x} (h : Solves n r x) : x = mean n hn r :=
  uniqueDrift n hn (((solves_iff n _ _).mp h).trans ((solves_iff n _ _).mp (mean_solves n hn r)).symm)

theorem mean_const (hn : Absorbs n) (a : ℝ) : mean n hn (fun _ _ => a) = fun _ => a := by
  symm
  apply eqMean
  intro i
  cases h₀ : n i false <;> cases h₁ : n i true <;> simp [Ends, h₀, h₁] <;> ring

theorem mean_nonneg (hn : Absorbs n) (r : Fin s → Bool → ℝ) (hr : ∀ i b, 0 ≤ r i b) :
    ∀ i, 0 ≤ mean n hn r i := by
  apply minimumLaw n hn
  intro i
  rw [mean_solves n hn r i]
  cases h₀ : n i false <;> cases h₁ : n i true <;> simp [Ends, h₀, h₁, hr, add_nonneg]

theorem mean_mono (hn : Absorbs n) {a b : Fin s → Bool → ℝ} (h : a ≤ b) :
    mean n hn a ≤ mean n hn b := by
  have hh := mean_nonneg n hn (b - a) (fun i j => sub_nonneg.mpr (h i j))
  rw [map_sub] at hh
  exact fun i => sub_nonneg.mp (hh i)

end

open Finset

section
variable {q N : ℕ}
variable (f : Fin q → Equiv.Perm (Fin N))

def row (j : Fin q) : Finset (Fin N × Fin N) :=
  univ.map ⟨fun x => (x,f j x), fun _ _ h => congrArg Prod.fst h⟩

@[simp] theorem mem_row (x y : Fin N) (j : Fin q) : (x,y) ∈ row f j ↔ f j x = y := by
  rw [row, mem_map]
  change (∃ a ∈ univ, (a,f j a) = (x,y)) ↔ _
  simp

@[simp] theorem card_row (j : Fin q) : (row f j).card = N := by simp [row]

def cost (B H : Fin N → Fin N → Bool) (D : Finset (Fin q)) :=
  (univ.filter (fun z : Fin N × Fin N => H z.1 z.2 ≠
    xor (B z.1 z.2) (decide (z.2 ∈ D.image (fun j => f j z.1))))).card

def changed (B H : Fin N → Fin N → Bool) :=
  univ.filter (fun z : Fin N × Fin N => H z.1 z.2 ≠ B z.1 z.2)

@[simp] theorem cost_empty (B H : Fin N → Fin N → Bool) :
    cost f B H ∅ = (changed B H).card := by simp [cost, changed]

theorem separateRows (hf : ∀ x, Function.Injective (fun j => f j x))
    {j k : Fin q} (hne : j ≠ k) : Disjoint (row f j) (row f k) := by
  rw [disjoint_left]
  rintro ⟨x,y⟩ h1 h2
  exact hne (hf x ((mem_row .. |>.mp h1).trans (mem_row .. |>.mp h2).symm))

theorem overlap (hf : ∀ x, Function.Injective (fun j => f j x)) (S : Finset (Fin N × Fin N))
    (D : Finset (Fin q)) :
    (S ∩ D.biUnion (row f)).card = ∑ j ∈ D, (S ∩ row f j).card := by
  rw [inter_biUnion, card_biUnion]
  intro j _ k _ hne
  exact (separateRows f hf hne).mono (inter_subset_right ..) (inter_subset_right ..)

theorem totalEdits (hf : ∀ x, Function.Injective (fun j => f j x)) (S : Finset (Fin N × Fin N)) :
    (∑ j, (S ∩ row f j).card) ≤ S.card := by
  rw [← overlap f hf]
  exact card_le_card (inter_subset_left ..)

theorem cost_id (hf : ∀ x, Function.Injective (fun j => f j x))
    (B H : Fin N → Fin N → Bool) (D : Finset (Fin q)) :
    cost f B H D + 2*(∑ j ∈ D, (changed B H ∩ row f j).card) =
      (changed B H).card + N*D.card := by
  let S := changed B H
  let U := D.biUnion (row f)
  have hU (x y) : (x,y) ∈ U ↔ y ∈ D.image (fun j => f j x) := by simp [U]
  have hcard : U.card = N*D.card := by
    rw [show U = D.biUnion (row f) from rfl, card_biUnion (fun _ _ _ _ h => separateRows f hf h)]
    simp [Nat.mul_comm]
  have hset : (univ.filter (fun z : Fin N × Fin N => H z.1 z.2 ≠
      xor (B z.1 z.2) (decide (z.2 ∈ D.image (fun j => f j z.1))))) =
      (S \ U) ∪ (U \ S) := by
    ext ⟨x,y⟩
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_sdiff, hU, S, changed]
    by_cases h : y ∈ D.image (fun j => f j x) <;> cases H x y <;> cases B x y <;> simp [h]
  have hd : Disjoint (S \ U) (U \ S) := by exact disjoint_left.mpr (fun _ hs hu => (mem_sdiff.mp hs).2 (mem_sdiff.mp hu).1)
  change _ + 2*(∑ j ∈ D, (S ∩ row f j).card) = S.card + _
  unfold cost
  rw [hset, card_union_of_disjoint hd, ← overlap f hf, ← hcard]
  have h₁ := card_sdiff_add_card_inter S U
  have h₂ := card_sdiff_add_card_inter U S
  rw [inter_comm U S] at h₂
  change _ + 2*(S ∩ U).card = _
  omega

end

theorem smallSet {q t : ℕ} (ht : 0 < t) (htq : t < q) (a : Fin q → ℝ) :
    ∃ D : Finset (Fin q), D.card = t ∧
      (q:ℝ)*(∑ j ∈ D, a j) ≤ (t:ℝ)*∑ j, a j ∧
      ((q:ℝ)*(∑ j ∈ D, a j) = (t:ℝ)*∑ j, a j → ∀ j, (q:ℝ)*a j = ∑ i, a i) := by
  classical
  let sets := univ.powersetCard t (α := Fin q)
  have hmem (D : Finset (Fin q)) : D ∈ sets ↔ D.card = t := by simp [sets]
  have hex : sets.Nonempty := by
    obtain ⟨D,_,hD⟩ := exists_subset_card_eq (s := (univ : Finset (Fin q))) (n := t) (by simpa using htq.le)
    exact ⟨D,(hmem D).mpr hD⟩
  obtain ⟨D,hD,hmin⟩ := sets.exists_min_image (fun d => ∑ j ∈ d, a j) hex
  have hc := (hmem D).mp hD
  have hcmp (i) (hi : i ∈ D) (j) (hj : j ∉ D) : a i ≤ a j := by
    have hje : j ∉ D.erase i := fun e => hj (mem_of_mem_erase e)
    have hsize : (insert j (D.erase i)).card = t := by rw [card_insert_of_notMem hje, card_erase_of_mem hi, hc]; omega
    have he := hmin _ ((hmem _).mpr hsize)
    rw [sum_insert hje] at he
    linarith [sum_erase_add D a hi]
  obtain ⟨m,hm,hmax⟩ := D.exists_max_image a (card_pos.mp (hc ▸ ht))
  let S := ∑ j ∈ D, a j
  let C := ∑ j ∈ Dᶜ, a j
  have hcompl : (Dᶜ.card : ℝ) = q - t := by rw [card_compl, Fintype.card_fin, hc, Nat.cast_sub htq.le]
  have hsum : S+C = ∑ j, a j := sum_add_sum_compl D a
  have hupper := sum_le_sum (s := D) (g := fun _ => a m) hmax
  have hlower := sum_le_sum (s := Dᶜ) (f := fun _ => a m) (fun j hj => hcmp m hm j (mem_compl.mp hj))
  simp only [sum_const, nsmul_eq_mul, hc] at hupper
  simp only [sum_const, nsmul_eq_mul, hcompl] at hlower
  change S ≤ t*a m at hupper
  change ((q:ℝ)-t)*a m ≤ C at hlower
  have ht' : (0:ℝ)<t := by exact_mod_cast ht
  have hqt : (0:ℝ)<q-t := sub_pos.mpr (by exact_mod_cast htq)
  have bound : (q:ℝ)*S ≤ (t:ℝ)*(S+C) := by
    nlinarith [mul_nonneg hqt.le (sub_nonneg.mpr hupper), mul_nonneg ht'.le (sub_nonneg.mpr hlower)]
  refine ⟨D,hc, hsum ▸ bound, ?_⟩
  intro heq
  change (q:ℝ)*S = (t:ℝ)*_ at heq
  rw [← hsum] at heq
  have eS : S = t*a m := by
    by_contra! hn
    have he := lt_of_le_of_ne hupper hn
    nlinarith [mul_pos hqt (sub_pos.mpr he), mul_nonneg ht'.le (sub_nonneg.mpr hlower)]
  have eC : C = ((q:ℝ)-t)*a m := by
    have eq : (t:ℝ)*(C-(q-t)*a m) = 0 := by linear_combination -heq + (q-t)*eS
    exact sub_eq_zero.mp ((mul_eq_zero.mp eq).resolve_left ht'.ne')
  have all (j) : a j = a m := by
    by_cases hj : j ∈ D
    · exact (sum_eq_sum_iff_of_le hmax).mp (by simpa [sum_const, hc, nsmul_eq_mul] using eS) j hj
    · have k := (sum_eq_sum_iff_of_le (s := Dᶜ) (f := fun _ => a m) (g := a)
          (fun l hl => hcmp m hm l (mem_compl.mp hl))).mp (by simpa [nsmul_eq_mul,hcompl] using eC.symm)
      exact (k j (mem_compl.mpr hj)).symm
  intro j
  simp only [all, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem gameBound {q N t E : ℕ} (hq : 1 < q) (hqN : q ≤ N) (hE : E < q)
    (ht : q < 2*t) (htq : t < q) (e : ℝ) (a : Fin q → ℝ)
    (hes : (∑ j, a j) ≤ e) (heE : e ≤ E)
    (pay : Finset (Fin q) → ℝ)
    (hpay : ∀ D, pay D = e + (N:ℝ)*D.card - 2*∑ j ∈ D, a j) :
    let target := ((q*N*t-(2*t-q)*E : ℕ):ℝ)/(q:ℝ)
    (∃ D, D.card = t ∧ target ≤ pay D) ∧
      ((∀ D : Finset (Fin q), D.card=t → pay D ≤ target) → ∀ j, (q:ℝ)*a j = E) := by
  dsimp only
  have ht0 : 0 < t := by omega
  obtain ⟨D, hD, hlo, hequal⟩ := smallSet ht0 htq a
  have hqt : 2*t-q ≤ t := by omega
  have hn1 : (2*t-q)*E ≤ q*N*t := calc
    _ ≤ t*N := Nat.mul_le_mul hqt (by omega)
    _ ≤ _ := by rw [mul_comm t, mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hq' : 0 < (q:ℝ) := by exact_mod_cast (show 0 < q by omega)
  have ht' : 0 < (t:ℝ) := by exact_mod_cast ht0
  have hcoeff : 0 < 2*(t:ℝ)-q := sub_pos.mpr (by exact_mod_cast ht)
  let goal := ((q*N*t-(2*t-q)*E : ℕ):ℝ)/(q:ℝ)
  have hgoal : (q:ℝ)*goal = (q:ℝ)*N*t - (2*(t:ℝ)-q)*E := by
    dsimp [goal]
    rw [Nat.cast_sub hn1]
    push_cast [Nat.cast_sub ht.le]
    field_simp
  have hg : pay D = e + (N:ℝ)*t - 2*∑ j ∈ D, a j := hD ▸ hpay D
  have hgap : (q:ℝ)*(pay D-goal) =
      (2*(t:ℝ)-q)*(E-e) + 2*t*(e-∑ j, a j) +
        2*((t:ℝ)*(∑ j, a j)-q*(∑ j ∈ D, a j)) := by
    rw [mul_sub,hgoal,hg]
    ring
  have h₁ := mul_nonneg hcoeff.le (sub_nonneg.mpr heE)
  have h₂ := mul_nonneg (show 0 ≤ 2*(t:ℝ) by positivity) (sub_nonneg.mpr hes)
  have h₃ := sub_nonneg.mpr hlo
  have low : goal ≤ pay D := by
    apply sub_nonneg.mp
    apply nonneg_of_mul_nonneg_right (a := (q:ℝ)) _ hq'
    linarith
  refine ⟨⟨D,hD,low⟩, ?_⟩
  intro h
  have heq := le_antisymm (h D hD) low
  change pay D = goal at heq
  rw [heq, sub_self, mul_zero] at hgap
  have e₁ : e = E := by
    by_contra! hn
    linarith [mul_pos hcoeff (sub_pos.mpr (lt_of_le_of_ne heE hn))]
  have e₂ : (∑ j, a j) = e := by
    by_contra! hn
    linarith [mul_pos (show 0 < 2*(t:ℝ) by positivity) (sub_pos.mpr (lt_of_le_of_ne hes hn))]
  have e₃ : (q:ℝ)*(∑ j ∈ D, a j) = (t:ℝ)*∑ j, a j := by linarith
  exact fun j => (hequal e₃ j).trans (e₂.trans e₁)

noncomputable def goalLoss (q N t E : ℕ) := ((q*N*t-(2*t-q)*E : ℕ) : ℝ)/(q : ℝ)
theorem boolSum (u : Bool → ℝ) : ∑ b, u b = u false + u true := by simp [Fintype.sum_bool, add_comm]

theorem equalize {q N s E t : ℕ} (hq : 1 < q) (hE : E < q)
    (hqN : q ≤ N) (ht : q < 2*t) (htq : t < q)
    (f : Fin q → Equiv.Perm (Fin N)) (hf : ∀ x, Function.Injective (fun j => f j x))
    (B : Fin N → Fin N → Bool) (z : Fin s) (n : Fin s → Bool → Option (Fin s))
    (H : Fin s → Bool → Fin N → Fin N → Bool) (L : Fin s → Finset (Fin q) → ℝ)
    (hn : Absorbs n) (hL : ∀ i D, 2*L i D = ∑ b : Bool, (n i b).elim (cost f B (H i b) D : ℝ) (fun j => L j D))
    (herr : ∀ i b, cost f B (H i b) ∅ ≤ E)
    (hopt : ∀ D : Finset (Fin q), D.card = t → L z D ≤ goalLoss q N t E) :
    ∃ (d : Fin s → Bool → Fin q → ℕ) (V : Fin s → Fin q → ℝ),
      (∀ j, Solves n (fun i b => (d i b j : ℝ)) (fun i => V i j)) ∧
      (∀ i j, 0 ≤ V i j) ∧ (∀ i, ∑ j, V i j ≤ E) ∧
      (∀ i b, ∑ j, d i b j ≤ E) ∧ (∀ j, (q:ℝ)*V z j = E) := by
  let A := mean n hn
  let marks := fun i b => changed B (H i b)
  let total := fun i b => ((marks i b).card : ℝ)
  let d := fun i b j => (marks i b ∩ row f j).card
  let R := fun (j : Fin q) (i : Fin s) (b : Bool) => (d i b j : ℝ)
  let V := fun (i : Fin s) (j : Fin q) => A (R j) i
  have hnon (i j) : 0 ≤ V i j := mean_nonneg n hn _ (fun _ _ => Nat.cast_nonneg _) i
  have httle : A total ≤ fun _ => (E:ℝ) := by
    rw [← mean_const n hn E]
    apply mean_mono
    intro i b
    change ((marks i b).card : ℝ) ≤ E
    exact_mod_cast (show (marks i b).card ≤ E by simpa [marks] using herr i b)
  have sumBound : (∑ j, R j) ≤ total := by
    intro i b
    change ((∑ j, R j) i b) ≤ _
    simp only [Finset.sum_apply, R, total, d]
    exact_mod_cast totalEdits f hf (marks i b)
  have hvSum (i) : (∑ j, V i j) ≤ A total i := by
    have hh := mean_mono n hn sumBound i
    simpa [V, A, map_sum, Finset.sum_apply] using hh
  have payoff (D : Finset (Fin q)) :
      L z D = A total z + (N:ℝ)*D.card - 2*∑ j ∈ D, V z j := by
    let r := fun i b => (cost f B (H i b) D : ℝ)
    have he := eqMean n hn (r := r) (x := fun i => L i D)
      (fun i => by simpa only [boolSum, Ends, r] using hL i D)
    have idR : r = total + (fun _ _ => (N:ℝ)*D.card) - (2:ℝ) • ∑ j ∈ D, R j := by
      funext i b
      simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_apply,r,total,R,d,marks]
      have hh := cost_id f hf B (H i b) D
      have hc : (cost f B (H i b) D : ℝ) + 2*(∑ j ∈ D, ((changed B (H i b) ∩ row f j).card : ℝ)) =
          ((changed B (H i b)).card : ℝ) + (N:ℝ)*D.card := by exact_mod_cast hh
      linarith
    have val := congrFun he z
    rw [idR, map_sub, map_add, map_smul, map_sum, mean_const] at val
    simpa [A,V, Finset.sum_apply] using val
  obtain ⟨hex,heq⟩ := gameBound hq hqN hE ht htq (A total z) (V z) (hvSum z) (httle z) (L z) payoff
  refine ⟨d, V, fun j => mean_solves n hn _, hnon, fun i => (hvSum i).trans (httle i), ?_, heq hopt⟩
  intro i b
  exact (totalEdits f hf (marks i b)).trans (by simpa [marks] using herr i b)

end PEqualNP.Outside.L_meta_29779.Tail

namespace PEqualNP.Outside.L_meta_29779.Tail

open Finset

variable {s : ℕ}

def atWord (n : Fin s → Bool → Option (Fin s)) (start : Option (Fin s))
    {b : ℕ} (w : Fin b → Bool) : Option (Fin s) :=
  (List.ofFn w).foldl (fun x bit => x.bind (fun i => n i bit)) start

theorem empty_run (n : Fin s → Bool → Option (Fin s)) (l : List Bool) :
    l.foldl (fun (x : Option (Fin s)) bit => x.bind (fun i => n i bit)) none = none := by
  induction l with
  | nil => rfl
  | cons a l ih => exact ih

def suffix (n : Fin s → Bool → Option (Fin s)) (start : Option (Fin s))
    (b : ℕ) (V : Fin s → ℝ) : ℝ :=
  ∑ w : Fin b → Bool, (atWord n start w).elim 0 V

@[simp] theorem suffix_none (n : Fin s → Bool → Option (Fin s)) (b : ℕ) (V : Fin s → ℝ) :
    suffix n none b V = 0 := by simp [suffix, atWord, empty_run]

theorem suffix_succ (n : Fin s → Bool → Option (Fin s)) (i : Fin s)
    (b : ℕ) (V : Fin s → ℝ) : suffix n (some i) (b+1) V =
    suffix n (n i false) b V + suffix n (n i true) b V := by
  unfold suffix
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (b+1) => Bool)) _, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, Fin.consEquiv_apply, atWord, List.ofFn_cons, List.foldl_cons,
    Option.bind_some]
  ac_rfl

def paid (n : Fin s → Bool → Option (Fin s)) (d : Fin s → Bool → ℕ) :
    ℕ → Fin s → ℕ
  | 0, _ => 0
  | b+1, i => (n i false).elim (2^b*d i false) (paid n d b) +
      (n i true).elim (2^b*d i true) (paid n d b)

theorem split_pay (n : Fin s → Bool → Option (Fin s)) (d : Fin s → Bool → ℕ)
    (V : Fin s → ℝ) (hv : Solves n (fun i t => (d i t : ℝ)) V) (b : ℕ) (i : Fin s) :
    2^b*V i = (paid n d b i : ℝ) + suffix n (some i) b V := by
  induction b generalizing i with
  | zero => simp [paid, suffix, atWord]
  | succ b ih =>
    have eq := congrArg ((2:ℝ)^b * ·) (hv i)
    rw [pow_succ, mul_assoc, eq, mul_add, suffix_succ]
    cases ha : n i false <;> cases hb : n i true <;>
      simp [paid, Ends, ha, hb, ih, add_comm, add_left_comm, add_assoc]

def liveCount (n : Fin s → Bool → Option (Fin s)) (z : Fin s) (b : ℕ) : ℕ :=
  (univ.filter (fun w : Fin b → Bool => (atWord n (some z) w).isSome)).card

theorem suffix_sum_le {q : ℕ} (n : Fin s → Bool → Option (Fin s)) (z : Fin s) (b : ℕ)
    (V : Fin s → Fin q → ℝ) (E : ℕ) (hv : ∀ i, ∑ j, V i j ≤ E) :
    (∑ j, suffix n (some z) b (fun i => V i j)) ≤ (liveCount n z b : ℝ)*E := by
  unfold suffix
  rw [sum_comm]
  calc
    _ ≤ ∑ w : Fin b → Bool, (if (atWord n (some z) w).isSome then (E:ℝ) else 0) := by
      apply sum_le_sum
      intro w _
      cases h : atWord n (some z) w with
      | none => simp
      | some i => simpa using hv i
    _ = _ := by simp [sum_ite, liveCount]

theorem finite_tail {q E : ℕ} (hq : 0 < q) (hE : 0 < E)
    (n : Fin s → Bool → Option (Fin s)) (z : Fin s)
    (d : Fin s → Bool → Fin q → ℕ) (V : Fin s → Fin q → ℝ)
    (sol : ∀ j, Solves n (fun i b => (d i b j : ℝ)) (fun i => V i j))
    (nonneg : ∀ i j, 0 ≤ V i j) (bound : ∀ i, ∑ j, V i j ≤ E)
    (equal : ∀ j, (q:ℝ)*V z j = E) (b : ℕ) :
    ((2^b*E % q)+E-1)/E ≤ liveCount n z b := by
  let P := fun j => paid n (fun i bit => d i bit j) b z
  let T := fun j => suffix n (some z) b (fun i => V i j)
  have split (j) : 2^b*V z j = (P j : ℝ) + T j := split_pay _ _ _ (sol j) b z
  have tpos (j) : 0 ≤ T j := by
    apply sum_nonneg
    intro w _
    cases h : atWord n (some z) w with
    | none => simp
    | some i => exact nonneg i j
  have cap (j) : P j ≤ (2^b*E)/q := by
    apply (Nat.le_div_iff_mul_le hq).2
    have a : (P j : ℝ) ≤ 2^b*V z j := by linarith [split j, tpos j]
    have bnd := mul_le_mul_of_nonneg_right a (Nat.cast_nonneg q : (0:ℝ) ≤ q)
    rw [mul_right_comm, mul_assoc, equal] at bnd
    exact_mod_cast bnd
  have total : (∑ j, P j) ≤ q*((2^b*E)/q) := by
    simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] using
      sum_le_sum (s := (univ : Finset (Fin q))) (fun j _ => cap j)
  have vsum : (∑ j, V z j) = E := by
    have h := sum_congr (s₁:=univ) rfl (fun j _ => equal j)
    rw [← mul_sum] at h
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    exact mul_left_cancel₀ (by exact_mod_cast hq.ne' : (q:ℝ) ≠ 0) h
  have hs := sum_congr (s₁:=univ) rfl (fun j _ => split j)
  rw [← mul_sum, vsum, sum_add_distrib] at hs
  have ht := suffix_sum_le n z b V E bound
  change (∑ j, T j) ≤ _ at ht
  have hb : 2^b*E ≤ q*((2^b*E)/q)+liveCount n z b*E := by
    exact_mod_cast (show (2:ℝ)^b*E ≤ q*(((2^b*E)/q : ℕ):ℝ)+(liveCount n z b : ℝ)*E by
      push_cast at hs
      have hp : (∑ j, (P j:ℝ)) ≤ q*(((2^b*E)/q : ℕ):ℝ) := by exact_mod_cast total
      linarith)
  have hm := Nat.mod_add_div (2^b*E) q
  have hr : 2^b*E%q ≤ liveCount n z b*E := by omega
  apply (Nat.div_le_iff_le_mul_add_pred hE).2
  rw [Nat.mul_comm E (liveCount n z b)]
  omega

end PEqualNP.Outside.L_meta_29779.Tail

namespace PEqualNP.Outside.L_meta_29779.Tail

def width (q E b : ℕ) := ((2^b*E % q)+E-1)/E

theorem universal {d e g p N t : ℕ} (hd : 1 < d) (he : 0 < e) (hed : e < d)
    (cop : d.Coprime e) (hg : 0 < g) (hp : 0 < p) (hpow : 2^p % d = 1)
    (minimal : ∀ h, 0 < h → h < p → 2^h % d ≠ 1)
    (hqN : g*d ≤ N) (ht : g*d < 2*t) (htq : t < g*d)
    (f : Fin (g*d) → Equiv.Perm (Fin N)) (hf : ∀ x, Function.Injective (fun j => f j x))
    (B : Fin N → Fin N → Bool) :
    ∀ (s : ℕ) (z : Fin s) (n : Fin s → Bool → Option (Fin s))
      (H : Fin s → Bool → Fin N → Fin N → Bool) (L : Fin s → Finset (Fin (g*d)) → ℝ),
      (Absorbs n ∧ ∀ i D, 2*L i D = ∑ bit : Bool,
        (n i bit).elim (cost f B (H i bit) D : ℝ) (fun j => L j D)) →
      (∀ i bit, cost f B (H i bit) ∅ ≤ g*e) →
      (∀ D : Finset (Fin (g*d)), D.card=t → L z D ≤ goalLoss (g*d) N t (g*e)) →
      (∀ b, width (g*d) (g*e) b ≤ liveCount n z b) ∧
      ((∀ b, liveCount n z b = width (g*d) (g*e) b) →
        ∃ l : ℕ, 0 < l ∧ l ≤ s ∧ p ∣ l ∧ ∀ b, width (g*d) (g*e) b ≤ 2^(s-l)) := by
  intro s z n H L law herr hopt
  have qgt : 1 < g*d := lt_of_lt_of_le hd (Nat.le_mul_of_pos_left d hg)
  have Eb : g*e < g*d := Nat.mul_lt_mul_of_pos_left hed hg
  obtain ⟨pay,V,sol,nonneg,bound,_,mass⟩ := equalize qgt Eb hqN ht htq f hf B z n H L
    law.1 law.2 herr hopt
  refine ⟨fun b => finite_tail (by omega) (Nat.mul_pos hg he) n z pay V sol nonneg bound mass b, ?_⟩
  intro exactWidth
  have singleton (k : ℕ) : ∃ b ≥ k, liveCount n z b = 1 := by
    exact ⟨p*k, Nat.le_mul_of_pos_left k hp, (exactWidth _).trans
      (Period.singleton_width hd he hed hg hpow k)⟩
  obtain ⟨l,hl,hls,_,hlive,integral⟩ := CycleAux.cycleCore s z n singleton
  let j : Fin (g*d) := ⟨0, by omega⟩
  have value := integral (fun i bit => (pay i bit j : ℤ)) (fun i => V i j) (by
    intro i
    rw [boolSum]
    simpa only [Ends, Int.cast_natCast] using sol j i)
  exact ⟨l,hl,hls,Period.denominator_period hd hg cop hp hpow minimal (V z j) (mass j) value,
    fun b => (exactWidth b).symm.le.trans (hlive b)⟩

end PEqualNP.Outside.L_meta_29779.Tail

namespace PEqualNP.Outside.L_meta_29779.Block.Pack

open Finset

theorem interm : ∀ (q : ℕ) (lo hi : Fin q → ℕ) (T : ℕ), (∀ j, lo j ≤ hi j) →
    ∑ j, lo j ≤ T → T ≤ ∑ j, hi j →
    ∃ x : Fin q → ℕ, (∀ j, lo j ≤ x j ∧ x j ≤ hi j) ∧ ∑ j, x j = T := by
  intro q
  induction q with
  | zero =>
    intro lo hi T _ _ h2
    refine ⟨fun _ => 0, fun j => j.elim0, ?_⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at h2 ⊢
    omega
  | succ q ih =>
    intro lo hi T hle h1 h2
    rw [Fin.sum_univ_succ] at h1 h2
    have hAB : ∑ i : Fin q, lo i.succ ≤ ∑ i : Fin q, hi i.succ :=
      Finset.sum_le_sum (fun i _ => hle i.succ)
    have h0 := hle 0
    obtain ⟨y, hy, hys⟩ := ih (fun i => lo i.succ) (fun i => hi i.succ)
      (T - max (lo 0) (T - ∑ i : Fin q, hi i.succ)) (fun i => hle i.succ) (by omega) (by omega)
    refine ⟨Fin.cons (max (lo 0) (T - ∑ i : Fin q, hi i.succ)) y, ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp only [Fin.cons_zero]; omega
      · simp only [Fin.cons_succ]; exact hy i
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [hys]; omega

theorem split (q E : ℕ) : ∀ (k : ℕ) (v : Fin q → ℕ), ∑ j, v j = E * k →
    ∃ g : Fin k → Fin q → ℕ, (∀ w, ∑ j, g w j = E) ∧ ∀ j, ∑ w, g w j = v j := by
  intro k
  induction k with
  | zero =>
    intro v hv
    refine ⟨fun w => w.elim0, fun w => w.elim0, fun j => ?_⟩
    rw [mul_zero, Finset.sum_eq_zero_iff] at hv
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact (hv j (Finset.mem_univ j)).symm
  | succ k ih =>
    intro v hv
    obtain ⟨a, ha, has⟩ := interm q (fun _ => 0) v E (fun _ => Nat.zero_le _) (by simp)
      (by rw [hv]; exact Nat.le_mul_of_pos_right _ (Nat.succ_pos k))
    have hsub : ∑ j, (v j - a j) + ∑ j, a j = ∑ j, v j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => Nat.sub_add_cancel (ha j).2)
    obtain ⟨g, hg1, hg2⟩ := ih (fun j => v j - a j) (by
      have e : E * (k+1) = E * k + E := by ring
      rw [hv, e, has] at hsub
      exact Nat.add_right_cancel hsub)
    refine ⟨Fin.cons a g, ?_, ?_⟩
    · intro w
      refine Fin.cases ?_ (fun i => ?_) w
      · simpa using has
      · simpa using hg1 i
    · intro j
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [hg2 j]
      have := (ha j).2
      omega

theorem shift (b : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ range (b+1), 2^(b+1-1-i) * f i = 2 * ∑ i ∈ range b, 2^(b-1-i) * f i + f b := by
  rw [sum_range_succ, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro i hi
    rw [mem_range] at hi
    rw [show b+1-1-i = (b-1-i)+1 by omega, pow_succ]
    ring
  · simp

theorem tele (u : ℕ → ℕ) (h0 : u 0 = 1) : ∀ b, (∀ i < b, u (i+1) ≤ 2*u i) →
    u b ≤ 2^b ∧ ∑ i ∈ range b, 2^(b-1-i) * (2*u i - u (i+1)) = 2^b - u b := by
  intro b
  induction b with
  | zero => intro _; simp [h0]
  | succ b ih =>
    intro hs
    obtain ⟨h1, h2⟩ := ih (fun i hi => hs i (by omega))
    have h3 := hs b (by omega)
    refine ⟨by rw [pow_succ]; omega, ?_⟩
    rw [shift b (fun i => 2*u i - u (i+1))]
    rw [h2, pow_succ]
    omega

theorem sumA (E q : ℕ) (u : ℕ → ℕ) (h0 : u 0 = 1) (c : ℕ → Fin q → ℕ) (b : ℕ)
    (hs : ∀ i < b, u (i+1) ≤ 2*u i) (hc : ∀ i < b, ∑ j, c i j = E * (2*u i - u (i+1))) :
    ∑ j, ∑ i ∈ range b, 2^(b-1-i) * c i j = E * (2^b - u b) := by
  rw [Finset.sum_comm, ← (tele u h0 b hs).2, mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [mem_range] at hi
  rw [← mul_sum, hc i hi]
  ring

theorem div2 (m p b : ℕ) (hb : b < p) : 2 * (m / 2^(p-b)) ≤ m / 2^(p-(b+1)) := by
  rw [show p - b = (p-(b+1)) + 1 by omega, pow_succ, ← Nat.div_div_eq_div_mul]
  exact Nat.mul_div_le _ _

theorem nec (p E q : ℕ) (hE : 0 < E) (M : Fin q → ℕ) (u : ℕ → ℕ) (h0 : u 0 = 1)
    (hs : ∀ b < p, u (b+1) ≤ 2*u b) (c : ℕ → Fin q → ℕ)
    (hc : ∀ i < p, ∑ j, c i j = E * (2*u i - u (i+1)))
    (hM : ∀ j, ∑ i ∈ range p, 2^(p-1-i) * c i j = M j) :
    ∀ b ≤ p, 2^b - (∑ j, M j / 2^(p-b)) / E ≤ u b := by
  intro b hb
  have hA : ∀ j, ∑ i ∈ range b, 2^(b-1-i) * c i j ≤ M j / 2^(p-b) := by
    intro j
    rw [Nat.le_div_iff_mul_le (by positivity), ← hM j, sum_mul]
    calc ∑ i ∈ range b, 2^(b-1-i) * c i j * 2^(p-b)
        = ∑ i ∈ range b, 2^(p-1-i) * c i j := by
          apply sum_congr rfl; intro i hi; rw [mem_range] at hi
          rw [show p-1-i = (b-1-i) + (p-b) by omega, pow_add]; ring
      _ ≤ ∑ i ∈ range p, 2^(p-1-i) * c i j :=
          sum_le_sum_of_subset (Finset.range_mono hb)
  have hsum := sumA E q u h0 c b (fun i hi => hs i (by omega)) (fun i hi => hc i (by omega))
  have hle : E * (2^b - u b) ≤ ∑ j, M j / 2^(p-b) := by
    rw [← hsum]; exact sum_le_sum (fun j _ => hA j)
  have : 2^b - u b ≤ (∑ j, M j / 2^(p-b)) / E :=
    (Nat.le_div_iff_mul_le hE).2 (by rw [mul_comm]; exact hle)
  omega

theorem suff (p E q : ℕ) (hE : 0 < E) (M : Fin q → ℕ) (hMs : ∑ j, M j = (2^p-1)*E)
    (u : ℕ → ℕ) (h0 : u 0 = 1) (hp1 : u p = 1)
    (hs : ∀ b < p, u (b+1) ≤ 2*u b)
    (hb : ∀ b ≤ p, 2^b - (∑ j, M j / 2^(p-b)) / E ≤ u b) :
    ∃ c : ℕ → Fin q → ℕ, (∀ i < p, ∑ j, c i j = E * (2*u i - u (i+1))) ∧
      ∀ j, ∑ i ∈ range p, 2^(p-1-i) * c i j = M j := by
  have hcap : ∀ b ≤ p, E * (2^b - u b) ≤ ∑ j, M j / 2^(p-b) := by
    intro b hbp
    have h1 := hb b hbp
    have h2 := Nat.mul_div_le (∑ j, M j / 2^(p-b)) E
    have h3 : 2^b - u b ≤ (∑ j, M j / 2^(p-b)) / E := by
      generalize (∑ j, M j / 2^(p-b)) / E = Y at h1 ⊢
      omega
    calc E * (2^b - u b) ≤ E * ((∑ j, M j / 2^(p-b)) / E) := Nat.mul_le_mul_left _ h3
      _ ≤ _ := h2
  have key : ∀ b ≤ p, ∃ c : ℕ → Fin q → ℕ, (∀ i < b, ∑ j, c i j = E * (2*u i - u (i+1))) ∧
      ∀ j, ∑ i ∈ range b, 2^(b-1-i) * c i j ≤ M j / 2^(p-b) := by
    intro b
    induction b with
    | zero =>
      intro _
      exact ⟨fun _ _ => 0, fun i hi => absurd hi (Nat.not_lt_zero _), fun j => by simp⟩
    | succ b ih =>
      intro hbp
      obtain ⟨c, hc1, hc2⟩ := ih (by omega)
      have ht := tele u h0 b (fun i hi => hs i (by omega))
      have hs' := hs b (by omega)
      have hsA := sumA E q u h0 c b (fun i hi => hs i (by omega)) hc1
      obtain ⟨A, hAdef⟩ : ∃ A : Fin q → ℕ, ∀ j, A j = ∑ i ∈ range b, 2^(b-1-i) * c i j :=
        ⟨_, fun j => rfl⟩
      have hsA' : ∑ j, A j = E * (2^b - u b) := by simp only [hAdef]; exact hsA
      have hsA2 : ∑ j, 2 * A j = 2 * (E * (2^b - u b)) := by rw [← mul_sum, hsA']
      obtain ⟨x, hx, hxs⟩ := interm q (fun j => 2 * A j)
        (fun j => M j / 2^(p-(b+1))) (E * (2^(b+1) - u (b+1)))
        (fun j => le_trans (Nat.mul_le_mul_left 2 (hAdef j ▸ hc2 j)) (div2 _ p b (by omega)))
        (by
          rw [hsA2]
          calc 2 * (E * (2^b - u b)) = E * (2 * (2^b - u b)) := by ring
            _ ≤ E * (2^(b+1) - u (b+1)) := Nat.mul_le_mul_left _ (by rw [pow_succ]; omega))
        (hcap (b+1) hbp)
      have hrow : ∑ j, (x j - 2 * A j) = E * (2*u b - u (b+1)) := by
        have e1 : ∑ j, (x j - 2 * A j) + ∑ j, 2 * A j = ∑ j, x j := by
          rw [← sum_add_distrib]; exact sum_congr rfl (fun j _ => Nat.sub_add_cancel (hx j).1)
        rw [hsA2, hxs] at e1
        have e2 : 2^(b+1) - u (b+1) = 2 * (2^b - u b) + (2*u b - u (b+1)) := by
          rw [pow_succ]; omega
        have e3 : E * (2 * (2^b - u b)) = 2 * (E * (2^b - u b)) := by ring
        rw [e2, mul_add, e3, add_comm (2 * (E * (2^b - u b)))] at e1
        exact Nat.add_right_cancel e1
      refine ⟨fun i j => if i = b then x j - 2 * A j else c i j, ?_, ?_⟩
      · intro i hi
        by_cases hib : i = b
        · subst hib
          simpa using hrow
        · simp only [hib, if_false]
          exact hc1 i (by omega)
      · intro j
        rw [shift b (fun i => if i = b then x j - 2 * A j else c i j)]
        have e : ∑ i ∈ range b, 2^(b-1-i) * (if i = b then x j - 2 * A j else c i j) = A j := by
          rw [hAdef]; apply sum_congr rfl; intro i hi; rw [mem_range] at hi
          rw [if_neg (by omega)]
        rw [e, if_pos rfl]
        have := hx j
        omega
  obtain ⟨c, hc1, hc2⟩ := key p le_rfl
  refine ⟨c, hc1, ?_⟩
  have hsum := sumA E q u h0 c p hs hc1
  rw [hp1] at hsum
  have hle : ∀ j ∈ univ, ∑ i ∈ range p, 2^(p-1-i) * c i j ≤ M j := by
    intro j _
    have := hc2 j
    rw [Nat.sub_self, pow_zero, Nat.div_one] at this
    exact this
  have heq := (sum_eq_sum_iff_of_le hle).1 (by rw [hsum, hMs, mul_comm])
  exact fun j => heq j (mem_univ j)

theorem fits_to (p E q : ℕ) (M : Fin q → ℕ) (u : ℕ → ℕ)
    (h : (i : Fin p) → Fin (2*u i.val-u (i.val+1)) → Fin q → ℕ)
    (h1 : ∀ i w, (∑ j, h i w j) = E)
    (h2 : ∀ j, (∑ i : Fin p, 2^(p-1-i.val) * ∑ w, h i w j) = M j) :
    ∃ c : ℕ → Fin q → ℕ, (∀ i < p, ∑ j, c i j = E * (2*u i - u (i+1))) ∧
      ∀ j, ∑ i ∈ range p, 2^(p-1-i) * c i j = M j := by
  refine ⟨fun i j => if hi : i < p then ∑ w, h ⟨i, hi⟩ w j else 0, ?_, ?_⟩
  · intro i hi
    simp only [dif_pos hi]
    rw [sum_comm]
    simp only [h1, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    exact mul_comm _ _
  · intro j
    rw [← h2 j, ← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro i _
    beta_reduce
    rw [dif_pos i.isLt]

theorem to_fits (p E q : ℕ) (M : Fin q → ℕ) (u : ℕ → ℕ) (c : ℕ → Fin q → ℕ)
    (hc : ∀ i < p, ∑ j, c i j = E * (2*u i - u (i+1)))
    (hM : ∀ j, ∑ i ∈ range p, 2^(p-1-i) * c i j = M j) :
    ∃ h : (i : Fin p) → Fin (2*u i.val-u (i.val+1)) → Fin q → ℕ,
      (∀ i w, (∑ j, h i w j) = E) ∧
      ∀ j, (∑ i : Fin p, 2^(p-1-i.val) * ∑ w, h i w j) = M j := by
  have := fun i : Fin p => split q E (2*u i.val - u (i.val+1)) (c i.val) (hc i.val i.isLt)
  choose g hg1 hg2 using this
  refine ⟨g, hg1, fun j => ?_⟩
  rw [← hM j, ← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro i _
  rw [hg2]

theorem best0 (p E q : ℕ) (hE : 0 < E) (M : Fin q → ℕ) (hMs : ∑ j, M j = (2^p-1)*E) :
    2^0 - (∑ j, M j / 2^(p-0))/E = 1 := by
  have hlt : ∑ j, M j / 2^(p-0) < E := by
    have h1 : 2^p * ∑ j, M j / 2^(p-0) ≤ ∑ j, M j := by
      rw [mul_sum]; exact sum_le_sum (fun j _ => by rw [Nat.sub_zero]; exact Nat.mul_div_le _ _)
    have h2 : 1 ≤ 2^p := Nat.one_le_two_pow
    by_contra hc
    push_neg at hc
    have h4 := Nat.mul_le_mul_left (2^p) hc
    rw [hMs] at h1
    have h3 : (2^p - 1) * E < 2^p * E := Nat.mul_lt_mul_of_pos_right (by omega) hE
    exact absurd (h4.trans h1) (not_le.2 h3)
  rw [Nat.div_eq_of_lt hlt]
  simp

theorem bestp (p E q : ℕ) (hE : 0 < E) (M : Fin q → ℕ) (hMs : ∑ j, M j = (2^p-1)*E) :
    2^p - (∑ j, M j / 2^(p-p))/E = 1 := by
  simp only [Nat.sub_self, pow_zero, Nat.div_one]
  rw [hMs, Nat.mul_div_cancel _ hE]
  have : 1 ≤ 2^p := Nat.one_le_two_pow
  omega

theorem beststep (p E q : ℕ) (M : Fin q → ℕ) (b : ℕ) (hb : b < p) :
    2^(b+1) - (∑ j, M j / 2^(p-(b+1)))/E ≤ 2 * (2^b - (∑ j, M j / 2^(p-b))/E) := by
  have h1 : 2 * ∑ j, M j / 2^(p-b) ≤ ∑ j, M j / 2^(p-(b+1)) := by
    rw [mul_sum]; exact sum_le_sum (fun j _ => div2 _ p b hb)
  have h2 : 2 * ((∑ j, M j / 2^(p-b))/E) ≤ (∑ j, M j / 2^(p-(b+1)))/E :=
    (Nat.mul_div_le_mul_div_assoc _ _ _).trans (Nat.div_le_div_right h1)
  rw [pow_succ]
  omega

end PEqualNP.Outside.L_meta_29779.Block.Pack

namespace PEqualNP.Outside.L_meta_29779.Block

open Pack in
theorem Pack :
∀ (p E q : ℕ), 0 < p → 0 < E → ∀ M : Fin q → ℕ,
  (∑ j, M j) = (2^p-1)*E →
  let cap := fun b : ℕ => ∑ j, M j / 2^(p-b)
  let best := fun b : ℕ => 2^b-cap b/E
  let shape := fun u : ℕ → ℕ =>
    u 0 = 1 ∧ u p = 1 ∧ ∀ b < p, u (b+1) ≤ 2*u b
  let fits := fun u : ℕ → ℕ =>
    ∃ h : (i : Fin p) → Fin (2*u i.val-u (i.val+1)) → Fin q → ℕ,
      (∀ i w, (∑ j, h i w j) = E) ∧
      ∀ j, (∑ i : Fin p, 2^(p-1-i.val) * ∑ w, h i w j) = M j
  (∀ u, shape u → (fits u ↔ ∀ b ≤ p, best b ≤ u b)) ∧ shape best ∧ fits best := by
  intro p E q hp hE M hMs
  dsimp only
  refine ⟨fun u hu => ⟨fun ⟨h, h1, h2⟩ => ?_, fun hb => ?_⟩, ⟨best0 p E q hE M hMs, bestp p E q hE M hMs,
    fun b hb => beststep p E q M b hb⟩, ?_⟩
  · obtain ⟨c, hc1, hc2⟩ := fits_to p E q M u h h1 h2
    exact nec p E q hE M u hu.1 hu.2.2 c hc1 hc2
  · obtain ⟨c, hc1, hc2⟩ := suff p E q hE M hMs u hu.1 hu.2.1 hu.2.2 hb
    exact to_fits p E q M u c hc1 hc2
  · obtain ⟨c, hc1, hc2⟩ := suff p E q hE M hMs _ (best0 p E q hE M hMs) (bestp p E q hE M hMs)
      (fun b hb => beststep p E q M b hb) (fun b _ => le_rfl)
    exact to_fits p E q M _ c hc1 hc2

end PEqualNP.Outside.L_meta_29779.Block

namespace PEqualNP.Outside.L_meta_29779.Block

open Finset

def width (q E b : ℕ) : ℕ := ((2^b*E % q)+E-1)/E

def quota (d e p : ℕ) : ℕ := (2^p/d)*e

theorem quota_eq {d e g p : ℕ} (hm : 2^p % d = 1) :
    (g*d)*quota d e p + g*e = 2^p*(g*e) := by
  have h := Nat.mod_add_div (2^p) d
  rw [hm] at h
  unfold quota
  calc
    g * d * (2 ^ p / d * e) + g * e = (1+d*(2^p/d))*(g*e) := by ring
    _ = _ := by rw [h]

theorem width_period (g e d p b : ℕ) (hm : 2^p % d = 1) :
    width (g*d) (g*e) (b+p) = width (g*d) (g*e) b := by
  have h := (quota_eq (g:=g) (e:=e) hm).symm
  have expand : 2^(b+p)*(g*e) = 2^b*(g*e)+(g*d)*(2^b*quota d e p) := by
    rw [pow_add,Nat.mul_assoc,h]
    ring
  unfold width
  rw [expand,Nat.add_mul_mod_self_left]

theorem floor_quota {q E k A M : ℕ} (hq : 0 < q) (hE : E < q) (hk : 0 < k)
    (h : q*M+E=k*A) : M/k=A/q := by
  have expand : k*A=k*(A%q)+q*(k*(A/q)) := by
    conv_lhs => rw [← Nat.mod_add_div A q]
    ring
  have Meq : M = (k*(A%q))/q+k*(A/q) := by
    calc
      M = (q*M+E)/q := by rw [Nat.mul_add_div hq, Nat.div_eq_of_lt hE, Nat.add_zero]
      _ = _ := by rw [h,expand,Nat.add_mul_div_left _ _ hq]
  have hlt : k*(A%q)/q < k :=
    (Nat.div_lt_iff_lt_mul hq).2 (Nat.mul_lt_mul_of_pos_left (Nat.mod_lt _ hq) hk)
  rw [Meq,Nat.add_mul_div_left _ _ hk,Nat.div_eq_of_lt hlt,Nat.zero_add]

theorem floor_width {q E z : ℕ} (hE : 0<E) :
    z - (q*((z*E)/q))/E = ((z*E)%q+E-1)/E := by
  let A := q*((z*E)/q)
  let r := (z*E)%q
  have hs : r+A=z*E := Nat.mod_add_div _ _
  change z-A/E = (r+E-1)/E
  have had := Nat.mod_add_div A E
  have hex : (z-A/E)*E = r+A%E := by
    rw [Nat.sub_mul, Nat.mul_comm (A/E) E]
    omega
  have hrem := Nat.mod_lt A hE
  symm
  apply Nat.div_eq_of_lt_le
  · rw [hex]
    omega
  · rw [Nat.add_mul, one_mul, hex]
    omega

theorem schedule {d e g p : ℕ} (hd : 1<d) (he : 0<e) (hed : e<d)
    (hg : 0<g) (hp : 0<p) (hm : 2^p % d=1) :
    let q := g*d
    let E := g*e
    let r := width q E
    r 0=1 ∧ r p=1 ∧ (∀ b≤p, 0<r b) ∧ (∀ b<p, r (b+1)≤2*r b) ∧
    ∃ h : (b : Fin p) → Fin (2*r b.val-r (b.val+1)) → Fin q → ℕ,
      (∀ b w, (∑ j, h b w j)=E) ∧
      ∀ j, (∑ b : Fin p, 2^(p-1-b.val)*∑ w, h b w j)=quota d e p := by
  let q := g*d
  let E := g*e
  let M := quota d e p
  let r := width q E
  have hq : 0<q := Nat.mul_pos hg (by omega)
  have he0 : 0<E := Nat.mul_pos hg he
  have heq : E<q := Nat.mul_lt_mul_of_pos_left hed hg
  have hM : q*M+E=2^p*E := quota_eq hm
  have hmass : (∑ _ : Fin q, M)=(2^p-1)*E := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
    rw [Nat.sub_one_mul]; omega
  have hpack := Pack p E q hp he0 (fun _ => M) hmass
  dsimp only at hpack
  let best := fun b : ℕ => 2^b-(∑ _ : Fin q, M/2^(p-b))/E
  have beq (b : ℕ) (hb : b≤p) : best b = r b := by
    have hqk : q*M+E=(2^(p-b))*(2^b*E) := by
      calc
        q*M+E = 2^p*E := hM
        _ = (2^(p-b)*2^b)*E := by rw [←pow_add, Nat.sub_add_cancel hb]
        _ = _ := Nat.mul_assoc _ _ _
    have hf := floor_quota hq heq (by positivity : 0<2^(p-b)) hqk
    simpa only [best,r,width, Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul,Nat.cast_id,hf] using (floor_width (q:=q) (z:=2^b) he0)
  have sh : r 0=1 ∧ r p=1 ∧ ∀ b<p, r (b+1)≤2*r b :=
    ⟨(beq 0 (by omega)).symm.trans hpack.2.1.1,(beq p le_rfl).symm.trans hpack.2.1.2.1,
      fun b hb => by rw [←beq (b+1) (by omega),←beq b hb.le]; exact hpack.2.1.2.2 b hb⟩
  have pos : ∀ b≤p, 0<r b := by
    intro b hb
    by_contra! hzero
    have vanish : ∀ k, b+k≤p → r (b+k)=0 := by
      intro k
      induction k with
      | zero => intro _; simpa using hzero
      | succ k ih =>
        intro hk
        have hstep := sh.2.2 (b+k) (by omega)
        rw [ih (by omega)] at hstep
        exact Nat.eq_zero_of_le_zero hstep
    have e0 := vanish (p-b) (by omega)
    rw [Nat.add_sub_of_le hb,sh.2.1] at e0
    omega
  exact ⟨sh.1,sh.2.1,pos,sh.2.2,(hpack.1 r sh).2 (fun b hb => (beq b hb).le)⟩

end PEqualNP.Outside.L_meta_29779.Block

namespace PEqualNP.Outside.L_meta_29779.Block

open Finset

section
variable {q N : ℕ}
variable (f : Fin q → Equiv.Perm (Fin N))

def row (j : Fin q) : Finset (Fin N × Fin N) :=
  univ.map ⟨fun x => (x,f j x), fun _ _ h => congrArg Prod.fst h⟩

@[simp] theorem mem_row (x y : Fin N) (j : Fin q) : (x,y) ∈ row f j ↔ f j x = y := by
  rw [row, mem_map]
  change (∃ a ∈ univ, (a,f j a) = (x,y)) ↔ _
  simp

@[simp] theorem card_row (j : Fin q) : (row f j).card = N := by simp [row]

def cost (B H : Fin N → Fin N → Bool) (D : Finset (Fin q)) :=
  (univ.filter (fun z : Fin N × Fin N => H z.1 z.2 ≠
    xor (B z.1 z.2) (decide (z.2 ∈ D.image (fun j => f j z.1))))).card

def changed (B H : Fin N → Fin N → Bool) :=
  univ.filter (fun z : Fin N × Fin N => H z.1 z.2 ≠ B z.1 z.2)

@[simp] theorem cost_empty (B H : Fin N → Fin N → Bool) :
    cost f B H ∅ = (changed B H).card := by simp [cost, changed]

theorem separateRows (hf : ∀ x, Function.Injective (fun j => f j x))
    {j k : Fin q} (hne : j ≠ k) : Disjoint (row f j) (row f k) := by
  rw [disjoint_left]
  rintro ⟨x,y⟩ h1 h2
  exact hne (hf x ((mem_row .. |>.mp h1).trans (mem_row .. |>.mp h2).symm))

theorem overlap (hf : ∀ x, Function.Injective (fun j => f j x)) (S : Finset (Fin N × Fin N))
    (D : Finset (Fin q)) :
    (S ∩ D.biUnion (row f)).card = ∑ j ∈ D, (S ∩ row f j).card := by
  rw [inter_biUnion, card_biUnion]
  intro j _ k _ hne
  exact (separateRows f hf hne).mono (inter_subset_right ..) (inter_subset_right ..)

theorem totalEdits (hf : ∀ x, Function.Injective (fun j => f j x)) (S : Finset (Fin N × Fin N)) :
    (∑ j, (S ∩ row f j).card) ≤ S.card := by
  rw [← overlap f hf]
  exact card_le_card (inter_subset_left ..)

theorem cost_id (hf : ∀ x, Function.Injective (fun j => f j x))
    (B H : Fin N → Fin N → Bool) (D : Finset (Fin q)) :
    cost f B H D + 2*(∑ j ∈ D, (changed B H ∩ row f j).card) =
      (changed B H).card + N*D.card := by
  let S := changed B H
  let U := D.biUnion (row f)
  have hU (x y) : (x,y) ∈ U ↔ y ∈ D.image (fun j => f j x) := by simp [U]
  have hcard : U.card = N*D.card := by
    rw [show U = D.biUnion (row f) from rfl, card_biUnion (fun _ _ _ _ h => separateRows f hf h)]
    simp [Nat.mul_comm]
  have hset : (univ.filter (fun z : Fin N × Fin N => H z.1 z.2 ≠
      xor (B z.1 z.2) (decide (z.2 ∈ D.image (fun j => f j z.1))))) =
      (S \ U) ∪ (U \ S) := by
    ext ⟨x,y⟩
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_sdiff, hU, S, changed]
    by_cases h : y ∈ D.image (fun j => f j x) <;> cases H x y <;> cases B x y <;> simp [h]
  have hd : Disjoint (S \ U) (U \ S) := by exact disjoint_left.mpr (fun _ hs hu => (mem_sdiff.mp hs).2 (mem_sdiff.mp hu).1)
  change _ + 2*(∑ j ∈ D, (S ∩ row f j).card) = S.card + _
  unfold cost
  rw [hset, card_union_of_disjoint hd, ← overlap f hf, ← hcard]
  have h₁ := card_sdiff_add_card_inter S U
  have h₂ := card_sdiff_add_card_inter U S
  rw [inter_comm U S] at h₂
  change _ + 2*(S ∩ U).card = _
  omega

def toggled (B : Fin N → Fin N → Bool) (S : Finset (Fin N × Fin N)) (x y : Fin N) :=
  xor (B x y) (decide ((x,y) ∈ S))

@[simp] theorem changed_toggled (B : Fin N → Fin N → Bool) (S : Finset (Fin N × Fin N)) :
    changed B (toggled B S) = S := by
  ext ⟨x,y⟩
  by_cases h : (x,y) ∈ S <;> cases e : B x y <;> simp [changed, toggled, e, h]

theorem editSet (hf : ∀ x, Function.Injective (fun j => f j x))
    (d : Fin q → ℕ) (hN : ∀ j, d j ≤ N) :
    ∃ S : Finset (Fin N × Fin N), S.card = ∑ j, d j ∧ ∀ j, (S ∩ row f j).card = d j := by
  classical
  have ex (j) : ∃ W ⊆ row f j, W.card = d j := exists_subset_card_eq (by simpa using hN j)
  choose W hsub hcard using ex
  refine ⟨univ.biUnion W, ?_, ?_⟩
  · rw [card_biUnion (fun j _ k _ h => (separateRows f hf h).mono (hsub j) (hsub k))]
    simp [hcard]
  · intro j
    suffices he : univ.biUnion W ∩ row f j = W j by rw [he,hcard]
    ext z
    simp only [mem_inter, mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨⟨k,hk⟩,hj⟩
      by_cases h : k=j
      · simpa [h] using hk
      · exact (disjoint_left.mp (separateRows f hf h) (hsub _ hk) hj).elim
    · intro h
      exact ⟨⟨j,h⟩, hsub _ h⟩
end

end PEqualNP.Outside.L_meta_29779.Block

namespace PEqualNP.Outside.L_meta_29779.Block

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def gateOK (g : Gate) := g.inputs.length ≤ 2 ∧
  (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))

def legal (N : ℕ) (C : Circuit) := ReadsBack (N+N) C ∧ C.output < N+N+C.size ∧
  ∀ g ∈ C.gates, gateOK g

def table {N : ℕ} (C : Circuit) (x y : Fin N) := C.eval (oneEach x y)

def fits {N q : ℕ} (f : Fin q → Equiv.Perm (Fin N)) (E : ℕ) (base C : Circuit) :=
  legal N C ∧ C.gates.take base.size = base.gates ∧ C.size ≤ base.size+2*E+3 ∧
    cost f (table base) (table C) ∅ ≤ E

def atBit {N : ℕ} (C : Circuit) (w : ℕ) (F : Fin N → Fin N → Bool) :=
  w < N+N+C.size ∧ ∀ x y, (C.wires (oneEach x y)).getD w false = F x y

theorem wireLength (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length+C.size := by
  rcases C with ⟨gs,o⟩
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires, Circuit.size]
  | append_singleton gs g ih => simp [Circuit.wires, Circuit.size, List.foldl_append] at ih ⊢; omega

theorem carryBit {N : ℕ} {A B : Circuit} (hab : A.gates <+: B.gates)
    {w : ℕ} {F : Fin N → Fin N → Bool} (h : atBit A w F) : atBit B w F := by
  obtain ⟨s,hs⟩ := hab
  have hle : A.size ≤ B.size := by simp [Circuit.size,← hs]
  refine ⟨by have := h.1; omega, ?_⟩
  intro x y
  rw [← h.2 x y]
  let v := A.wires (oneEach x y)
  have hlen : w < v.length := by simpa [v,wireLength,oneEach] using h.1
  have prop (s : List Gate) : ∀ (l : List Bool), w < l.length →
      (s.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) l).getD w false
      = l.getD w false := by
    induction s with
    | nil => simp
    | cons g s ih =>
      intro l hl
      rw [List.foldl_cons, ih _ (by simp; omega), List.getD_eq_getElem?_getD,
        List.getElem?_append_left hl, ← List.getD_eq_getElem?_getD]
  unfold Circuit.wires
  rw [← hs, List.foldl_append]
  exact prop s v hlen

def snoc (N : ℕ) (C : Circuit) (g : Gate) : Circuit := ⟨C.gates ++ [g], N+N+C.size⟩

theorem snocLeg {N : ℕ} {C : Circuit} (hc : legal N C) (g : Gate) (hg : gateOK g)
    (hi : ∀ i ∈ g.inputs, i < N+N+C.size) : legal N (snoc N C g) := by
  refine ⟨?_,by simp [snoc,Circuit.size],?_⟩
  · intro j hj i h
    simp only [snoc, List.length_append, List.length_singleton] at hj
    by_cases he : j < C.gates.length
    · apply hc.1 j he i
      simpa [gateAt,snoc,List.getD_eq_getElem?_getD,List.getElem?_append_left he] using h
    · have e : j = C.gates.length := by omega
      subst j
      apply hi
      simpa [gateAt,snoc,List.getD_eq_getElem?_getD] using h
  · intro a ha
    simp only [snoc,List.mem_append,List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact hc.2.2 a ha
    · exact hg

theorem snocEval {N : ℕ} (C : Circuit) (g : Gate) (x y : Fin N) :
    table (snoc N C g) x y =
      g.op.eval (g.inputs.map fun i => (C.wires (oneEach x y)).getD i false) := by
  have hlen : (C.wires (oneEach x y)).length = N+N+C.size := by simp [wireLength,oneEach]
  unfold table Circuit.eval
  change (((C.gates++[g]).foldl _ (oneEach x y)).getD (N+N+C.size) false) = _
  rw [← hlen, List.foldl_append]
  change ((C.wires (oneEach x y)) ++ [_]).getD (C.wires (oneEach x y)).length false = _
  simp [List.getD_eq_getElem?_getD, Circuit.wires]

theorem endBit {N : ℕ} {C : Circuit} (hc : legal N C) : atBit C C.output (@table N C) :=
  ⟨hc.2.1, by intros; rfl⟩

theorem addBinary {N : ℕ} {C : Circuit} (hc : legal N C) {a b : ℕ}
    {A B : Fin N → Fin N → Bool} (ha : atBit C a A) (hb : atBit C b B) (isAnd : Bool) :
    ∃ K : Circuit, C.gates <+: K.gates ∧ legal N K ∧ K.size = C.size+1 ∧
      atBit K K.output (fun x y => if isAnd then A x y && B x y else A x y || B x y) := by
  let g : Gate := ⟨if isAnd then .and else .or,[a,b]⟩
  have hgood := snocLeg hc g (by cases isAnd <;> simp [g,gateOK])
    (by intro i hi; simp [g] at hi; rcases hi with rfl | rfl; exact ha.1; exact hb.1)
  refine ⟨snoc N C g, ⟨[g],rfl⟩, hgood, by simp [snoc,Circuit.size], hgood.2.1, ?_⟩
  intro x y
  change table (snoc N C g) x y = _
  rw [snocEval]
  cases isAnd <;> simp [-List.getD_eq_getElem?_getD,g,GateOp.eval,ha.2 x y,hb.2 x y]

theorem addNot {N : ℕ} {C : Circuit} (hc : legal N C) {a : ℕ} {A : Fin N → Fin N → Bool}
    (ha : atBit C a A) : ∃ K : Circuit, C.gates <+: K.gates ∧ legal N K ∧ K.size = C.size+1 ∧
      atBit K K.output (fun x y => !(A x y)) := by
  let g : Gate := ⟨.not,[a]⟩
  have hgood := snocLeg hc g (by simp [g,gateOK])
    (by intro i hi; simp [g] at hi; simpa [hi] using ha.1)
  refine ⟨snoc N C g,⟨[g],rfl⟩,hgood, by simp [snoc,Circuit.size],hgood.2.1,?_⟩
  intro x y
  change table (snoc N C g) x y = _
  simp [-List.getD_eq_getElem?_getD,snocEval,g,GateOp.eval,ha.2 x y]

theorem addCell {N : ℕ} {C : Circuit} (hc : legal N C) (p : Fin N × Fin N) :
    ∃ K : Circuit, C.gates <+: K.gates ∧ legal N K ∧ K.size = C.size+1 ∧
      atBit K K.output (fun x y => decide ((x,y)=p)) := by
  let O : Circuit := ⟨[],0⟩
  have hp : O.gates <+: C.gates := ⟨C.gates,rfl⟩
  have h1 : atBit O p.1.val (fun x _ => decide (p.1=x)) := by
    refine ⟨by have := p.1.isLt; dsimp [O,Circuit.size]; omega,?_⟩
    intro x y
    simp [O,Circuit.wires,oneEach,List.getD_eq_getElem?_getD,List.getElem?_append_left,p.1.isLt]
  have h2 : atBit O (N+p.2.val) (fun _ y => decide (p.2=y)) := by
    refine ⟨by have := p.2.isLt; dsimp [O,Circuit.size]; omega,?_⟩
    intro x y
    simp [O,Circuit.wires,oneEach,List.getD_eq_getElem?_getD]
  obtain ⟨K,he,hg,hl,hb⟩ := addBinary hc (carryBit hp h1) (carryBit hp h2) true
  exact ⟨K,he,hg,hl,hb.1,fun x y => by simpa [Prod.ext_iff, eq_comm] using hb.2 x y⟩

theorem addCells {N : ℕ} {C : Circuit} (hc : legal N C) (S : Finset (Fin N × Fin N)) (hs : S.Nonempty) :
    ∃ K : Circuit, C.gates <+: K.gates ∧ legal N K ∧ K.size+1 = C.size+2*S.card ∧
      atBit K K.output (fun x y => decide ((x,y)∈S)) := by
  induction S using Finset.induction_on with
  | empty => simp at hs
  | @insert a S ha ih =>
    rw [Finset.card_insert_of_notMem ha]
    rcases S.eq_empty_or_nonempty with rfl | hne
    · obtain ⟨K,he,hg,hl,hb⟩ := addCell hc a
      exact ⟨K,he,hg,by simp [hl],hb.1,fun x y => by simpa using hb.2 x y⟩
    · obtain ⟨K,he,hg,hl,hb⟩ := ih hne
      obtain ⟨A,hA,hgA,hlA,hbA⟩ := addCell hg a
      obtain ⟨B,hB,hgB,hlB,hbB⟩ := addBinary hgA hbA (carryBit hA hb) false
      exact ⟨B,(he.trans hA).trans hB,hgB,by omega,hbB.1,fun x y => by simpa using hbB.2 x y⟩

theorem compileSet {q N E : ℕ} (f : Fin q → Equiv.Perm (Fin N)) {base : Circuit} (hbase : legal N base)
    (S : Finset (Fin N × Fin N)) (hE : S.card = E) (he : 0 < E) :
    ∃ C, fits f E base C ∧ @table N C = toggled (table base) S := by
  obtain ⟨A,hA,gA,lA,bA⟩ := addCells hbase S (Finset.card_pos.mp (hE ▸ he))
  have bb := carryBit hA (endBit hbase)
  obtain ⟨B,hB,gB,lB,bB⟩ := addBinary gA bb bA false
  obtain ⟨K,hK,gK,lK,bK⟩ := addBinary gB (carryBit hB bb) (carryBit hB bA) true
  obtain ⟨L,hL,gL,lL,bL⟩ := addNot gK bK
  obtain ⟨M,hM,gM,lM,bM⟩ := addBinary gL (carryBit (hK.trans hL) bB) bL true
  have eq : @table N M = toggled (table base) S := by
    funext x y
    change (M.wires _).getD M.output false = _
    rw [bM.2 x y]
    change ((_ || _) && !(_ && _)) = xor _ _
    cases table base x y <;> cases decide ((x,y)∈S) <;> rfl
  have htake := (((hA.trans hB).trans hK).trans hL).trans hM
  obtain ⟨tail,htail⟩ := htake
  refine ⟨M, ⟨gM,by simp [← htail,Circuit.size],by omega,?_⟩,eq⟩
  rw [eq,cost_empty,changed_toggled,hE]

end PEqualNP.Outside.L_meta_29779.Block

namespace PEqualNP.Outside.L_meta_29779.Block

open PEqualNP.CircuitLowerBounds Finset

theorem compile_histogram {q N E : ℕ} (he : 0<E) (hen : E≤N)
    (f : Fin q → Equiv.Perm (Fin N)) (hf : ∀ x, Function.Injective (fun j => f j x))
    (base : Circuit) (hbase : legal N base) (v : Fin q → ℕ) (hv : (∑ j, v j)=E) :
    ∃ C, fits f E base C ∧ ∀ D : Finset (Fin q),
      (cost f (table base) (table C) D : ℝ) =
        (E : ℝ) + (N : ℝ)*D.card - 2 * ∑ j ∈ D, (v j : ℝ) := by
  classical
  have lim (j) : v j ≤ N := calc
    v j ≤ ∑ k, v k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ j)
    _ ≤ N := hv ▸ hen
  obtain ⟨S,hSc,hSj⟩ := editSet f hf v lim
  obtain ⟨C,hfit,htable⟩ := compileSet f hbase S (hSc.trans hv) he
  refine ⟨C,hfit,?_⟩
  intro D
  have hh := cost_id f hf (table base) (table C) D
  rw [htable, changed_toggled] at hh
  simp only [hSj, hSc, hv] at hh
  have h' : (cost f (table base) (toggled (table base) S) D : ℝ)
        + 2 * ∑ j ∈ D, (v j:ℝ) = E+(N:ℝ)*D.card := by exact_mod_cast hh
  rw [htable]
  linarith

end PEqualNP.Outside.L_meta_29779.Block

namespace PEqualNP.Outside.L_meta_29779.Risk
open Finset

noncomputable def pick (r : ℕ → ℕ) (pay : ℕ → ℕ → ℝ)
    (v : (b : ℕ) → Fin (r b) → ℝ) (b k : ℕ) : ℝ :=
  if h : k < r (b+1) then v (b+1) ⟨k,h⟩ else pay b (k-r (b+1))

private noncomputable def splice (m : ℕ) (u pay : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k < m then u k else pay (k-m)

private noncomputable def sweep (r : ℕ → ℕ) (pay : ℕ → ℕ → ℝ) (root : ℝ) :
    ℕ → ℕ → ℕ → ℝ
  | 0, _, _ => root
  | k+1, b, i =>
    let next := splice (r (b+1)) (sweep r pay root k (b+1)) (pay b)
    (next (2*i) + next (2*i+1))/2

private theorem double_sum (f : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range (2*n), f i = ∑ i ∈ range n, (f (2*i) + f (2*i+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega, sum_range_succ, sum_range_succ, ih, sum_range_succ]
    simp only [add_assoc]

private theorem splice_sum (n m : ℕ) (hm : m ≤ n) (u pay : ℕ → ℝ) :
    ∑ i ∈ range n, splice m u pay i =
      (∑ i ∈ range m, u i) + ∑ i ∈ range (n-m), pay i := by
  calc
    _ = ∑ i ∈ range (m + (n-m)), splice m u pay i := by rw [Nat.add_sub_of_le hm]
    _ = _ := by
      rw [sum_range_add]
      apply congrArg₂ (· + ·)
      · exact sum_congr rfl fun i hi => by simp [splice, mem_range.mp hi]
      · exact sum_congr rfl fun i _ => by simp [splice]

private theorem telescope (p : ℕ) (a e : ℕ → ℝ)
    (step : ∀ b < p, 2*a b = a (b+1) + e b) :
    (2:ℝ)^p * a 0 = a p + ∑ b ∈ range p, 2^(p-1-b) * e b := by
  suffices gen : ∀ k ≤ p, (2:ℝ)^k * a 0 = a k + ∑ b ∈ range k, 2^(k-1-b) * e b from
    gen p le_rfl
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    intro hkp
    have hx := ih (by omega)
    have hy := step k (by omega)
    have scale : (∑ b ∈ range k, (2:ℝ)^(k+1-1-b) * e b) =
        2 * ∑ b ∈ range k, (2:ℝ)^(k-1-b) * e b := by
      rw [mul_sum]
      refine sum_congr rfl fun b hb => ?_
      have hb' := mem_range.mp hb
      rw [show k+1-1-b = (k-1-b)+1 by omega, pow_succ]
      ring
    rw [sum_range_succ, scale, show k+1-1-k = 0 by omega, pow_zero, one_mul, pow_succ]
    linear_combination 2*hx + hy

theorem periodicRisk (p : ℕ) (hp : 0 < p) (r : ℕ → ℕ) (h0 : r 0 = 1)
    (hP : r p = 1) (hcap : ∀ b < p, r (b+1) ≤ 2*r b) (pay : ℕ → ℕ → ℝ) :
    ∃ v : (b : ℕ) → Fin (r b) → ℝ,
      (∀ (i : Fin (r p)) (j : Fin (r 0)), v p i = v 0 j) ∧
      (∀ b < p, ∀ i : Fin (r b), 2*v b i =
        pick r pay v b (2*i.val) + pick r pay v b (2*i.val+1)) ∧
      ∀ i : Fin (r 0), ((2:ℝ)^p-1)*v 0 i =
        ∑ b ∈ range p, 2^(p-1-b) * ∑ k ∈ range (2*r b-r (b+1)), pay b k := by
  let e (b : ℕ) := ∑ k ∈ range (2*r b-r (b+1)), pay b k
  let weighted : ℝ := ∑ b ∈ range p, 2^(p-1-b)*e b
  let root := weighted / ((2:ℝ)^p-1)
  let u (b i : ℕ) := sweep r pay root (p-b) b i
  let a (b : ℕ) := ∑ i ∈ range (r b), u b i
  have step (b : ℕ) (hb : b < p) (i : ℕ) :
      2*u b i = splice (r (b+1)) (u (b+1)) (pay b) (2*i) +
        splice (r (b+1)) (u (b+1)) (pay b) (2*i+1) := by
    dsimp only [u]
    rw [show p-b = p-(b+1)+1 by omega, sweep]
    ring
  have massStep (b : ℕ) (hb : b < p) : 2*a b = a (b+1) + e b := by
    dsimp only [a,e]
    rw [mul_sum]
    simp_rw [step b hb]
    rw [← double_sum, splice_sum _ _ (hcap b hb)]
  have hsum := telescope p a e massStep
  have atop : a 0 = u 0 0 := by simp [a, h0]
  have alast : a p = root := by simp [a, u, hP, sweep]
  change (2:ℝ)^p * a 0 = a p + weighted at hsum
  rw [atop, alast] at hsum
  have hbig : 1 < (2:ℝ)^p := one_lt_pow₀ (by norm_num) hp.ne'
  have hroot : ((2:ℝ)^p-1)*root = weighted :=
    mul_div_cancel₀ _ (sub_ne_zero.mpr hbig.ne')
  have hub : u 0 0 = root := by
    apply mul_left_cancel₀ (show (2:ℝ)^p ≠ 0 by positivity)
    linear_combination hsum - hroot
  have hz (j : Fin (r 0)) : j.val = 0 := by have h := j.isLt; omega
  refine ⟨fun b i => u b i.val, ?_, ?_, ?_⟩
  · intro i j
    change u p i.val = u 0 j.val
    rw [hz j, hub]
    simp [u, sweep]
  · intro b hb i
    rw [step b hb]
    dsimp only [pick, splice]
    split <;> split <;> simp_all
  · intro i
    change ((2:ℝ)^p-1)*u 0 i.val = weighted
    rw [hz i, hub]
    exact hroot

theorem exitWeight (p : ℕ) (r : ℕ → ℕ) (h0 : r 0 = 1)
    (hP : r p = 1) (hcap : ∀ b < p, r (b+1) ≤ 2*r b) :
    (∑ b ∈ range p, (2:ℝ)^(p-1-b) * ((2*r b-r (b+1) : ℕ) : ℝ)) = (2:ℝ)^p-1 := by
  have step (b : ℕ) (hb : b < p) :
      (2:ℝ)*(r b : ℝ) = (r (b+1):ℝ) + ((2*r b-r (b+1):ℕ):ℝ) := by
    rw [Nat.cast_sub (hcap b hb), Nat.cast_mul, Nat.cast_ofNat]
    ring
  have h := telescope p (fun b => (r b:ℝ)) (fun b => ((2*r b-r (b+1):ℕ):ℝ)) step
  simp only [h0,hP,Nat.cast_one,mul_one] at h
  linarith

end PEqualNP.Outside.L_meta_29779.Risk

namespace PEqualNP.Outside.L_meta_29779.Risk
open Finset

private noncomputable def weighted (p : ℕ) (r : ℕ → ℕ) : (ℕ → ℕ → ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∑ b ∈ range p, 2^(p-1-b) * ∑ k ∈ range (2*r b-r (b+1)), f b k
  map_add' f g := by simp only [Pi.add_apply, sum_add_distrib, mul_add]
  map_smul' a f := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [← mul_sum, mul_left_comm (a := (2:ℝ)^_) (b := a), ← mul_sum]

theorem weighted_payoff {J : Type*} (p : ℕ) (r : ℕ → ℕ)
    (h0 : r 0 = 1) (hP : r p = 1) (hcap : ∀ b < p, r (b+1) ≤ 2*r b)
    (D : Finset J) (K M : ℝ) (pay : ℕ → ℕ → ℝ) (v : ℕ → ℕ → J → ℝ)
    (hpay : ∀ b < p, ∀ k < 2*r b-r (b+1), pay b k = K-2*∑ j ∈ D, v b k j)
    (hm : ∀ j ∈ D, (∑ b ∈ range p, (2:ℝ)^(p-1-b) *
      ∑ k ∈ range (2*r b-r (b+1)), v b k j) = M) :
    (∑ b ∈ range p, (2:ℝ)^(p-1-b) * ∑ k ∈ range (2*r b-r (b+1)), pay b k)
      = ((2:ℝ)^p-1)*K - 2*(D.card:ℝ)*M := by
  classical
  let u (j : J) (b k : ℕ) := v b k j
  let c : ℕ → ℕ → ℝ := fun _ _ => K
  have same : weighted p r pay = weighted p r (c - (2:ℝ) • ∑ j ∈ D, u j) := by
    change (∑ b ∈ range p, (2:ℝ)^(p-1-b) * ∑ k ∈ range (2*r b-r (b+1)), pay b k) =
      ∑ b ∈ range p, (2:ℝ)^(p-1-b) * ∑ k ∈ range (2*r b-r (b+1)),
        (c - (2:ℝ) • ∑ j ∈ D, u j) b k
    apply sum_congr rfl
    intro b hb
    apply congrArg ((2:ℝ)^(p-1-b)*·)
    apply sum_congr rfl
    intro k hk
    simpa [c, u, Finset.sum_apply] using hpay b (mem_range.mp hb) k (mem_range.mp hk)
  have const : weighted p r c = ((2:ℝ)^p-1)*K := by
    change (∑ b ∈ range p, (2:ℝ)^(p-1-b) * ∑ _k ∈ range (2*r b-r (b+1)), K) = _
    rw [← exitWeight p r h0 hP hcap, Finset.sum_mul]
    simp [mul_assoc]
  change weighted p r pay = _
  rw [same, map_sub, map_smul, map_sum, const]
  have mass : (∑ j ∈ D, weighted p r (u j)) = (D.card:ℝ)*M := by
    calc
      _ = ∑ _j ∈ D, M := sum_congr rfl fun j hj => hm j hj
      _ = _ := by simp
  rw [mass, smul_eq_mul]
  ring

theorem optimalRootValue (p q N E t M : ℕ) (Z : ℝ)
    (hp : 0 < p) (hqN : q ≤ N) (hE : E < q) (ht : q < 2*t) (htq : t < q)
    (hm : M*q = (2^p-1)*E)
    (hZ : ((2:ℝ)^p-1)*Z =
      ((2:ℝ)^p-1)*((E:ℝ)+(N:ℝ)*t)-2*(t:ℝ)*M) :
    Z = ((q*N*t-(2*t-q)*E : ℕ) : ℝ) / (q:ℝ) := by
  have hq : 0 < q := by omega
  have ex : 2*t-q ≤ t := by omega
  have hpaid : (2*t-q)*E ≤ q*N*t := calc
    _ ≤ t*N := Nat.mul_le_mul ex (by omega)
    _ ≤ _ := by rw [mul_comm t N, mul_assoc]; exact Nat.le_mul_of_pos_left _ hq
  have hmR := congrArg (fun v : ℕ => (v : ℝ)) hm
  push_cast [Nat.cast_sub Nat.one_le_two_pow] at hmR
  have hden : (2:ℝ)^p - 1 ≠ 0 := sub_ne_zero.mpr (one_lt_pow₀ (by norm_num) hp.ne').ne'
  apply (eq_div_iff (by exact_mod_cast hq.ne')).mpr
  rw [Nat.cast_sub hpaid]
  push_cast [Nat.cast_sub ht.le]
  apply mul_left_cancel₀ hden
  linear_combination (q:ℝ)*hZ - (2*(t:ℝ))*hmR

end PEqualNP.Outside.L_meta_29779.Risk

namespace PEqualNP.Outside.L_meta_29779.Block

open Finset PEqualNP.CircuitLowerBounds

theorem scheduled_actions {d e g p N t : ℕ} (hd : 1<d) (he : 0<e) (hed : e<d)
    (hg : 0<g) (hp : 0<p) (hm : 2^p % d=1)
    (hqN : g*d≤N) (ht : g*d<2*t) (htq : t<g*d)
    (f : Fin (g*d) → Equiv.Perm (Fin N)) (hf : ∀ x, Function.Injective (fun j => f j x))
    (base : Circuit) (hbase : legal N base) :
    let q := g*d
    let E := g*e
    let r := width q E
    r 0=1 ∧ r p=1 ∧ (∀ b≤p, 0<r b) ∧ (∀ b<p, r (b+1)≤2*r b) ∧
    ∃ A : ℕ → ℕ → Circuit, (∀ b k, fits f E base (A b k)) ∧
      ∀ D : Finset (Fin q), D.card=t →
      (∑ b ∈ range p, (2:ℝ)^(p-1-b) * ∑ k ∈ range (2*r b-r (b+1)),
          (cost f (table base) (table (A b k)) D : ℝ))
        = ((2:ℝ)^p-1)*(((q*N*t-(2*t-q)*E : ℕ) : ℝ)/(q:ℝ)) := by
  classical
  let q := g*d
  let E := g*e
  let r := width q E
  let M := quota d e p
  have hq : 0<q := Nat.mul_pos hg (by omega)
  have hE : 0<E := Nat.mul_pos hg he
  have hEq : E<q := Nat.mul_lt_mul_of_pos_left hed hg
  obtain ⟨h0,hP,hpos,hcap,h,hmass,hsum⟩ := schedule hd he hed hg hp hm
  let v (b k : ℕ) (j : Fin q) : ℕ :=
    if bnd : b<p then
      if lmt : k<2*r b-r (b+1) then h ⟨b,bnd⟩ ⟨k,lmt⟩ j else if j=⟨0,hq⟩ then E else 0
    else if j=⟨0,hq⟩ then E else 0
  have vmass (b k) : (∑ j, v b k j)=E := by
    by_cases bnd : b<p
    · by_cases lmt : k<2*r b-r (b+1)
      · simpa only [v,dite_eq_left bnd,dite_eq_left lmt] using hmass ⟨b,bnd⟩ ⟨k,lmt⟩
      · simp [v,bnd,lmt]
    · simp [v,bnd]
  choose A hfit hcost using fun b k => compile_histogram hE (hEq.le.trans hqN) f hf base hbase (v b k) (vmass b k)
  refine ⟨h0,hP,hpos,hcap,A,hfit,?_⟩
  intro D hD
  let W := ∑ b ∈ range p, (2:ℝ)^(p-1-b)*∑ k ∈ range (2*r b-r (b+1)), (cost f (table base) (table (A b k)) D:ℝ)
  let den := (2:ℝ)^p-1
  have hden : den≠0 := sub_ne_zero.mpr (one_lt_pow₀ (by norm_num) hp.ne').ne'
  have vt (j : Fin q) : (∑ b ∈ range p, 2^(p-1-b)*∑ k ∈ range (2*r b-r (b+1)), v b k j)=M := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine (Finset.sum_congr rfl (fun b hb => ?_)).trans (hsum j)
    apply congrArg ((2^(p-1-b.val)) * ·)
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro w hw
    simp [v,b.isLt,w.isLt]
  have pay := Risk.weighted_payoff p r h0 hP hcap D ((E:ℝ)+(N:ℝ)*t) (M:ℝ)
    (fun b k => (cost f (table base) (table (A b k)) D:ℝ)) (fun b k j => (v b k j:ℝ))
    (fun b _ k _ => by simpa [hD] using hcost b k D)
    (fun j _ => by exact_mod_cast vt j)
  have hquota : M*q=(2^p-1)*E := by
    have hs : q*M+E=2^p*E := quota_eq hm
    rw [Nat.mul_comm M q,Nat.sub_one_mul]
    omega
  have norm : den*(W/den)=W := by field_simp
  have hz := Risk.optimalRootValue p q N E t M (W/den) hp hqN hEq ht htq hquota
    (norm.trans (by simpa only [hD] using pay))
  change W=den*_
  rw [←hz,norm]

end PEqualNP.Outside.L_meta_29779.Block

namespace PEqualNP.Outside.L_meta_29779.Graph

def bit (x : Bool) : ℕ := if x then 1 else 0

def doubleEquiv (n : ℕ) : Bool × Fin n ≃ Fin (2*n) where
  toFun := fun ⟨t,i⟩ => ⟨2*i.val + bit t, by have := i.isLt; cases t <;> simp [bit] <;> omega⟩
  invFun := fun j => (decide (j.val % 2=1), ⟨j.val / 2, by have := j.isLt; omega⟩)
  left_inv := by rintro ⟨t,i⟩; cases t <;> simp [bit, Fin.ext_iff] <;> omega
  right_inv := by intro j; apply Fin.ext; simp only; simp [bit]; split_ifs <;> omega

noncomputable def enc : (b : ℕ) → (Fin b → Bool) ≃ Fin (2^b)
  | 0 => (Equiv.ofUnique (Fin 0 → Bool) (Fin 1)).trans (finCongr (by decide))
  | b+1 => ((Fin.snocEquiv fun _ : Fin (b+1) => Bool).symm.trans
      ((Equiv.refl Bool).prodCongr (enc b))).trans
        ((doubleEquiv (2^b)).trans (finCongr (by rw [pow_succ'])))

theorem enc_succ {b : ℕ} (w : Fin (b+1) → Bool) : (enc _ w).val =
    2*(enc _ (Fin.init w)).val + bit (w (Fin.last b)) := rfl

abbrev Node (p : ℕ) (r : ℕ → ℕ) := (b : Fin p) × Fin (r b.val)
abbrev size (p : ℕ) (r : ℕ → ℕ) := ∑ b ∈ Finset.range p, r b

noncomputable def pack (p : ℕ) (r : ℕ → ℕ) : Node p r ≃ Fin (size p r) :=
  Fintype.equivFinOfCardEq (by simp [Node, size, Fin.sum_univ_eq_sum_range])

noncomputable def atPhase {p : ℕ} (r : ℕ → ℕ) (pos : ∀ b, 0 < r b) (b : Fin p)
    (i : ℕ) : Fin (size p r) := pack p r ⟨b, ⟨i % r b.val, Nat.mod_lt _ (pos _)⟩⟩

noncomputable def st {p : ℕ} (hp : 0 < p) (r : ℕ → ℕ) (pos : ∀ b, 0 < r b)
    (b i : ℕ) : Fin (size p r) := atPhase r pos ⟨b % p, Nat.mod_lt _ hp⟩ i

theorem st_congr {p : ℕ} (hp : 0 < p) (r : ℕ → ℕ) (pos : ∀ b, 0 < r b)
    {b c : ℕ} (h : b % p=c % p) (i : ℕ) : st hp r pos b i = st hp r pos c i :=
  congrArg (fun a : Fin p => atPhase r pos a i) (Fin.ext h)

theorem unpack_st {p : ℕ} (hp : 0 < p) (r : ℕ → ℕ) (pos : ∀ b, 0 < r b)
    (b i : ℕ) : (pack p r).symm (st hp r pos b i) =
      ⟨⟨b % p, Nat.mod_lt _ hp⟩, ⟨i % r (b % p), Nat.mod_lt _ (pos _)⟩⟩ :=
  (pack p r).symm_apply_apply _

noncomputable def next {p : ℕ} (hp : 0 < p) (r : ℕ → ℕ) (pos : ∀ b, 0 < r b)
    (u : Fin (size p r)) (t : Bool) :=
  let a := (pack p r).symm u
  let k := 2*a.2.val + bit t
  if k < r (a.1.val+1) then some (st hp r pos (a.1.val+1) k) else none

theorem resucc {p : ℕ} (b : ℕ) : (b % p+1) % p = (b+1) % p := by
  exact Nat.mod_add_mod _ _ _

theorem next_st {p : ℕ} (hp : 0 < p) (r : ℕ → ℕ) (pos : ∀ b, 0 < r b)
    (per : ∀ b, r (b % p)=r b) (b i : ℕ) (hi : i < r b) (t : Bool) :
    next hp r pos (st hp r pos b i) t =
    if 2*i+bit t < r (b+1) then some (st hp r pos (b+1) (2*i+bit t)) else none := by
  have ph := congrArg (fun a : Node p r => a.1.val) (unpack_st hp r pos b i)
  have ix := congrArg (fun a : Node p r => a.2.val) (unpack_st hp r pos b i)
  change ((pack p r).symm (st hp r pos b i)).1.val=b % p at ph
  change ((pack p r).symm (st hp r pos b i)).2.val=i % r (b % p) at ix
  rw [per, Nat.mod_eq_of_lt hi] at ix
  have hr : r (b % p+1) = r (b+1) := by rw [← per (b % p+1), resucc, per]
  unfold next
  dsimp only
  rw [ix, ph, hr, st_congr hp r pos (resucc b)]

def run {s : ℕ} (z : Fin s) (n : Fin s → Bool → Option (Fin s)) (b : ℕ)
    (w : Fin b → Bool) := (List.ofFn w).foldl
      (fun (x : Option (Fin s)) (t : Bool) => x.bind (fun i => n i t)) (some z)

theorem run_succ {s b : ℕ} (z : Fin s) (n : Fin s → Bool → Option (Fin s)) (w : Fin (b+1) → Bool) :
    run z n (b+1) w = (run z n b (Fin.init w)).bind (fun i => n i (w (Fin.last b))) := by
  unfold run
  rw [List.ofFn_succ' w, List.concat_eq_append, List.foldl_append]
  rfl

theorem run_eq {p : ℕ} (hp : 0 < p) (r : ℕ → ℕ) (pos : ∀ b, 0 < r b)
    (per : ∀ b, r (b % p)=r b) (cap : ∀ b, r (b+1) ≤ 2*r b) (b : ℕ) (w : Fin b → Bool) :
    run (st hp r pos 0 0) (next hp r pos) b w =
    if (enc b w).val < r b then some (st hp r pos b (enc b w).val) else none := by
  induction b with
  | zero => have hz : (enc 0 w).val=0 := by have := (enc 0 w).isLt; simpa using this
            simp [run, hz, pos]
  | succ b ih =>
    rw [run_succ, ih, enc_succ]
    split_ifs with h h' h'
    · simpa [next_st hp r pos per _ _ h, h']
    · simpa [next_st hp r pos per _ _ h, h']
    · exfalso; have := cap b; omega
    · rfl

theorem size_le_bits (r : ℕ → ℕ) (h0 : r 0=1) (cap : ∀ b, r (b+1) ≤ 2*r b) (b : ℕ) :
    r b ≤ 2^b := by induction b with
    | zero => simp [h0]
    | succ b ih => rw [pow_succ']; exact (cap b).trans (Nat.mul_le_mul_left _ ih)

theorem card_alive {p : ℕ} (hp : 0 < p) (r : ℕ → ℕ) (pos : ∀ b, 0 < r b) (h0 : r 0=1)
    (per : ∀ b, r (b % p)=r b) (cap : ∀ b, r (b+1) ≤ 2*r b) (b : ℕ) :
    (Finset.univ.filter (fun w : Fin b → Bool => (run (st hp r pos 0 0) (next hp r pos) b w).isSome)).card = r b := by
  classical
  simp only [run_eq hp r pos per cap]
  have hh : ∀ w : Fin b → Bool, (if (enc b w).val < r b then some (st hp r pos b (enc b w).val) else none).isSome = true ↔ (enc b w).val < r b := by
    intro w; split_ifs <;> simp_all
  simp_rw [hh]
  let emb : Fin (r b) ↪ (Fin b → Bool) :=
    (Fin.castLEEmb (size_le_bits r h0 cap b)).trans (enc b).symm.toEmbedding
  have set_eq : Finset.univ.filter (fun w : Fin b → Bool => (enc b w).val < r b) = Finset.univ.map emb := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro h
      exact ⟨⟨(enc b w).val,h⟩, (enc b).symm_apply_apply w⟩
    · rintro ⟨i,_,rfl⟩
      simpa [emb] using i.isLt
  simp [set_eq]

theorem return_root {p : ℕ} (hp : 0 < p) (r : ℕ → ℕ) (pos : ∀ b, 0 < r b) (h0 : r 0=1)
    (per : ∀ b, r (b % p)=r b) (cap : ∀ b, r (b+1) ≤ 2*r b) (w : Fin p → Bool)
    (h : (run (st hp r pos 0 0) (next hp r pos) p w).isSome = true) :
    run (st hp r pos 0 0) (next hp r pos) p w = some (st hp r pos 0 0) := by
  rw [run_eq hp r pos per cap] at h ⊢
  split_ifs with hl
  · have hr := per p
    simp [h0] at hr
    have : (enc p w).val = 0 := by omega
    rw [this, st_congr hp r pos (show p % p = 0 % p by simp) 0]
  · simp [hl] at h

theorem st_at {p : ℕ} (hp : 0 < p) (r : ℕ → ℕ) (pos : ∀ b, 0 < r b)
    (b : Fin p) (i : Fin (r b.val)) : st hp r pos b.val i.val = pack p r ⟨b,i⟩ := by
  calc _ = atPhase r pos b i.val := congrArg (fun a : Fin p => atPhase r pos a i.val) (Fin.ext (Nat.mod_eq_of_lt b.isLt))
       _ = _ := by simp [atPhase, Nat.mod_eq_of_lt i.isLt]

theorem absorbs {p : ℕ} (hp : 0 < p) (r : ℕ → ℕ) (pos : ∀ b, 0 < r b) (hp1 : r p=1) :
    ∃ c : Fin (size p r) → Bool, ∀ i : Fin (size p r),
    (fun x : Option (Fin (size p r)) => x.bind (fun j => next hp r pos j (c j)))^[size p r]
      (some i) = none := by
  classical
  refine ⟨fun _ => true, ?_⟩
  let F := fun x : Option (Fin (size p r)) => x.bind (fun i => next hp r pos i true)
  have fixed (k : ℕ) : F^[k] none = none := by
    induction k with | zero => rfl | succ k ih => rw [Function.iterate_succ_apply]; exact ih
  have inc (i j : Fin (size p r)) (h : next hp r pos i true = some j) :
      ((pack p r).symm i).1.val < ((pack p r).symm j).1.val := by
    let a := (pack p r).symm i
    change (if 2*a.2.val + bit true < r (a.1.val+1) then some _ else none) = some j at h
    split_ifs at h with H
    · have lt : a.1.val+1 < p := by
        have := a.1.isLt
        by_contra! hh
        have eq : a.1.val+1=p := by omega
        rw [eq, hp1] at H
        simp [bit] at H
      obtain rfl := Option.some.inj h
      change a.1.val < ((pack p r).symm (st hp r pos (a.1.val+1) _)).1.val
      simp [unpack_st, Nat.mod_eq_of_lt lt]
  have ends (k : ℕ) : ∀ i : Fin (size p r), p ≤ ((pack p r).symm i).1.val + k → F^[k] (some i) = none := by
    induction k with
    | zero => intro i hi; have := ((pack p r).symm i).1.isLt; omega
    | succ k ih =>
      intro i hi
      rw [Function.iterate_succ_apply]
      change F^[k] (next hp r pos i true) = none
      cases h : next hp r pos i true with
      | none => exact fixed _
      | some j => exact ih j (by have := inc i j h; omega)
  have big : p ≤ size p r := by
    calc p = ∑ _b ∈ Finset.range p, (1:ℕ) := by simp
         _ ≤ size p r := Finset.sum_le_sum (fun b _ => pos b)
  intro i
  exact ends _ i (by omega)

end PEqualNP.Outside.L_meta_29779.Graph

namespace PEqualNP.Outside.L_meta_29779.Graph

noncomputable def liftV {p : ℕ} (r : ℕ → ℕ) (v : (b : ℕ) → Fin (r b) → ℝ) (u : Fin (size p r)) : ℝ :=
  let a := (pack p r).symm u
  v a.1.val a.2

private theorem lift_pack {p : ℕ} (r : ℕ → ℕ) (v : (b : ℕ) → Fin (r b) → ℝ)
    (a : Node p r) : liftV r v (pack p r a) = v a.1.val a.2 :=
  congrArg (fun w : Node p r => v w.1.val w.2) ((pack p r).symm_apply_apply a)

theorem lift_st {p : ℕ} (hp : 0 < p) (r : ℕ → ℕ) (pos : ∀ b, 0 < r b)
    (v : (b : ℕ) → Fin (r b) → ℝ) (cycle : ∀ (i : Fin (r p)) (j : Fin (r 0)), v p i=v 0 j)
    (b : ℕ) (hb : b ≤ p) (i : Fin (r b)) : liftV r v (st hp r pos b i.val) = v b i := by
  rcases lt_or_eq_of_le hb with lt | same
  · rw [st_at hp r pos ⟨b,lt⟩ i]
    exact lift_pack r v _
  · subst b
    rw [st_congr hp r pos (show p%p=0%p by simp) i.val]
    let j : Fin (r 0) := ⟨i.val % (r 0), Nat.mod_lt _ (pos _)⟩
    have eq : st hp r pos 0 i.val = pack p r ⟨⟨0,hp⟩,j⟩ := by
      calc
        _ = atPhase r pos ⟨0,hp⟩ i.val := congrArg
          (fun phase : Fin p => atPhase r pos phase i.val) (Fin.ext (Nat.zero_mod p))
        _ = _ := rfl
    rw [eq, lift_pack]
    exact (cycle i j).symm

noncomputable def action {p : ℕ} {A : Type*} (r : ℕ → ℕ) (act : ℕ → ℕ → A)
    (u : Fin (size p r)) (t : Bool) : A :=
  let a := (pack p r).symm u
  act a.1.val (2*a.2.val + bit t - r (a.1.val+1))

theorem harmonic {p : ℕ} {A D : Type*} (hp : 0 < p) (r : ℕ → ℕ) (pos : ∀ b, 0 < r b)
    (h0 : r 0=1) (hp1 : r p=1) (cap : ∀ b < p, r (b+1) ≤ 2*r b)
    (act : ℕ → ℕ → A) (cost : A → D → ℝ) :
    ∃ L : Fin (size p r) → D → ℝ,
      (∀ i d, 2*L i d = ∑ t : Bool, (next hp r pos i t).elim (cost (action r act i t) d) (fun j => L j d)) ∧
      (∀ d, ((2:ℝ)^p-1)*L (st hp r pos 0 0) d = ∑ b ∈ Finset.range p,
        (2:ℝ)^(p-1-b)*∑ k ∈ Finset.range (2*r b-r (b+1)), cost (act b k) d) := by
  classical
  choose V cycle bell root using fun d : D => Risk.periodicRisk p hp r h0 hp1 cap (fun b k => cost (act b k) d)
  refine ⟨fun i d => liftV r (V d) i, ?_, ?_⟩
  · intro i d
    let a := (pack p r).symm i
    have one (t : Bool) : (next hp r pos i t).elim (cost (action r act i t) d)
        (liftV r (V d)) = Risk.pick r (fun b k => cost (act b k) d) (V d)
          a.1.val (2*a.2.val+bit t) := by
      let k := 2*a.2.val+bit t
      change (if k<r (a.1.val+1) then some (st hp r pos (a.1.val+1) k) else none).elim
        (cost (act a.1.val (k-r (a.1.val+1))) d) _ =
          Risk.pick r (fun b k => cost (act b k) d) (V d) a.1.val k
      by_cases h : k < r (a.1.val+1)
      · rw [if_pos h]
        change liftV r (V d) (st hp r pos (a.1.val+1) k) = _
        calc
          _ = V d (a.1.val+1) ⟨k,h⟩ :=
            lift_st hp r pos (V d) (cycle d) _ (by have := a.1.isLt; omega) ⟨k,h⟩
          _ = _ := by simp [Risk.pick, h]
      · rw [if_neg h]
        simp [Risk.pick, h]
    rw [Fintype.sum_bool, one true, one false, add_comm]
    simpa [liftV, a, bit] using bell d a.1.val a.1.isLt a.2
  · intro d
    let zero : Fin (r 0) := ⟨0, pos 0⟩
    have hz := lift_st hp r pos (V d) (cycle d) 0 (Nat.zero_le _) zero
    change liftV r (V d) (st hp r pos 0 0) = _ at hz
    change ((2:ℝ)^p-1)*liftV r (V d) (st hp r pos 0 0) = _
    rw [hz]
    exact root d zero

end PEqualNP.Outside.L_meta_29779.Graph

set_option maxHeartbeats 1500000 in
open PEqualNP.Outside.L_meta_29779 in
theorem PEqualNP.Outside.L_meta_29779 : (∀ (d e g p : ℕ), 1 < d → 0 < e → e < d → Nat.Coprime d e → 0 < g →
  0 < p → 2^p % d = 1 → (∀ h, 0 < h → h < p → 2^h % d ≠ 1) →
  let q := g*d
  let E := g*e
  ∀ (N t : ℕ), q ≤ N → q < 2*t → t < q →
  let X := Fin N
  let I := Fin q
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun C : Circ =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧ C.output < N+N+C.size ∧
    ∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))
  let table := fun (C : Circ) (x y : X) => C.eval (PEqualNP.Represents.oneEach x y)
  ∀ (base : Circ), legal base → ∀ f : I → Equiv.Perm X,
    (∀ x : X, Function.Injective (fun j => f j x)) →
    let loss := fun (H : X → X → Bool) (D : Finset I) =>
      ((Finset.univ : Finset (X × X)).filter (fun z => H z.1 z.2 ≠
        xor (table base z.1 z.2) (decide (z.2 ∈ D.image (fun j => f j z.1))))).card
    let fits := fun C : Circ => legal C ∧ C.gates.take base.size = base.gates ∧
      C.size ≤ base.size+2*E+3 ∧ loss (table C) ∅ ≤ E
    let ideal := ((q*N*t-(2*t-q)*E : ℕ) : ℝ)/(q : ℝ)
    let R := fun b : ℕ => ((2^b*E % q)+E-1)/E
    let run := fun (s : ℕ) (z : Fin s) (n : Fin s → Bool → Option (Fin s))
        (b : ℕ) (w : Fin b → Bool) =>
      (List.ofFn w).foldl (fun (x : Option (Fin s)) (bit : Bool) =>
        x.bind (fun i => n i bit)) (some z)
    let live := fun (s : ℕ) (z : Fin s) (n : Fin s → Bool → Option (Fin s)) (b : ℕ) =>
      ((Finset.univ : Finset (Fin b → Bool)).filter (fun w => (run s z n b w).isSome)).card
    let law := fun (s : ℕ) (n : Fin s → Bool → Option (Fin s))
        (H : Fin s → Bool → X → X → Bool) (L : Fin s → Finset I → ℝ) =>
      (∃ c : Fin s → Bool, ∀ i : Fin s,
        (fun x : Option (Fin s) => x.bind (fun j => n j (c j)))^[s] (some i) = none) ∧
      ∀ i D, 2*L i D = ∑ bit : Bool, (n i bit).elim (loss (H i bit) D : ℝ) (fun j => L j D)
    (∀ (s : ℕ) (z : Fin s) (n : Fin s → Bool → Option (Fin s))
        (H : Fin s → Bool → X → X → Bool) (L : Fin s → Finset I → ℝ),
      law s n H L → (∀ i bit, loss (H i bit) ∅ ≤ E) →
      (∀ D : Finset I, D.card = t → L z D ≤ ideal) →
      (∀ b, R b ≤ live s z n b) ∧
      ((∀ b, live s z n b = R b) →
        ∃ l : ℕ, 0 < l ∧ l ≤ s ∧ p ∣ l ∧ ∀ b, R b ≤ 2^(s-l))) ∧
    let S := ∑ b ∈ Finset.range p, R b
    ∃ (z : Fin S) (n : Fin S → Bool → Option (Fin S)) (C : Fin S → Bool → Circ)
        (L : Fin S → Finset I → ℝ),
      law S n (fun i bit => table (C i bit)) L ∧ (∀ i bit, fits (C i bit)) ∧
      (∀ D : Finset I, D.card = t → L z D = ideal) ∧ (∀ b, live S z n b = R b) ∧
      ∀ w : Fin p → Bool, (run S z n p w).isSome = true → run S z n p w = some z) := by
  classical
  intro d e g p hd he hed cop hg hp hpow minimal
  dsimp only
  intro N t hqN ht htq base hbase f hf
  constructor
  · exact Tail.universal hd he hed cop hg hp hpow minimal hqN ht htq f hf
      (fun x y => base.eval (PEqualNP.Represents.oneEach x y))
  · let q := g*d
    let E := g*e
    let r := Block.width q E
    obtain ⟨h0,hp1,pos,cap,A,legal,weight⟩ :=
      Block.scheduled_actions hd he hed hg hp hpow hqN ht htq f hf base hbase
    have per (b : ℕ) : r (b%p)=r b := Period.width_mod hd hpow b
    have posAll (b : ℕ) : 0 < r b := by rw [← per b]; exact pos _ (Nat.mod_lt _ hp).le
    have capAll (b : ℕ) : r (b+1) ≤ 2*r b := by
      have hh : r (b%p+1) = r (b+1) := by rw [← per (b%p+1), Graph.resucc, per]
      have localCap : r (b%p+1) ≤ 2*r (b%p) := cap _ (Nat.mod_lt _ hp)
      rwa [hh, per] at localCap
    let z := Graph.st hp r posAll 0 0
    let n := Graph.next hp r posAll
    let C := Graph.action (p:=p) r A
    let cost := fun (c : PEqualNP.CircuitLowerBounds.Circuit) (D : Finset (Fin q)) =>
      (Block.cost f (Block.table base) (Block.table c) D : ℝ)
    obtain ⟨L, bell, root⟩ := Graph.harmonic hp r posAll h0 hp1 cap A cost
    refine ⟨z,n,C,L,⟨Graph.absorbs hp r posAll hp1,bell⟩,?_,?_,?_,?_⟩
    · intro i bit
      exact legal _ _
    · intro D hD
      have eq := (root D).trans (weight D hD)
      have fact : (2:ℝ)^p > 1 := one_lt_pow₀ (by norm_num) (by omega)
      exact mul_left_cancel₀ (sub_ne_zero.mpr fact.ne') eq
    · exact Graph.card_alive hp r posAll h0 per capAll
    · exact Graph.return_root hp r posAll h0 per capAll
