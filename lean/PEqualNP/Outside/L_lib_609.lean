import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_609_aux

def runFn {V : Type} (ask : Nat → Nat → (V → Bool) → Bool) (n : Nat) (x : V → Bool) : Nat :=
  (List.range n).foldl (fun h pos => h + ((ask pos h x).toNat <<< pos)) 0

lemma runFn_succ {V : Type} (ask : Nat → Nat → (V → Bool) → Bool) (n : Nat) (x : V → Bool) :
    runFn ask (n + 1) x = runFn ask n x + ((ask n (runFn ask n x) x).toNat <<< n) := by
  simp [runFn, List.range_succ]

lemma runFn_eq_of_ask_eq {V : Type} (ask : Nat → Nat → (V → Bool) → Bool)
    (base x : V → Bool) (d : Nat)
    (h : ∀ u : Fin d, ask u.val (runFn ask u.val base) x = ask u.val (runFn ask u.val base) base) :
    ∀ n ≤ d, runFn ask n x = runFn ask n base := by
  intro n
  induction n with
  | zero =>
    intro _
    rfl
  | succ n ih =>
    intro hle
    have hprev := ih (Nat.le_of_succ_le hle)
    rw [runFn_succ, runFn_succ, hprev]
    have hu := h ⟨n, hle⟩
    dsimp only at hu
    rw [hu]

def boolToZ2 (b : Bool) : ZMod 2 :=
  if b = true then 1 else 0

lemma boolToZ2_par (z : Nat) : boolToZ2 ((z % 2) == 1) = (z : ZMod 2) := by
  have hdiv : z = 2 * (z / 2) + z % 2 := (Nat.div_add_mod z 2).symm
  have hz : (z : ZMod 2) = ((z % 2 : Nat) : ZMod 2) := by
    conv_lhs => rw [hdiv]
    push_cast
    have h2 : (2 : ZMod 2) = 0 := by decide
    simp [h2]
  rw [hz]
  have hlt : z % 2 < 2 := Nat.mod_lt z (by decide)
  interval_cases (z % 2) <;> decide

lemma z2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

lemma z2_eq_one_of_ne_zero {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact False.elim (ha rfl)
  · rfl

lemma z2_ind_eq (a b : ZMod 2) : (1 : ZMod 2) + a + b = if a = b then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> decide

def monVal {t : Nat} (flags : Fin t → Bool) (M : Finset (Fin t)) : ZMod 2 :=
  if ∀ z ∈ M, flags z = true then 1 else 0

lemma monVal_empty {t : Nat} (flags : Fin t → Bool) : monVal flags ∅ = 1 := by
  simp [monVal]

lemma monVal_union {t : Nat} (flags : Fin t → Bool) (A B : Finset (Fin t)) :
    monVal flags (A ∪ B) = monVal flags A * monVal flags B := by
  simp only [monVal, Finset.mem_union]
  by_cases hA : ∀ z ∈ A, flags z = true
  · by_cases hB : ∀ z ∈ B, flags z = true
    · have hAB : ∀ z, z ∈ A ∨ z ∈ B → flags z = true := by
        rintro z (hz | hz)
        · exact hA z hz
        · exact hB z hz
      simp only [eq_true hA, eq_true hB, eq_true hAB, ↓reduceIte, mul_one]
    · have hAB : ¬ (∀ z, z ∈ A ∨ z ∈ B → flags z = true) := by
        intro h
        exact hB (fun z hz => h z (Or.inr hz))
      simp only [eq_false hB, eq_false hAB, ↓reduceIte, mul_zero]
  · have hAB : ¬ (∀ z, z ∈ A ∨ z ∈ B → flags z = true) := by
      intro h
      exact hA (fun z hz => h z (Or.inl hz))
    simp only [eq_false hA, eq_false hAB, ↓reduceIte, zero_mul]

def evalPoly {t : Nat} (c : Finset (Fin t) → ZMod 2) (flags : Fin t → Bool) : ZMod 2 :=
  ∑ M : Finset (Fin t), c M * monVal flags M

def polyDegLe {t : Nat} (D : Nat) (c : Finset (Fin t) → ZMod 2) : Prop :=
  ∀ M : Finset (Fin t), c M ≠ 0 → M.card ≤ D

lemma polyDegLe_mono {t D1 D2 : Nat} {c : Finset (Fin t) → ZMod 2}
    (h : polyDegLe D1 c) (hle : D1 ≤ D2) : polyDegLe D2 c :=
  fun M hM => le_trans (h M hM) hle

def constPoly {t : Nat} (k : ZMod 2) : Finset (Fin t) → ZMod 2 :=
  fun M => if M = ∅ then k else 0

lemma evalPoly_const {t : Nat} (k : ZMod 2) (flags : Fin t → Bool) :
    evalPoly (constPoly k) flags = k := by
  simp [evalPoly, constPoly, monVal_empty]

lemma polyDegLe_const {t : Nat} (k : ZMod 2) : polyDegLe 0 (constPoly (t := t) k) := by
  intro M hM
  by_cases h : M = ∅
  · simp [h]
  · simp [constPoly, h] at hM

def varPoly {t : Nat} (z : Fin t) : Finset (Fin t) → ZMod 2 :=
  fun M => if M = {z} then 1 else 0

lemma evalPoly_var {t : Nat} (z : Fin t) (flags : Fin t → Bool) :
    evalPoly (varPoly z) flags = boolToZ2 (flags z) := by
  simp only [evalPoly, varPoly, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, monVal, Finset.mem_singleton, forall_eq, boolToZ2]

lemma polyDegLe_var {t : Nat} (z : Fin t) : polyDegLe 1 (varPoly z) := by
  intro M hM
  by_cases h : M = {z}
  · simp [h]
  · simp [varPoly, h] at hM

lemma evalPoly_add {t : Nat} (c1 c2 : Finset (Fin t) → ZMod 2) (flags : Fin t → Bool) :
    evalPoly (c1 + c2) flags = evalPoly c1 flags + evalPoly c2 flags := by
  simp [evalPoly, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma polyDegLe_add {t D : Nat} {c1 c2 : Finset (Fin t) → ZMod 2}
    (h1 : polyDegLe D c1) (h2 : polyDegLe D c2) : polyDegLe D (c1 + c2) := by
  intro M hM
  by_cases hc1 : c1 M = 0
  · have hc2 : c2 M ≠ 0 := by
      intro hc2
      apply hM
      simp [Pi.add_apply, hc1, hc2]
    exact h2 M hc2
  · exact h1 M hc1

lemma evalPoly_sum {t : Nat} {α : Type*} (s : Finset α) (c : α → Finset (Fin t) → ZMod 2)
    (flags : Fin t → Bool) :
    evalPoly (∑ a ∈ s, c a) flags = ∑ a ∈ s, evalPoly (c a) flags := by
  simp only [evalPoly, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

lemma polyDegLe_sum {t D : Nat} {α : Type*} (s : Finset α) (c : α → Finset (Fin t) → ZMod 2)
    (h : ∀ a ∈ s, polyDegLe D (c a)) : polyDegLe D (∑ a ∈ s, c a) := by
  intro M hM
  rw [Finset.sum_apply] at hM
  obtain ⟨a, ha, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hM
  exact h a ha M hne

def mulPoly {t : Nat} (c1 c2 : Finset (Fin t) → ZMod 2) : Finset (Fin t) → ZMod 2 :=
  fun M => ∑ A : Finset (Fin t), ∑ B : Finset (Fin t), if A ∪ B = M then c1 A * c2 B else 0

lemma evalPoly_mul {t : Nat} (c1 c2 : Finset (Fin t) → ZMod 2) (flags : Fin t → Bool) :
    evalPoly (mulPoly c1 c2) flags = evalPoly c1 flags * evalPoly c2 flags := by
  simp only [evalPoly, mulPoly]
  have h1 :
      ∑ M : Finset (Fin t),
          (∑ A : Finset (Fin t), ∑ B : Finset (Fin t), if A ∪ B = M then c1 A * c2 B else 0) *
            monVal flags M =
        ∑ A : Finset (Fin t), ∑ B : Finset (Fin t),
          ∑ M : Finset (Fin t), if A ∪ B = M then c1 A * c2 B * monVal flags M else 0 := by
    trans (∑ M : Finset (Fin t), ∑ A : Finset (Fin t), ∑ B : Finset (Fin t),
      if A ∪ B = M then c1 A * c2 B * monVal flags M else (0 : ZMod 2))
    · refine Finset.sum_congr rfl fun M _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun A _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun B _ => ?_
      split_ifs <;> simp
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun A _ => ?_
      exact Finset.sum_comm
  rw [h1]
  have h2 :
      (∑ A : Finset (Fin t), ∑ B : Finset (Fin t),
          ∑ M : Finset (Fin t), if A ∪ B = M then c1 A * c2 B * monVal flags M else 0) =
        ∑ A : Finset (Fin t), ∑ B : Finset (Fin t),
          (c1 A * monVal flags A) * (c2 B * monVal flags B) := by
    refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, monVal_union]
    ring
  rw [h2, Finset.sum_mul]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.mul_sum]

lemma polyDegLe_mul {t D1 D2 : Nat} {c1 c2 : Finset (Fin t) → ZMod 2}
    (h1 : polyDegLe D1 c1) (h2 : polyDegLe D2 c2) : polyDegLe (D1 + D2) (mulPoly c1 c2) := by
  intro M hM
  dsimp only [mulPoly] at hM
  obtain ⟨A, _, hA⟩ := Finset.exists_ne_zero_of_sum_ne_zero hM
  obtain ⟨B, _, hB⟩ := Finset.exists_ne_zero_of_sum_ne_zero hA
  split_ifs at hB with hAB
  · have hc1 : c1 A ≠ 0 := left_ne_zero_of_mul hB
    have hc2 : c2 B ≠ 0 := right_ne_zero_of_mul hB
    have hle1 := h1 A hc1
    have hle2 := h2 B hc2
    have hu : (A ∪ B).card ≤ A.card + B.card := Finset.card_union_le A B
    rw [← hAB]
    omega
  · exact False.elim (hB rfl)

def sitePoly {V : Type} {t : Nat} (base : V → Bool) (driver : V → Option (Fin t)) (site : V) :
    Finset (Fin t) → ZMod 2 :=
  match driver site with
  | none => constPoly (boolToZ2 (base site))
  | some z => if base site = true then constPoly 1 + varPoly z else varPoly z

lemma evalPoly_sitePoly {V : Type} {t : Nat} (base : V → Bool) (driver : V → Option (Fin t))
    (site : V) (flags : Fin t → Bool) :
    evalPoly (sitePoly base driver site) flags =
      boolToZ2 (xor (base site) ((driver site).elim false flags)) := by
  cases hd : driver site with
  | none =>
    simp [sitePoly, hd, evalPoly_const]
  | some z =>
    simp only [sitePoly, hd, Option.elim_some]
    cases hb : base site
    · simp [evalPoly_var]
    · simp only [↓reduceIte, evalPoly_add, evalPoly_const, evalPoly_var]
      cases hf : flags z <;> decide

lemma polyDegLe_sitePoly {V : Type} {t : Nat} (base : V → Bool) (driver : V → Option (Fin t))
    (site : V) : polyDegLe 1 (sitePoly base driver site) := by
  cases hd : driver site with
  | none =>
    simp only [sitePoly, hd]
    exact polyDegLe_mono (polyDegLe_const _) (Nat.zero_le 1)
  | some z =>
    simp only [sitePoly, hd]
    split_ifs
    · exact polyDegLe_add (polyDegLe_mono (polyDegLe_const _) (Nat.zero_le 1)) (polyDegLe_var z)
    · exact polyDegLe_var z

lemma exists_mon_poly {V : Type} [DecidableEq V] {t : Nat}
    (base : V → Bool) (driver : V → Option (Fin t)) (mon : Finset V) :
    ∃ c : Finset (Fin t) → ZMod 2, polyDegLe mon.card c ∧
      ∀ flags : Fin t → Bool,
        evalPoly c flags =
          if ∀ j ∈ mon, xor (base j) ((driver j).elim false flags) = true then 1 else 0 := by
  induction mon using Finset.induction_on with
  | empty =>
    refine ⟨constPoly 1, polyDegLe_const 1, fun flags => ?_⟩
    simp [evalPoly_const]
  | @insert j mon' hj ih =>
    rcases ih with ⟨c', hc'deg, hc'eval⟩
    refine ⟨mulPoly (sitePoly base driver j) c', ?_, ?_⟩
    · have hcard : 1 + mon'.card = (insert j mon').card := by
        rw [Finset.card_insert_of_notMem hj]
        omega
      rw [← hcard]
      exact polyDegLe_mul (polyDegLe_sitePoly base driver j) hc'deg
    · intro flags
      rw [evalPoly_mul, evalPoly_sitePoly, hc'eval]
      simp only [boolToZ2, Finset.mem_insert, forall_eq_or_imp]
      by_cases h1 : xor (base j) ((driver j).elim false flags) = true
      · by_cases h2 : ∀ a ∈ mon', xor (base a) ((driver a).elim false flags) = true
        · simp only [eq_true h1, eq_true h2, and_self, ↓reduceIte, mul_one]
        · simp only [eq_true h1, eq_false h2, and_false, ↓reduceIte, mul_zero]
      · simp only [eq_false h1, false_and, ↓reduceIte, zero_mul]

lemma exists_deg_poly {V : Type} [DecidableEq V] {t : Nat}
    (base : V → Bool) (driver : V → Option (Fin t))
    (b : Nat) (f : (V → Bool) → Bool)
    (hf : ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ b) ∧
      ∀ input, f input = (((terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card % 2) == 1)) :
    ∃ c : Finset (Fin t) → ZMod 2, polyDegLe b c ∧
      ∀ flags : Fin t → Bool,
        evalPoly c flags = boolToZ2 (f (fun site => xor (base site) ((driver site).elim false flags))) := by
  rcases hf with ⟨terms, hdeg, hfeval⟩
  have hchoose : ∀ mon : Finset V, ∃ c : Finset (Fin t) → ZMod 2, polyDegLe mon.card c ∧
      ∀ flags : Fin t → Bool,
        evalPoly c flags =
          if ∀ j ∈ mon, xor (base j) ((driver j).elim false flags) = true then 1 else 0 :=
    fun mon => exists_mon_poly base driver mon
  choose cMon hcMonDeg hcMonEval using hchoose
  refine ⟨∑ mon ∈ terms, cMon mon, ?_, ?_⟩
  · refine polyDegLe_sum terms cMon ?_
    intro mon hmon
    exact polyDegLe_mono (hcMonDeg mon) (hdeg mon hmon)
  · intro flags
    rw [evalPoly_sum, hfeval, boolToZ2_par]
    trans ∑ mon ∈ terms,
      if ∀ j ∈ mon, xor (base j) ((driver j).elim false flags) = true then (1 : ZMod 2) else 0
    · exact Finset.sum_congr rfl fun mon _ => hcMonEval mon flags
    · simp [Finset.sum_boole]

lemma exists_prod_poly {t d : Nat} (B : Fin d → Nat)
    (c : Fin d → Finset (Fin t) → ZMod 2)
    (hc : ∀ u : Fin d, polyDegLe (B u) (c u)) :
    ∀ s : Finset (Fin d), ∃ P : Finset (Fin t) → ZMod 2,
      polyDegLe (∑ u ∈ s, B u) P ∧
      ∀ flags : Fin t → Bool, evalPoly P flags = ∏ u ∈ s, evalPoly (c u) flags := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨constPoly 1, ?_, fun flags => ?_⟩
    · simpa using polyDegLe_const (t := t) 1
    · simp [evalPoly_const]
  | @insert u s' hu ih =>
    rcases ih with ⟨P', hP'deg, hP'eval⟩
    refine ⟨mulPoly (c u) P', ?_, ?_⟩
    · rw [Finset.sum_insert hu]
      exact polyDegLe_mul (hc u) hP'deg
    · intro flags
      rw [evalPoly_mul, hP'eval, Finset.prod_insert hu]

lemma schwartz_zippel_z2 {t D : Nat} (P : Finset (Fin t) → ZMod 2)
    (hdeg : polyDegLe D P) (flags0 : Fin t → Bool) (hval : evalPoly P flags0 = 1) :
    2 ^ (t - D) ≤
      ((Finset.univ : Finset (Fin t → Bool)).filter (fun flags => evalPoly P flags = 1)).card := by
  let supp : Finset (Finset (Fin t)) := Finset.univ.filter (fun M => P M ≠ 0)
  have hsupp_ne : supp.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hall0 : ∀ M : Finset (Fin t), P M = 0 := by
      intro M
      by_contra hne
      have hmem : M ∈ supp := Finset.mem_filter.mpr ⟨Finset.mem_univ M, hne⟩
      rw [hemp] at hmem
      exact Finset.notMem_empty M hmem
    have h0 : evalPoly P flags0 = 0 := by
      simp [evalPoly, hall0]
    rw [h0] at hval
    exact zero_ne_one hval
  obtain ⟨M0, hM0_mem, hM0_max⟩ := Finset.exists_max_image supp Finset.card hsupp_ne
  have hPM0_ne : P M0 ≠ 0 := (Finset.mem_filter.mp hM0_mem).2
  have hPM0_one : P M0 = 1 := z2_eq_one_of_ne_zero hPM0_ne
  have hM0_le : M0.card ≤ D := hdeg M0 hPM0_ne
  let extend : ({ z : Fin t // z ∉ M0 } → Bool) → ({ z : Fin t // z ∈ M0 } → Bool) → (Fin t → Bool) :=
    fun g h z => if hz : z ∈ M0 then h ⟨z, hz⟩ else g ⟨z, hz⟩
  have hsum_mon_top : ∀ g : { z : Fin t // z ∉ M0 } → Bool,
      ∑ h : { z : Fin t // z ∈ M0 } → Bool, monVal (extend g h) M0 = 1 := by
    intro g
    let h1 : { z : Fin t // z ∈ M0 } → Bool := fun _ => true
    have hiff : ∀ h : { z : Fin t // z ∈ M0 } → Bool,
        (∀ z ∈ M0, extend g h z = true) ↔ h = h1 := by
      intro h
      constructor
      · intro hall
        funext ⟨z, hz⟩
        have := hall z hz
        simpa [extend, hz, h1] using this
      · rintro rfl z hz
        simp [extend, hz, h1]
    have hrew : ∀ h : { z : Fin t // z ∈ M0 } → Bool,
        monVal (extend g h) M0 = if h = h1 then 1 else 0 := by
      intro h
      simp only [monVal, hiff h]
    simp [hrew]
  have hsum_mon_other : ∀ (g : { z : Fin t // z ∉ M0 } → Bool) (M : Finset (Fin t)),
      P M ≠ 0 → M ≠ M0 →
      ∑ h : { z : Fin t // z ∈ M0 } → Bool, monVal (extend g h) M = 0 := by
    intro g M hPM hne
    have hMle : M.card ≤ M0.card :=
      hM0_max M (Finset.mem_filter.mpr ⟨Finset.mem_univ M, hPM⟩)
    have hnotSub : ¬ M0 ⊆ M := by
      intro hsub
      exact hne (Finset.eq_of_subset_of_card_le hsub hMle).symm
    rw [Finset.not_subset] at hnotSub
    obtain ⟨z0, hz0_in, hz0_not⟩ := hnotSub
    let z0' : { z : Fin t // z ∈ M0 } := ⟨z0, hz0_in⟩
    let F0 : Finset ({ z : Fin t // z ∈ M0 } → Bool) :=
      Finset.univ.filter (fun h => h z0' = false)
    let F1 : Finset ({ z : Fin t // z ∈ M0 } → Bool) :=
      Finset.univ.filter (fun h => h z0' = true)
    have hunion : (Finset.univ : Finset ({ z : Fin t // z ∈ M0 } → Bool)) = F0 ∪ F1 := by
      ext h
      simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff, F0, F1]
      cases h z0' <;> simp
    have hdisj : Disjoint F0 F1 := by
      rw [Finset.disjoint_left]
      intro h h0 h1
      have ha : h z0' = false := (Finset.mem_filter.mp h0).2
      have hb : h z0' = true := (Finset.mem_filter.mp h1).2
      rw [ha] at hb
      cases hb
    have hsum_eq : ∑ h ∈ F0, monVal (extend g h) M = ∑ h ∈ F1, monVal (extend g h) M := by
      refine Finset.sum_bij (fun h _ => Function.update h z0' true) ?_ ?_ ?_ ?_
      · intro h _
        simp [F1]
      · intro h1 hh1 h2 hh2 heq
        funext z
        by_cases hzz : z = z0'
        · subst hzz
          have ha : h1 z0' = false := (Finset.mem_filter.mp hh1).2
          have hb : h2 z0' = false := (Finset.mem_filter.mp hh2).2
          exact ha.trans hb.symm
        · have := congrFun heq z
          simpa [Function.update_of_ne hzz] using this
      · intro h1 hh1
        refine ⟨Function.update h1 z0' false, by simp [F0], ?_⟩
        funext z
        by_cases hzz : z = z0'
        · subst hzz
          have hb : h1 z0' = true := (Finset.mem_filter.mp hh1).2
          simp [hb]
        · simp [Function.update_of_ne hzz]
      · intro h _
        have hext : ∀ z ∈ M, extend g h z = extend g (Function.update h z0' true) z := by
          intro z hz
          have hzne : z ≠ z0 := fun heq => hz0_not (heq ▸ hz)
          by_cases hzm : z ∈ M0
          · have hzne' : (⟨z, hzm⟩ : { z : Fin t // z ∈ M0 }) ≠ z0' := fun heq =>
              hzne (congrArg Subtype.val heq)
            simp [extend, hzm, Function.update_of_ne hzne']
          · simp [extend, hzm]
        simp only [monVal]
        congr 1
        refine propext ⟨fun hall z hz => ?_, fun hall z hz => ?_⟩
        · rw [← hext z hz]
          exact hall z hz
        · rw [hext z hz]
          exact hall z hz
    rw [hunion, Finset.sum_union hdisj, hsum_eq]
    exact z2_add_self _
  have hexists : ∀ g : { z : Fin t // z ∉ M0 } → Bool,
      ∃ h : { z : Fin t // z ∈ M0 } → Bool, evalPoly P (extend g h) = 1 := by
    intro g
    have htotal : ∑ h : { z : Fin t // z ∈ M0 } → Bool, evalPoly P (extend g h) = 1 := by
      simp only [evalPoly]
      rw [Finset.sum_comm]
      have hpull : ∀ M : Finset (Fin t),
          ∑ h : { z : Fin t // z ∈ M0 } → Bool, P M * monVal (extend g h) M =
            if M = M0 then 1 else 0 := by
        intro M
        rw [← Finset.mul_sum]
        by_cases hMM0 : M = M0
        · subst hMM0
          simp [hPM0_one, hsum_mon_top g]
        · simp only [hMM0, ↓reduceIte]
          by_cases hPM : P M = 0
          · simp [hPM]
          · rw [hsum_mon_other g M hPM hMM0, mul_zero]
      simp [hpull]
    have hne0 : ∑ h : { z : Fin t // z ∈ M0 } → Bool, evalPoly P (extend g h) ≠ 0 := by
      rw [htotal]
      exact one_ne_zero
    obtain ⟨h, _, hh⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne0
    exact ⟨h, z2_eq_one_of_ne_zero hh⟩
  choose hPick hhPick using hexists
  let fInj : ({ z : Fin t // z ∉ M0 } → Bool) → (Fin t → Bool) := fun g => extend g (hPick g)
  have hinj : Function.Injective fInj := by
    intro g1 g2 heq
    funext ⟨z, hz⟩
    have := congrFun heq z
    simpa [fInj, extend, hz] using this
  let sols : Finset (Fin t → Bool) := Finset.univ.filter (fun flags => evalPoly P flags = 1)
  have hsub : (Finset.univ : Finset ({ z : Fin t // z ∉ M0 } → Bool)).image fInj ⊆ sols := by
    intro flags hflags
    rcases Finset.mem_image.mp hflags with ⟨g, _, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhPick g⟩
  have hcard_dom : Fintype.card ({ z : Fin t // z ∉ M0 } → Bool) = 2 ^ (t - M0.card) := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl, Fintype.card_coe,
      Fintype.card_fin]
  have hpow : 2 ^ (t - D) ≤ 2 ^ (t - M0.card) :=
    Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_left hM0_le t)
  calc
    2 ^ (t - D) ≤ 2 ^ (t - M0.card) := hpow
    _ = (Finset.univ : Finset ({ z : Fin t // z ∉ M0 } → Bool)).card := by
          rw [Finset.card_univ, hcard_dom]
    _ = ((Finset.univ : Finset ({ z : Fin t // z ∉ M0 } → Bool)).image fInj).card :=
          (Finset.card_image_of_injective _ hinj).symm
    _ ≤ sols.card := Finset.card_le_card hsub

theorem main : (∀ (m r L d : Nat), 0 < L →
  let V := Fin m × Fin r
  let W := V → Bool
  let deg := fun (b : Nat) (f : W → Bool) =>
    ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ b) ∧
      ∀ input, f input = (((terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card % 2) == 1)
  let t := m/L
  let F := Fin t → Bool
  let run := fun (ask : Nat → Nat → W → Bool) (n : Nat) (x : W) =>
    (List.range n).foldl (fun h pos => h + ((ask pos h x).toNat <<< pos)) 0
  ∀ (ask : Nat → Nat → W → Bool) (leaf : Nat → Fin L → Fin m → Fin r → Bool) (base : W),
    let path := run ask d base
    (∃ a : Fin L, ∀ i, (fun v => base (i,v)) ≠ leaf path a i) →
    ∀ B : Fin d → Nat, (∀ u, deg (B u) (ask u.val (run ask u.val base))) →
    ∃ (driver : V → Option (Fin t)) (embed : F → W),
      (∀ flags site, embed flags site = xor (base site) ((driver site).elim false flags)) ∧
      Function.Injective embed ∧
      (∀ flags : F, (∃ z, flags z = true) → ∀ a : Fin L, ∃ i,
        (fun v => embed flags (i,v)) = leaf path a i) ∧
      2^(t - ∑ u : Fin d, B u) ≤ 1 +
        ((Finset.univ : Finset F).filter (fun active =>
          (∃ z, active z = true) ∧ run ask d (embed active) = path)).card) := by
  intro m r L d hL V W deg t F run ask leaf base path hmiss B hB
  have htm : t * L ≤ m := Nat.div_mul_le_self m L
  let driver : V → Option (Fin t) := fun site =>
    if h : site.1.val < t * L then
      let z : Fin t := ⟨site.1.val / L, Nat.div_lt_of_lt_mul (by rwa [mul_comm])⟩
      let a : Fin L := ⟨site.1.val % L, Nat.mod_lt _ hL⟩
      if base site ≠ leaf path a site.1 site.2 then some z else none
    else none
  let embed : F → W := fun flags site => xor (base site) ((driver site).elim false flags)
  have hidx_lt : ∀ (z : Fin t) (a : Fin L), z.val * L + a.val < t * L := by
    intro z a
    have hz1 : (z.val + 1) * L ≤ t * L := Nat.mul_le_mul_right L z.isLt
    have hmul : (z.val + 1) * L = z.val * L + L := Nat.succ_mul z.val L
    omega
  have hidx_div : ∀ (z : Fin t) (a : Fin L), (z.val * L + a.val) / L = z.val := by
    intro z a
    rw [mul_comm z.val L, Nat.mul_add_div hL, Nat.div_eq_of_lt a.isLt, Nat.add_zero]
  have hidx_mod : ∀ (z : Fin t) (a : Fin L), (z.val * L + a.val) % L = a.val := by
    intro z a
    rw [mul_comm z.val L, Nat.mul_add_mod, Nat.mod_eq_of_lt a.isLt]
  refine ⟨driver, embed, fun _ _ => rfl, ?_, ?_, ?_⟩
  · intro f1 f2 heq
    rcases hmiss with ⟨a0, ha0⟩
    funext z
    let i : Fin m := ⟨z.val * L + a0.val, lt_of_lt_of_le (hidx_lt z a0) htm⟩
    have hne_fn : (fun v => base (i, v)) ≠ leaf path a0 i := ha0 i
    have hex_v : ∃ v : Fin r, base (i, v) ≠ leaf path a0 i v := by
      by_contra hall
      apply hne_fn
      funext v
      by_contra hv
      exact hall ⟨v, hv⟩
    obtain ⟨v, hv⟩ := hex_v
    have hdrv : driver (i, v) = some z := by
      have hi_lt : i.val < t * L := hidx_lt z a0
      have ha_eq : (⟨i.val % L, Nat.mod_lt _ hL⟩ : Fin L) = a0 := Fin.ext (hidx_mod z a0)
      have hz_eq : (⟨i.val / L, Nat.div_lt_of_lt_mul (by rwa [mul_comm])⟩ : Fin t) = z :=
        Fin.ext (hidx_div z a0)
      dsimp only [driver]
      simp only [hi_lt, ↓reduceDIte, ha_eq, hz_eq, hv, ne_eq, not_false_eq_true, ↓reduceIte]
    have hsite := congrFun heq (i, v)
    simp only [embed, hdrv, Option.elim_some] at hsite
    cases hb : base (i, v) <;> cases h1 : f1 z <;> cases h2 : f2 z <;> simp_all
  · intro flags ⟨z, hz⟩ a
    let i : Fin m := ⟨z.val * L + a.val, lt_of_lt_of_le (hidx_lt z a) htm⟩
    refine ⟨i, ?_⟩
    funext v
    have hi_lt : i.val < t * L := hidx_lt z a
    have ha_eq : (⟨i.val % L, Nat.mod_lt _ hL⟩ : Fin L) = a := Fin.ext (hidx_mod z a)
    have hz_eq : (⟨i.val / L, Nat.div_lt_of_lt_mul (by rwa [mul_comm])⟩ : Fin t) = z :=
      Fin.ext (hidx_div z a)
    by_cases hdiff : base (i, v) = leaf path a i v
    · have hdrv : driver (i, v) = none := by
        dsimp only [driver]
        simp only [hi_lt, ↓reduceDIte, ha_eq, hdiff, ne_eq, not_true_eq_false, ↓reduceIte]
      simp [embed, hdrv, hdiff]
    · have hdrv : driver (i, v) = some z := by
        dsimp only [driver]
        simp only [hi_lt, ↓reduceDIte, ha_eq, hz_eq, hdiff, ne_eq, not_false_eq_true, ↓reduceIte]
      simp only [embed, hdrv, Option.elim_some, hz]
      cases hb : base (i, v) <;> cases hl : leaf path a i v <;> simp_all
  · have hzero_embed : embed (fun _ => false) = base := by
      funext site
      cases hd : driver site <;> simp [embed, hd]
    have hchoose : ∀ u : Fin d, ∃ c : Finset (Fin t) → ZMod 2, polyDegLe (B u) c ∧
        ∀ flags : F, evalPoly c flags = boolToZ2 (ask u.val (run ask u.val base) (embed flags)) := by
      intro u
      rcases hB u with ⟨terms, hdeg, hfeval⟩
      exact exists_deg_poly base driver (B u) (ask u.val (run ask u.val base))
        ⟨terms, hdeg, fun input => by convert hfeval input⟩
    choose cAsk hcAskDeg hcAskEval using hchoose
    let cInd : Fin d → Finset (Fin t) → ZMod 2 := fun u =>
      constPoly 1 + cAsk u + constPoly (boolToZ2 (ask u.val (run ask u.val base) base))
    have hcIndDeg : ∀ u : Fin d, polyDegLe (B u) (cInd u) := by
      intro u
      refine polyDegLe_add ?_ (polyDegLe_mono (polyDegLe_const _) (Nat.zero_le _))
      exact polyDegLe_add (polyDegLe_mono (polyDegLe_const _) (Nat.zero_le _)) (hcAskDeg u)
    have hcIndEval : ∀ (u : Fin d) (flags : F),
        evalPoly (cInd u) flags =
          if ask u.val (run ask u.val base) (embed flags) =
              ask u.val (run ask u.val base) base then 1 else 0 := by
      intro u flags
      simp only [cInd, evalPoly_add, evalPoly_const, hcAskEval u flags, z2_ind_eq]
      cases ask u.val (run ask u.val base) (embed flags) <;>
        cases ask u.val (run ask u.val base) base <;> decide
    obtain ⟨P, hPdeg, hPeval⟩ := exists_prod_poly B cInd hcIndDeg Finset.univ
    have hP0 : evalPoly P (fun _ => false) = 1 := by
      rw [hPeval]
      refine Finset.prod_eq_one fun u _ => ?_
      rw [hcIndEval, hzero_embed]
      simp
    have hsz := schwartz_zippel_z2 P hPdeg (fun _ => false) hP0
    have hsub :
        (Finset.univ : Finset F).filter (fun flags => evalPoly P flags = 1) ⊆
          insert (fun _ : Fin t => false)
            ((Finset.univ : Finset F).filter (fun active =>
              (∃ z, active z = true) ∧ run ask d (embed active) = path)) := by
      intro flags hflags
      have hP1 : evalPoly P flags = 1 := (Finset.mem_filter.mp hflags).2
      have hall : ∀ u : Fin d,
          ask u.val (run ask u.val base) (embed flags) =
            ask u.val (run ask u.val base) base := by
        intro u
        by_contra hne
        have h0 : evalPoly (cInd u) flags = 0 := by
          rw [hcIndEval]
          simp [hne]
        have hp0 : evalPoly P flags = 0 := by
          rw [hPeval]
          exact Finset.prod_eq_zero (Finset.mem_univ u) h0
        rw [hp0] at hP1
        exact zero_ne_one hP1
      have hrun_eq : run ask d (embed flags) = path :=
        runFn_eq_of_ask_eq ask base (embed flags) d hall d (Nat.le_refl d)
      by_cases hact : ∃ z, flags z = true
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hact, hrun_eq⟩)
      · have hfl0 : flags = fun _ => false := by
          funext z
          cases hfz : flags z
          · rfl
          · exact False.elim (hact ⟨z, hfz⟩)
        rw [hfl0]
        exact Finset.mem_insert_self _ _
    have hcard_le :
        ((Finset.univ : Finset F).filter (fun flags => evalPoly P flags = 1)).card ≤
          1 + ((Finset.univ : Finset F).filter (fun active =>
            (∃ z, active z = true) ∧ run ask d (embed active) = path)).card := by
      calc
        ((Finset.univ : Finset F).filter (fun flags => evalPoly P flags = 1)).card
            ≤ (insert (fun _ : Fin t => false)
                ((Finset.univ : Finset F).filter (fun active =>
                  (∃ z, active z = true) ∧ run ask d (embed active) = path))).card :=
              Finset.card_le_card hsub
        _ ≤ ((Finset.univ : Finset F).filter (fun active =>
              (∃ z, active z = true) ∧ run ask d (embed active) = path)).card + 1 :=
              Finset.card_insert_le _ _
        _ = 1 + ((Finset.univ : Finset F).filter (fun active =>
              (∃ z, active z = true) ∧ run ask d (embed active) = path)).card :=
              Nat.add_comm _ 1
    exact le_trans hsz hcard_le

end PEqualNP.Outside.L_lib_609_aux

theorem PEqualNP.Outside.L_lib_609 : (∀ (m r L d : Nat), 0 < L →
  let V := Fin m × Fin r
  let W := V → Bool
  let deg := fun (b : Nat) (f : W → Bool) =>
    ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ b) ∧
      ∀ input, f input = (((terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card % 2) == 1)
  let t := m/L
  let F := Fin t → Bool
  let run := fun (ask : Nat → Nat → W → Bool) (n : Nat) (x : W) =>
    (List.range n).foldl (fun h pos => h + ((ask pos h x).toNat <<< pos)) 0
  ∀ (ask : Nat → Nat → W → Bool) (leaf : Nat → Fin L → Fin m → Fin r → Bool) (base : W),
    let path := run ask d base
    (∃ a : Fin L, ∀ i, (fun v => base (i,v)) ≠ leaf path a i) →
    ∀ B : Fin d → Nat, (∀ u, deg (B u) (ask u.val (run ask u.val base))) →
    ∃ (driver : V → Option (Fin t)) (embed : F → W),
      (∀ flags site, embed flags site = xor (base site) ((driver site).elim false flags)) ∧
      Function.Injective embed ∧
      (∀ flags : F, (∃ z, flags z = true) → ∀ a : Fin L, ∃ i,
        (fun v => embed flags (i,v)) = leaf path a i) ∧
      2^(t - ∑ u : Fin d, B u) ≤ 1 +
        ((Finset.univ : Finset F).filter (fun active =>
          (∃ z, active z = true) ∧ run ask d (embed active) = path)).card) := by
  exact PEqualNP.Outside.L_lib_609_aux.main
