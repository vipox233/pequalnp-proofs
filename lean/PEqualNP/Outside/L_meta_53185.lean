import Mathlib
import PEqualNP.Defs
import PEqualNP.Library.Helpers.FiniteGateBank

namespace PEqualNP.Outside.L_meta_53185_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.CoverCircuit
  (run wires_eq run_append run_nil run_singleton run_length getD_run
   getD_snoc_length eval_and2 eval_or2)

open Classical

private def bitsF {n : Nat} (s : Finset (Fin n)) : List Bool :=
  List.ofFn (fun j : Fin n => decide (j ∈ s))

private lemma bitsF_length {n : Nat} (s : Finset (Fin n)) : (bitsF s).length = n := by
  simp [bitsF]

private lemma bitsF_getD {n : Nat} (s : Finset (Fin n)) (k : Fin n) :
    (bitsF s).getD k.val false = decide (k ∈ s) := by
  simp [bitsF, List.getD_eq_getElem?_getD, k.isLt]

private lemma bitsF_mono {n : Nat} {s1 s2 : Finset (Fin n)} (hsub : s1 ⊆ s2) (i : Nat) :
    (bitsF s1).getD i false = true → (bitsF s2).getD i false = true := by
  by_cases hi : i < n
  · have h1 := bitsF_getD s1 ⟨i, hi⟩
    have h2 := bitsF_getD s2 ⟨i, hi⟩
    rw [h1, h2]
    simp only [decide_eq_true_eq]
    exact fun h => hsub h
  · intro h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [bitsF_length]; omega)] at h
    cases h

private lemma list_ordered_append {a1 a2 b1 b2 : List Bool}
    (hlen : a1.length = a2.length)
    (ha : ∀ i, a1.getD i false = true → a2.getD i false = true)
    (hb : ∀ i, b1.getD i false = true → b2.getD i false = true) :
    ∀ i, (a1 ++ b1).getD i false = true → (a2 ++ b2).getD i false = true := by
  intro i hi
  by_cases h : i < a1.length
  · rw [List.getD_append _ _ _ _ h] at hi
    rw [List.getD_append _ _ _ _ (hlen ▸ h)]
    exact ha i hi
  · have hge : a1.length ≤ i := Nat.le_of_not_lt h
    rw [List.getD_append_right _ _ _ _ hge] at hi
    rw [List.getD_append_right _ _ _ _ (hlen ▸ hge), ← hlen]
    exact hb (i - a1.length) hi

private lemma mono_run {gs : List Gate}
    (hmono : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ {w1 w2 : List Bool}, w1.length = w2.length →
      (∀ i, w1.getD i false = true → w2.getD i false = true) →
      ∀ i, (run gs w1).getD i false = true → (run gs w2).getD i false = true := by
  induction gs with
  | nil => intro _ _ _ hw; exact hw
  | cons g gs ih =>
    intro w1 w2 hlen hw
    have hg := (hmono g (by simp)).1
    have hrest : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hmono g' (by simp [hg'])
    change ∀ i, (run gs (w1 ++ [g.op.eval (g.inputs.map fun k => w1.getD k false)])).getD i false = true →
      (run gs (w2 ++ [g.op.eval (g.inputs.map fun k => w2.getD k false)])).getD i false = true
    apply ih hrest (by simp [hlen])
    apply list_ordered_append hlen hw
    intro i hi
    cases i with
    | zero =>
      simp only [List.getD_cons_zero] at hi ⊢
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with hand | hor
      · rw [hand] at hi ⊢
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hi ⊢
        intro k hk
        exact hw k (hi k hk)
      · rw [hor] at hi ⊢
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hi ⊢
        obtain ⟨k, hk, hk1⟩ := hi
        exact ⟨k, hk, hw k hk1⟩
    | succ i =>
      simp at hi

private lemma mono_wires {C : Circuit} (hM : Monotone2 C) {w1 w2 : List Bool}
    (hlen : w1.length = w2.length)
    (hw : ∀ i, w1.getD i false = true → w2.getD i false = true) :
    ∀ i, (C.wires w1).getD i false = true → (C.wires w2).getD i false = true :=
  mono_run hM hlen hw

private structure MNet (n : Nat) where
  gates : List Gate
  mono : Monotone2 ⟨gates, 0⟩
  back : ∀ j (hj : j < gates.length), ∀ i ∈ gates[j].inputs, i < n + j

private def MNet.empty (n : Nat) : MNet n :=
  ⟨[], by intro g hg; simp at hg, by intro j hj; simp at hj⟩

private theorem MNet.readsBack {n : Nat} (p : MNet n) : ReadsBack n ⟨p.gates, 0⟩ := by
  intro j hj i hi
  exact p.back j hj i (by simpa [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using hi)

private def MNet.has {X : Type} {n : Nat} (p : MNet n) (raw : X → List Bool) (f : X → Bool) : Prop :=
  ∃ i, i < n + p.gates.length ∧ ∀ x, (run p.gates (raw x)).getD i false = f x

private def MNet.ext {X : Type} {n : Nat} (raw : X → List Bool) (p q : MNet n) : Prop :=
  ∀ f, p.has raw f → q.has raw f

private lemma MNet.ext_refl {X : Type} {n : Nat} (raw : X → List Bool) (p : MNet n) :
    MNet.ext raw p p := fun _ h => h

private lemma MNet.ext_trans {X : Type} {n : Nat} {raw : X → List Bool} {p q r : MNet n}
    (h1 : MNet.ext raw p q) (h2 : MNet.ext raw q r) : MNet.ext raw p r :=
  fun f hf => h2 f (h1 f hf)

private def MNet.push {n : Nat} (p : MNet n) (g : Gate)
    (hmono : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hok : ∀ i ∈ g.inputs, i < n + p.gates.length) : MNet n where
  gates := p.gates ++ [g]
  mono := by
    intro v hv
    rcases List.mem_append.mp hv with old | last
    · exact p.mono v old
    · exact (List.mem_singleton.mp last) ▸ hmono
  back := by
    intro j hj i hi
    by_cases h : j < p.gates.length
    · rw [List.getElem_append_left h] at hi
      exact p.back j h i hi
    · have heq : j = p.gates.length := by simp at hj; omega
      subst heq
      simp at hi
      exact hok i hi

private lemma MNet.binary {X : Type} {n : Nat} {raw : X → List Bool}
    (hwidth : ∀ x, (raw x).length = n) (p : MNet n) (a b : X → Bool)
    (ha : p.has raw a) (hb : p.has raw b) (isAnd : Bool) :
    ∃ q : MNet n, MNet.ext raw p q ∧
      q.has raw (fun x => if isAnd then a x && b x else a x || b x) := by
  obtain ⟨ia, hia, hra⟩ := ha
  obtain ⟨ib, hib, hrb⟩ := hb
  let g : Gate := ⟨if isAnd then .and else .or, [ia, ib]⟩
  let q := p.push g (by cases isAnd <;> simp [g]) (by simp [g, hia, hib])
  have hlen : ∀ x, (run p.gates (raw x)).length = n + p.gates.length := fun x => by
    rw [run_length, hwidth]
  refine ⟨q, ?_, n + p.gates.length, by simp [q, MNet.push], ?_⟩
  · rintro f ⟨i, hi, hr⟩
    refine ⟨i, by simp [q, MNet.push]; omega, fun x => ?_⟩
    change (run (p.gates ++ [g]) (raw x)).getD i false = f x
    rw [run_append, getD_run _ _ _ (by rw [hlen x]; exact hi)]
    exact hr x
  · intro x
    change (run (p.gates ++ [g]) (raw x)).getD (n + p.gates.length) false = _
    rw [run_append, run_singleton, ← hlen x, getD_snoc_length]
    cases isAnd <;> simp only [g, ite_true, ite_false, Bool.false_eq_true, List.map_cons,
      List.map_nil, eval_and2, eval_or2, hra x, hrb x]

private lemma MNet.allList {X J : Type} {n : Nat} {raw : X → List Bool}
    (hwidth : ∀ x, (raw x).length = n) (p : MNet n)
    (htrue : p.has raw (fun _ => true)) (l : List J) (f : J → X → Bool)
    (hknown : ∀ j ∈ l, p.has raw (f j)) :
    ∃ q : MNet n, MNet.ext raw p q ∧ q.has raw (fun x => l.all (fun j => f j x)) := by
  induction l with
  | nil => exact ⟨p, MNet.ext_refl raw p, by simpa using htrue⟩
  | cons j l ih =>
    obtain ⟨q, hq, hold⟩ := ih (fun i hi => hknown i (by simp [hi]))
    obtain ⟨r, hr, hans⟩ := MNet.binary hwidth q _ _ (hq _ (hknown j (by simp))) hold true
    exact ⟨r, MNet.ext_trans hq hr, by simpa [List.all_cons] using hans⟩

private lemma MNet.anyList {X J : Type} {n : Nat} {raw : X → List Bool}
    (hwidth : ∀ x, (raw x).length = n) (p : MNet n)
    (hfalse : p.has raw (fun _ => false)) (l : List J) (f : J → X → Bool)
    (hknown : ∀ j ∈ l, p.has raw (f j)) :
    ∃ q : MNet n, MNet.ext raw p q ∧ q.has raw (fun x => l.any (fun j => f j x)) := by
  induction l with
  | nil => exact ⟨p, MNet.ext_refl raw p, by simpa using hfalse⟩
  | cons j l ih =>
    obtain ⟨q, hq, hold⟩ := ih (fun i hi => hknown i (by simp [hi]))
    obtain ⟨r, hr, hans⟩ := MNet.binary hwidth q _ _ (hq _ (hknown j (by simp))) hold false
    exact ⟨r, MNet.ext_trans hq hr, by simpa [List.any_cons] using hans⟩

private lemma MNet.buildAll {X J : Type} {n : Nat} {raw : X → List Bool}
    (p : MNet n) (l : List J) (f : J → X → Bool)
    (hbuild : ∀ j ∈ l, ∀ q : MNet n, MNet.ext raw p q →
      ∃ r : MNet n, MNet.ext raw q r ∧ r.has raw (f j)) :
    ∃ r : MNet n, MNet.ext raw p r ∧ ∀ j ∈ l, r.has raw (f j) := by
  induction l with
  | nil => exact ⟨p, MNet.ext_refl raw p, by simp⟩
  | cons j l ih =>
    obtain ⟨q, hq, hold⟩ := ih (fun i hi => hbuild i (by simp [hi]))
    obtain ⟨r, hr, hans⟩ := hbuild j (by simp) q hq
    refine ⟨r, MNet.ext_trans hq hr, fun i hi => ?_⟩
    rcases List.mem_cons.mp hi with rfl | ht
    · exact hans
    · exact hr _ (hold i ht)

private theorem fwd (m d a b : Nat) (X : Fin m → Finset (Fin d)) (Y : Fin m → Finset (Fin a))
    (down up : Fin m → Nat) :
    (∃ (P Q : Circuit) (s : Fin b → Nat) (o : Fin a → Nat),
      let high := fun i => (Finset.univ : Finset (Fin b)).filter (fun j =>
        (P.wires (bitsF (X i) ++ [false, true])).getD (s j) false = false)
      Monotone2 P ∧ Monotone2 Q ∧
      ReadsBack (d + 2) P ∧ ReadsBack (d + b + 2) Q ∧
      (∀ j, s j < d + 2 + P.size) ∧ (∀ j, o j < d + b + 2 + Q.size) ∧
      ∀ i (z : Finset (Fin b)), (high i \ z).card ≤ down i → (z \ high i).card ≤ up i →
        ∀ j, (Q.wires (bitsF (X i) ++ bitsF z ++ [false, true])).getD (o j) false = decide (j ∈ Y i)) →
    ∃ h : Fin m → Nat, (∀ i, h i ≤ b) ∧ ∀ i j, X i ⊆ X j →
      h i + (if Y i ⊆ Y j then 0 else down i + up j + 1) ≤ h j := by
  rintro ⟨P, Q, s, o, hMP, hMQ, _hRBP, _hRBQ, _hs, _ho, hCorr⟩
  let high : Fin m → Finset (Fin b) := fun i =>
    (Finset.univ : Finset (Fin b)).filter (fun k =>
      (P.wires (bitsF (X i) ++ [false, true])).getD (s k) false = false)
  let h : Fin m → Nat := fun i => b - (high i).card
  have hcard_le : ∀ i, (high i).card ≤ b := fun i => by
    have h1 := Finset.card_le_card (Finset.subset_univ (high i))
    simpa using h1
  refine ⟨h, fun i => by dsimp [h]; omega, ?_⟩
  intro i j hXij
  have hsub : high j ⊆ high i := by
    intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    cases hval : (P.wires (bitsF (X i) ++ [false, true])).getD (s k) false with
    | false => rfl
    | true =>
      have hord : ∀ t, (bitsF (X i) ++ [false, true]).getD t false = true →
          (bitsF (X j) ++ [false, true]).getD t false = true :=
        list_ordered_append (by simp [bitsF_length]) (bitsF_mono hXij) (fun _ ht => ht)
      have htrue := mono_wires hMP (by simp [bitsF_length]) hord (s k) hval
      rw [hk'] at htrue
      cases htrue
  have hle : (high j).card ≤ (high i).card := Finset.card_le_card hsub
  by_cases hYij : Y i ⊆ Y j
  · rw [ite_eq_left hYij]
    dsimp [h]
    have := hcard_le i
    have := hcard_le j
    omega
  · rw [ite_eq_right hYij]
    by_contra hlt
    push Not at hlt
    have hdiff_le : (high i \ high j).card ≤ down i + up j := by
      rw [Finset.card_sdiff_of_subset hsub]
      dsimp [h] at hlt
      have := hcard_le i
      have := hcard_le j
      omega
    let Δ := high i \ high j
    have hmin_le : min Δ.card (down i) ≤ Δ.card := Nat.min_le_left _ _
    obtain ⟨D, hDsub, hDcard⟩ := Finset.exists_subset_card_eq hmin_le
    let z : Finset (Fin b) := high i \ D
    have hDhi : D ⊆ high i := hDsub.trans Finset.sdiff_subset
    have hiz : (high i \ z).card ≤ down i := by
      have heq : high i \ z = D := by
        ext x
        simp only [z, Finset.mem_sdiff]
        by_cases hxD : x ∈ D
        · simp [hxD, hDhi hxD]
        · simp [hxD]
      rw [heq, hDcard]
      exact Nat.min_le_right _ _
    have hzi : (z \ high i).card ≤ up i := by
      have heq : z \ high i = ∅ := by
        ext x; simp [z]
      rw [heq]; simp
    have hhj_sub_z : high j ⊆ z := by
      intro x hx
      refine Finset.mem_sdiff.mpr ⟨hsub hx, fun hxD => ?_⟩
      exact (Finset.mem_sdiff.mp (hDsub hxD)).2 hx
    have hjz : (high j \ z).card ≤ down j := by
      rw [Finset.sdiff_eq_empty_iff_subset.mpr hhj_sub_z]; simp
    have hzj : (z \ high j).card ≤ up j := by
      have heq : z \ high j = Δ \ D := by
        ext x; simp [z, Δ, Finset.mem_sdiff]; tauto
      rw [heq, Finset.card_sdiff_of_subset hDsub, hDcard]
      dsimp only [Δ]
      omega
    obtain ⟨u, huYi, huYj⟩ := Finset.not_subset.mp hYij
    have hi_true : (Q.wires (bitsF (X i) ++ bitsF z ++ [false, true])).getD (o u) false = true := by
      rw [hCorr i z hiz hzi u]
      simpa using huYi
    have hj_false : (Q.wires (bitsF (X j) ++ bitsF z ++ [false, true])).getD (o u) false = false := by
      rw [hCorr j z hjz hzj u]
      simpa using huYj
    have hord : ∀ t, (bitsF (X i) ++ bitsF z ++ [false, true]).getD t false = true →
        (bitsF (X j) ++ bitsF z ++ [false, true]).getD t false = true := by
      apply list_ordered_append (by simp [bitsF_length]) _ (fun _ ht => ht)
      exact list_ordered_append (by simp [bitsF_length]) (bitsF_mono hXij) (fun _ ht => ht)
    have hj_true := mono_wires hMQ (by simp [bitsF_length]) hord (o u) hi_true
    rw [hj_false] at hj_true
    cases hj_true

private theorem bwd (m d a b : Nat) (X : Fin m → Finset (Fin d)) (Y : Fin m → Finset (Fin a))
    (down up : Fin m → Nat) :
    (∃ h : Fin m → Nat, (∀ i, h i ≤ b) ∧ ∀ i j, X i ⊆ X j →
      h i + (if Y i ⊆ Y j then 0 else down i + up j + 1) ≤ h j) →
    ∃ (P Q : Circuit) (s : Fin b → Nat) (o : Fin a → Nat),
      let high := fun i => (Finset.univ : Finset (Fin b)).filter (fun j =>
        (P.wires (bitsF (X i) ++ [false, true])).getD (s j) false = false)
      Monotone2 P ∧ Monotone2 Q ∧
      ReadsBack (d + 2) P ∧ ReadsBack (d + b + 2) Q ∧
      (∀ j, s j < d + 2 + P.size) ∧ (∀ j, o j < d + b + 2 + Q.size) ∧
      ∀ i (z : Finset (Fin b)), (high i \ z).card ≤ down i → (z \ high i).card ≤ up i →
        ∀ j, (Q.wires (bitsF (X i) ++ bitsF z ++ [false, true])).getD (o j) false = decide (j ∈ Y i) := by
  rintro ⟨h, hle_b, hmono_h⟩

  let rawP : Finset (Fin d) → List Bool := fun S => bitsF S ++ [false, true]
  have hwidthP : ∀ S, (rawP S).length = d + 2 := fun S => by simp [rawP, bitsF_length]
  let p0 : MNet (d + 2) := MNet.empty (d + 2)
  have p0_var : ∀ v : Fin d, p0.has rawP (fun S => decide (v ∈ S)) := fun v => by
    refine ⟨v.val, by simp [p0, MNet.empty]; omega, fun S => ?_⟩
    change (bitsF S ++ [false, true]).getD v.val false = decide (v ∈ S)
    rw [List.getD_append _ _ _ _ (by rw [bitsF_length]; exact v.isLt), bitsF_getD]
  have p0_false : p0.has rawP (fun _ => false) := by
    refine ⟨d, by simp [p0, MNet.empty], fun S => ?_⟩
    change (bitsF S ++ [false, true]).getD d false = false
    rw [List.getD_append_right _ _ _ _ (by rw [bitsF_length]), bitsF_length]; simp
  have p0_true : p0.has rawP (fun _ => true) := by
    refine ⟨d + 1, by simp [p0, MNet.empty], fun S => ?_⟩
    change (bitsF S ++ [false, true]).getD (d + 1) false = true
    rw [List.getD_append_right _ _ _ _ (by rw [bitsF_length]; omega), bitsF_length]
    simp
  let encF : Fin b → Finset (Fin d) → Bool :=
    fun k S => decide (∃ i : Fin m, X i ⊆ S ∧ k.val < h i)
  obtain ⟨pP, _hpP_ext, hpP_has⟩ := MNet.buildAll p0 (List.finRange b) encF (by
    intro k _ q hq
    let rows : List (Fin m) := (List.finRange m).filter (fun i => decide (k.val < h i))
    let term : Fin m → Finset (Fin d) → Bool := fun i S => decide (X i ⊆ S)
    obtain ⟨q1, hq1, hterms⟩ := MNet.buildAll q rows term (by
      intro i _ r hr
      let vars : List (Fin d) := (X i).toList
      obtain ⟨r1, hr1, hall⟩ := MNet.allList hwidthP r (hr _ (hq _ p0_true)) vars
        (fun v S => decide (v ∈ S)) (fun v _ => hr _ (hq _ (p0_var v)))
      refine ⟨r1, hr1, ?_⟩
      convert hall using 2 with S
      apply Bool.eq_iff_iff.mpr
      simp only [term, vars, List.all_eq_true, Finset.mem_toList, decide_eq_true_eq]
      exact Finset.subset_iff)
    obtain ⟨q2, hq2, hany⟩ := MNet.anyList hwidthP q1 (hq1 _ (hq _ p0_false)) rows term hterms
    refine ⟨q2, MNet.ext_trans hq1 hq2, ?_⟩
    convert hany using 2 with S
    apply Bool.eq_iff_iff.mpr
    simp only [encF, rows, term, List.any_eq_true, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq]
    tauto)
  let P : Circuit := ⟨pP.gates, 0⟩
  have hs_ex : ∀ k : Fin b, ∃ idx < d + 2 + P.size,
      ∀ S, (P.wires (rawP S)).getD idx false = encF k S := fun k =>
    hpP_has k (List.mem_finRange k)
  let s : Fin b → Nat := fun k => Classical.choose (hs_ex k)
  have hs_lt : ∀ k, s k < d + 2 + P.size := fun k => (Classical.choose_spec (hs_ex k)).1
  have hs_eval : ∀ k S, (P.wires (rawP S)).getD (s k) false = encF k S :=
    fun k S => (Classical.choose_spec (hs_ex k)).2 S
  let high : Fin m → Finset (Fin b) := fun i =>
    (Finset.univ : Finset (Fin b)).filter (fun k =>
      (P.wires (bitsF (X i) ++ [false, true])).getD (s k) false = false)
  have hhigh_eq : ∀ i (k : Fin b), k ∈ high i ↔ h i ≤ k.val := by
    intro i k
    simp only [high, Finset.mem_filter, Finset.mem_univ, true_and]
    change (P.wires (rawP (X i))).getD (s k) false = false ↔ h i ≤ k.val
    rw [hs_eval k (X i)]
    simp only [encF, decide_eq_false_iff_not, not_exists, not_and]
    constructor
    · intro hno
      have := hno i (Finset.Subset.refl _)
      omega
    · intro hge r hXr hkr
      have hle_hr : h r ≤ h i := by
        have := hmono_h r i hXr
        omega
      omega
  have hhigh_card : ∀ i, (high i).card = b - h i := by
    intro i
    have hbij : (high i).card = (Finset.Ico (h i) b).card := by
      refine Finset.card_bij (fun k _ => k.val) ?_ ?_ ?_
      · intro k hk
        exact Finset.mem_Ico.mpr ⟨(hhigh_eq i k).mp hk, k.isLt⟩
      · intro k1 _ k2 _ heq
        exact Fin.ext heq
      · intro x hx
        obtain ⟨hx1, hx2⟩ := Finset.mem_Ico.mp hx
        exact ⟨⟨x, hx2⟩, (hhigh_eq i ⟨x, hx2⟩).mpr hx1, rfl⟩
    rw [hbij, Nat.card_Ico]

  let rawQ : Finset (Fin d) × Finset (Fin b) → List Bool :=
    fun p => bitsF p.1 ++ bitsF p.2 ++ [false, true]
  have hwidthQ : ∀ p, (rawQ p).length = d + b + 2 := fun p => by simp [rawQ, bitsF_length]; omega
  let q0 : MNet (d + b + 2) := MNet.empty (d + b + 2)
  have q0_varX : ∀ v : Fin d, q0.has rawQ (fun p => decide (v ∈ p.1)) := fun v => by
    refine ⟨v.val, by simp [q0, MNet.empty]; omega, fun p => ?_⟩
    change (bitsF p.1 ++ bitsF p.2 ++ [false, true]).getD v.val false = decide (v ∈ p.1)
    rw [List.getD_append _ _ _ _ (by simp [bitsF_length]; omega),
      List.getD_append _ _ _ _ (by rw [bitsF_length]; exact v.isLt), bitsF_getD]
  have q0_varZ : ∀ k : Fin b, q0.has rawQ (fun p => decide (k ∈ p.2)) := fun k => by
    refine ⟨d + k.val, by simp [q0, MNet.empty]; omega, fun p => ?_⟩
    change (bitsF p.1 ++ bitsF p.2 ++ [false, true]).getD (d + k.val) false = decide (k ∈ p.2)
    rw [List.getD_append _ _ _ _ (by simp [bitsF_length]),
      List.getD_append_right _ _ _ _ (by rw [bitsF_length]; omega), bitsF_length]
    simpa [Nat.add_sub_cancel_left] using bitsF_getD p.2 k
  have q0_false : q0.has rawQ (fun _ => false) := by
    refine ⟨d + b, by simp [q0, MNet.empty], fun p => ?_⟩
    change (bitsF p.1 ++ bitsF p.2 ++ [false, true]).getD (d + b) false = false
    rw [List.getD_append_right _ _ _ _ (by simp [bitsF_length])]
    simp [bitsF_length]
  have q0_true : q0.has rawQ (fun _ => true) := by
    refine ⟨d + b + 1, by simp [q0, MNet.empty], fun p => ?_⟩
    change (bitsF p.1 ++ bitsF p.2 ++ [false, true]).getD (d + b + 1) false = true
    rw [List.getD_append_right _ _ _ _ (by simp [bitsF_length])]
    simp [bitsF_length]
  let decF : Fin a → Finset (Fin d) × Finset (Fin b) → Bool :=
    fun u p => decide (∃ i : Fin m, u ∈ Y i ∧ X i ⊆ p.1 ∧ (high i \ p.2).card ≤ down i)
  obtain ⟨qQ, _hqQ_ext, hqQ_has⟩ := MNet.buildAll q0 (List.finRange a) decF (by
    intro u _ r hr
    let rows : List (Fin m) := (List.finRange m).filter (fun i => decide (u ∈ Y i))
    let rowF : Fin m → Finset (Fin d) × Finset (Fin b) → Bool :=
      fun i p => decide (X i ⊆ p.1 ∧ (high i \ p.2).card ≤ down i)
    obtain ⟨r1, hr1, hrows⟩ := MNet.buildAll r rows rowF (by
      intro i _ r' hr'

      obtain ⟨r2, hr2, hXi⟩ := MNet.allList hwidthQ r' (hr' _ (hr _ q0_true)) (X i).toList
        (fun v p => decide (v ∈ p.1)) (fun v _ => hr' _ (hr _ (q0_varX v)))

      let goodA : List (Finset (Fin b)) :=
        ((Finset.univ : Finset (Finset (Fin b))).filter (fun A => (high i \ A).card ≤ down i)).toList
      let termA : Finset (Fin b) → Finset (Fin d) × Finset (Fin b) → Bool :=
        fun A p => decide (A ⊆ p.2)
      obtain ⟨r3, hr3, hAs⟩ := MNet.buildAll r2 goodA termA (by
        intro A _ t ht
        obtain ⟨t1, ht1, hallA⟩ := MNet.allList hwidthQ t (ht _ (hr2 _ (hr' _ (hr _ q0_true))))
          A.toList (fun k p => decide (k ∈ p.2)) (fun k _ => ht _ (hr2 _ (hr' _ (hr _ (q0_varZ k)))))
        refine ⟨t1, ht1, ?_⟩
        convert hallA using 2 with p
        apply Bool.eq_iff_iff.mpr
        simp only [termA, List.all_eq_true, Finset.mem_toList, decide_eq_true_eq]
        exact Finset.subset_iff)
      obtain ⟨r4, hr4, hanyA⟩ := MNet.anyList hwidthQ r3
        (hr3 _ (hr2 _ (hr' _ (hr _ q0_false)))) goodA termA hAs
      obtain ⟨r5, hr5, hboth⟩ := MNet.binary hwidthQ r4 _ _
        (hr4 _ (hr3 _ hXi)) hanyA true
      refine ⟨r5, MNet.ext_trans (MNet.ext_trans (MNet.ext_trans hr2 hr3) hr4) hr5, ?_⟩
      convert hboth using 2 with p
      apply Bool.eq_iff_iff.mpr
      simp only [rowF, goodA, termA, ite_true, Bool.and_eq_true, List.all_eq_true,
        List.any_eq_true, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and,
        decide_eq_true_eq]
      constructor
      · rintro ⟨hsubX, hcard⟩
        exact ⟨fun v hv => hsubX hv, p.2, hcard, Finset.Subset.refl _⟩
      · rintro ⟨hsubX, A, hAcard, hAsub⟩
        refine ⟨fun v hv => hsubX v hv, le_trans (Finset.card_le_card ?_) hAcard⟩
        intro k hk
        obtain ⟨hk1, hk2⟩ := Finset.mem_sdiff.mp hk
        exact Finset.mem_sdiff.mpr ⟨hk1, fun hkA => hk2 (hAsub hkA)⟩)
    obtain ⟨r2, hr2, hany⟩ := MNet.anyList hwidthQ r1 (hr1 _ (hr _ q0_false)) rows rowF hrows
    refine ⟨r2, MNet.ext_trans hr1 hr2, ?_⟩
    convert hany using 2 with p
    apply Bool.eq_iff_iff.mpr
    simp only [decF, rows, rowF, List.any_eq_true, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq])
  let Q : Circuit := ⟨qQ.gates, 0⟩
  have ho_ex : ∀ u : Fin a, ∃ idx < d + b + 2 + Q.size,
      ∀ p, (Q.wires (rawQ p)).getD idx false = decF u p := fun u =>
    hqQ_has u (List.mem_finRange u)
  let o : Fin a → Nat := fun u => Classical.choose (ho_ex u)
  have ho_lt : ∀ u, o u < d + b + 2 + Q.size := fun u => (Classical.choose_spec (ho_ex u)).1
  have ho_eval : ∀ u p, (Q.wires (rawQ p)).getD (o u) false = decF u p :=
    fun u p => (Classical.choose_spec (ho_ex u)).2 p
  refine ⟨P, Q, s, o, pP.mono, qQ.mono, pP.readsBack, qQ.readsBack, hs_lt, ho_lt, ?_⟩
  intro j z hjz hzj u
  change (Q.wires (rawQ (X j, z))).getD (o u) false = decide (u ∈ Y j)
  rw [ho_eval u (X j, z)]
  apply Bool.eq_iff_iff.mpr
  simp only [decF, decide_eq_true_eq]
  constructor
  · rintro ⟨i, huYi, hXij, hiz⟩
    by_contra huYj
    have hnotSub : ¬ Y i ⊆ Y j := fun hsub => huYj (hsub huYi)
    have hgap := hmono_h i j hXij
    rw [ite_eq_right hnotSub] at hgap
    have hhi_sub : high j ⊆ high i := by
      intro k hk
      exact (hhigh_eq i k).mpr (by have := (hhigh_eq j k).mp hk; omega)
    have hdiff_sub : high i \ high j ⊆ (high i \ z) ∪ (z \ high j) := by
      intro k hk
      obtain ⟨hki, hkj⟩ := Finset.mem_sdiff.mp hk
      by_cases hkz : k ∈ z
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hkz, hkj⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hki, hkz⟩)
    have h1 := Finset.card_le_card hdiff_sub
    have h2 := Finset.card_union_le (high i \ z) (z \ high j)
    rw [Finset.card_sdiff_of_subset hhi_sub, hhigh_card i, hhigh_card j] at h1
    change (z \ high j).card ≤ up j at hzj
    have := hle_b i
    have := hle_b j
    omega
  · intro huYj
    exact ⟨j, huYj, Finset.Subset.refl _, hjz⟩

theorem main (m d a b : Nat) (X : Fin m → Finset (Fin d)) (Y : Fin m → Finset (Fin a))
    (down up : Fin m → Nat) :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    let bits := fun {n : Nat} (s : Finset (Fin n)) => List.ofFn (fun j => decide (j ∈ s))
    (∃ (P Q : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin b → Nat) (o : Fin a → Nat),
      let high := fun i => (Finset.univ : Finset (Fin b)).filter (fun j =>
        (P.wires (bits (X i) ++ [false, true])).getD (s j) false = false)
      PEqualNP.MetaComplexity.Monotone2 P ∧ PEqualNP.MetaComplexity.Monotone2 Q ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) P ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + b + 2) Q ∧
      (∀ j, s j < d + 2 + P.size) ∧ (∀ j, o j < d + b + 2 + Q.size) ∧
      ∀ i (z : Finset (Fin b)), (high i \ z).card ≤ down i → (z \ high i).card ≤ up i →
        ∀ j, (Q.wires (bits (X i) ++ bits z ++ [false, true])).getD (o j) false = decide (j ∈ Y i)) ↔
    ∃ h : Fin m → Nat, (∀ i, h i ≤ b) ∧ ∀ i j, X i ⊆ X j →
      h i + (if Y i ⊆ Y j then 0 else down i + up j + 1) ≤ h j := by
  have hiff := Iff.intro (fwd m d a b X Y down up) (bwd m d a b X Y down up)
  have hbits_eq : ∀ {n : Nat} (dp : ∀ P : Prop, Decidable P) (s : Finset (Fin n)),
      List.ofFn (fun j : Fin n => @decide (j ∈ s) (dp _)) = bitsF s := fun dp s => by
    apply List.ext_getElem (by simp [bitsF])
    intro i hi1 hi2
    simp only [bitsF, List.getElem_ofFn]
    exact congrArg (@decide _) (Subsingleton.elim _ _)
  have hcard_sdiff_eq : ∀ (d1 d2 : DecidableEq (Fin b)) (s t : Finset (Fin b)),
      (@SDiff.sdiff _ (@Finset.instSDiff _ d1) s t).card =
      (@SDiff.sdiff _ (@Finset.instSDiff _ d2) s t).card :=
    fun _ _ s t => congrArg Finset.card (by ext x; simp)
  have hhigh_eq : ∀ (P : Circuit) (s : Fin b → Nat) (i : Fin m),
      @Finset.filter (Fin b)
        (fun j => (P.wires (List.ofFn (fun k : Fin d => @decide (k ∈ X i) (Classical.propDecidable _)) ++ [false, true])).getD (s j) false = false)
        (fun j => Classical.propDecidable _) Finset.univ =
      (Finset.univ : Finset (Fin b)).filter (fun j =>
        (P.wires (bitsF (X i) ++ [false, true])).getD (s j) false = false) := by
    intro P s i
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hbits_eq]
  constructor
  · rintro ⟨P, Q, s, o, h1, h2, h3, h4, h5, h6, h7⟩
    obtain ⟨h, hle, hstep⟩ := hiff.mp ⟨P, Q, s, o, h1, h2, h3, h4, h5, h6, by
      intro i z hiz hzi j
      have hiz' := hiz
      dsimp only at hiz'
      rw [← hhigh_eq P s i, ← hcard_sdiff_eq (fun x y => Classical.propDecidable (x = y)) _] at hiz'
      have hzi' := hzi
      dsimp only at hzi'
      rw [← hhigh_eq P s i, ← hcard_sdiff_eq (fun x y => Classical.propDecidable (x = y)) _] at hzi'
      have := h7 i z hiz' hzi' j
      dsimp only at this
      rw [hbits_eq, hbits_eq] at this
      exact this.trans (congrArg (@decide _) (Subsingleton.elim _ _))⟩
    refine ⟨h, hle, fun i j hX => ?_⟩
    have := hstep i j hX
    by_cases hY : Y i ⊆ Y j
    · simpa [ite_eq_left hY] using this
    · simpa [ite_eq_right hY] using this
  · rintro ⟨h, hle, hstep⟩
    have hstep' : ∀ i j, X i ⊆ X j → h i + (if Y i ⊆ Y j then 0 else down i + up j + 1) ≤ h j := by
      intro i j hX
      have := hstep i j hX
      by_cases hY : Y i ⊆ Y j
      · simpa [ite_eq_left hY] using this
      · simpa [ite_eq_right hY] using this
    obtain ⟨P, Q, s, o, h1, h2, h3, h4, h5, h6, h7⟩ := hiff.mpr ⟨h, hle, hstep'⟩
    refine ⟨P, Q, s, o, h1, h2, h3, h4, h5, h6, ?_⟩
    intro i z hiz hzi j
    have hiz' := hiz
    dsimp only at hiz'
    rw [hhigh_eq P s i, hcard_sdiff_eq _ (inferInstance : DecidableEq (Fin b))] at hiz'
    have hzi' := hzi
    dsimp only at hzi'
    rw [hhigh_eq P s i, hcard_sdiff_eq _ (inferInstance : DecidableEq (Fin b))] at hzi'
    have := h7 i z hiz' hzi' j
    dsimp only
    rw [hbits_eq, hbits_eq]
    exact this.trans (congrArg (@decide _) (Subsingleton.elim _ _))

end PEqualNP.Outside.L_meta_53185_aux

theorem PEqualNP.Outside.L_meta_53185 : (∀ (m d a b : Nat) (X : Fin m → Finset (Fin d)) (Y : Fin m → Finset (Fin a))
  (down up : Fin m → Nat),
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  let bits := fun {n : Nat} (s : Finset (Fin n)) => List.ofFn (fun j => decide (j ∈ s))
  (∃ (P Q : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin b → Nat) (o : Fin a → Nat),
    let high := fun i => (Finset.univ : Finset (Fin b)).filter (fun j =>
      (P.wires (bits (X i) ++ [false,true])).getD (s j) false = false)
    PEqualNP.MetaComplexity.Monotone2 P ∧ PEqualNP.MetaComplexity.Monotone2 Q ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (d+2) P ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (d+b+2) Q ∧
    (∀ j, s j < d+2+P.size) ∧ (∀ j, o j < d+b+2+Q.size) ∧
    ∀ i (z : Finset (Fin b)), (high i \ z).card ≤ down i → (z \ high i).card ≤ up i →
      ∀ j, (Q.wires (bits (X i) ++ bits z ++ [false,true])).getD (o j) false = decide (j ∈ Y i)) ↔
  ∃ h : Fin m → Nat, (∀ i, h i ≤ b) ∧ ∀ i j, X i ⊆ X j →
    h i + (if Y i ⊆ Y j then 0 else down i + up j + 1) ≤ h j) :=
  PEqualNP.Outside.L_meta_53185_aux.main
