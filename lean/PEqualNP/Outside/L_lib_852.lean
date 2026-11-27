import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_lib_852

def step {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (x : Option (Fin s)) (bit : Bool) :
    Option (Fin s) :=
  x.bind (fun i => n i bit)

def runList {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (u : Fin s) (l : List Bool) :
    Option (Fin s) :=
  l.foldl (step n) (some u)

def runFrom {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (u : Fin s) (b : ℕ) (w : Fin b → Bool) :
    Option (Fin s) :=
  (List.ofFn w).foldl (step n) (some u)

def Reach {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (u v : Fin s) : Prop :=
  ∃ l : List Bool, runList n u l = some v

def ReachPos {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (u v : Fin s) : Prop :=
  ∃ l : List Bool, l ≠ [] ∧ runList n u l = some v

def InfState {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (u : Fin s) : Prop :=
  ∀ k : ℕ, ∃ l : List Bool, l.length = k ∧ (runList n u l).isSome

lemma foldl_step_none {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (l : List Bool) :
    l.foldl (step n) none = none := by
  induction l with
  | nil => rfl
  | cons a t ih => exact ih

lemma runList_nil {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (u : Fin s) :
    runList n u [] = some u := rfl

lemma runList_cons {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (u : Fin s) (bit : Bool)
    (l : List Bool) :
    runList n u (bit :: l) = (n u bit).bind (fun v => runList n v l) := by
  unfold runList
  simp only [List.foldl_cons, step, Option.bind_some]
  cases h : n u bit with
  | none => exact foldl_step_none n l
  | some v => rfl

lemma runList_append {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (u : Fin s)
    (l1 l2 : List Bool) :
    runList n u (l1 ++ l2) = (runList n u l1).bind (fun v => runList n v l2) := by
  induction l1 generalizing u with
  | nil => simp [runList_nil]
  | cons bit t ih =>
    rw [List.cons_append, runList_cons, runList_cons]
    cases h : n u bit with
    | none => rfl
    | some v => exact ih v

lemma runList_replicate_flatten {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (u : Fin s)
    (p : List Bool) (hp : runList n u p = some u) (r : ℕ) :
    runList n u (List.replicate r p).flatten = some u := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [List.replicate_succ, List.flatten_cons, runList_append, hp, Option.bind_some, ih]

lemma runList_take_isSome {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (u : Fin s)
    (l : List Bool) (k : ℕ) (h : (runList n u l).isSome) :
    (runList n u (l.take k)).isSome := by
  have hsplit : l.take k ++ l.drop k = l := List.take_append_drop k l
  rw [← hsplit, runList_append] at h
  cases h1 : runList n u (l.take k) with
  | none => rw [h1] at h; simp at h
  | some _ => rfl

lemma reach_refl {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (u : Fin s) : Reach n u u :=
  ⟨[], rfl⟩

lemma reach_trans {s : ℕ} (n : Fin s → Bool → Option (Fin s)) {u v w : Fin s}
    (h1 : Reach n u v) (h2 : Reach n v w) : Reach n u w := by
  obtain ⟨l1, hl1⟩ := h1
  obtain ⟨l2, hl2⟩ := h2
  exact ⟨l1 ++ l2, by rw [runList_append, hl1, Option.bind_some, hl2]⟩

lemma reach_step {s : ℕ} (n : Fin s → Bool → Option (Fin s)) {u v : Fin s} {bit : Bool}
    (h : n u bit = some v) : Reach n u v :=
  ⟨[bit], by rw [runList_cons, h]; rfl⟩

lemma reachPos_of_step_reach {s : ℕ} (n : Fin s → Bool → Option (Fin s)) {u v w : Fin s}
    {bit : Bool} (h1 : n u bit = some v) (h2 : Reach n v w) : ReachPos n u w := by
  obtain ⟨l, hl⟩ := h2
  exact ⟨bit :: l, List.cons_ne_nil _ _, by rw [runList_cons, h1, Option.bind_some, hl]⟩

lemma inf_of_step {s : ℕ} (n : Fin s → Bool → Option (Fin s)) {u v : Fin s} {bit : Bool}
    (h : n u bit = some v) (hv : InfState n v) : InfState n u := by
  intro k
  cases k with
  | zero => exact ⟨[], rfl, rfl⟩
  | succ k =>
    obtain ⟨l, hl, hs⟩ := hv k
    refine ⟨bit :: l, by simp [hl], ?_⟩
    rw [runList_cons, h, Option.bind_some]
    exact hs

lemma inf_of_reachPos_self {s : ℕ} (n : Fin s → Bool → Option (Fin s)) {u : Fin s}
    (h : ReachPos n u u) : InfState n u := by
  obtain ⟨p, hpne, hp⟩ := h
  have hplen : 1 ≤ p.length := Nat.succ_le_of_lt (List.length_pos_of_ne_nil hpne)
  intro k
  let big := (List.replicate k p).flatten
  have hlen : k ≤ big.length := by
    have hb : big.length = k * p.length := by simp [big]
    rw [hb]
    exact Nat.le_mul_of_pos_right k (by omega)
  have hsome : (runList n u big).isSome := by
    rw [runList_replicate_flatten n u p hp k]
    rfl
  exact ⟨big.take k, by simp [hlen], runList_take_isSome n u big k hsome⟩

lemma getD_append_at_length (a b : List Bool) (d : Bool) :
    (a ++ b).getD a.length d = b.getD 0 d := by
  induction a with
  | nil => rfl
  | cons x t ih => exact ih

lemma ofFn_getD_eq {b : ℕ} (l : List Bool) (hl : l.length = b) :
    List.ofFn (fun i : Fin b => l.getD i.val false) = l := by
  apply List.ext_getElem
  · simp [hl]
  · intro i h1 h2
    simp [List.getElem?_eq_getElem h2]

lemma unique_inf_step {s : ℕ} (z : Fin s) (n : Fin s → Bool → Option (Fin s)) (K : ℕ)
    (hlive : ∀ B : ℕ, ∃ b ≥ B,
      ((Finset.univ : Finset (Fin b → Bool)).filter (fun w => (runFrom n z b w).isSome)).card ≤ K)
    {u : Fin s} (hzu : Reach n z u) (hcyc : ReachPos n u u)
    {b1 b2 : Bool} {v1 v2 : Fin s}
    (h1 : n u b1 = some v1) (hi1 : InfState n v1)
    (h2 : n u b2 = some v2) (hi2 : InfState n v2) :
    b1 = b2 := by
  by_contra hne
  obtain ⟨p0, hp0⟩ := hzu
  obtain ⟨cyc, hcyc_ne, hcyc_run⟩ := hcyc
  cases cyc with
  | nil => exact hcyc_ne rfl
  | cons cbit crest =>
    have hother : ∃ v_other : Fin s, n u (!cbit) = some v_other ∧ InfState n v_other := by
      cases hc : cbit <;> cases hb1 : b1 <;> cases hb2 : b2 <;> simp_all
    obtain ⟨v_other, hv_other, hinf_other⟩ := hother
    let cyc := cbit :: crest
    obtain ⟨b, hb_ge, hb_le⟩ := hlive (p0.length + K * cyc.length + 1)
    have hex : ∀ r : Fin (K + 1), ∃ l : List Bool,
        l.length = b ∧
        (runList n z l).isSome ∧
        ∃ tail : List Bool, l = p0 ++ (List.replicate r.val cyc).flatten ++ [!cbit] ++ tail := by
      intro r
      have hr : p0.length + r.val * cyc.length + 1 ≤ b := by
        have h1 : r.val ≤ K := Nat.lt_succ_iff.mp r.isLt
        have h2 : r.val * cyc.length ≤ K * cyc.length := Nat.mul_le_mul_right _ h1
        omega
      let rem := b - (p0.length + r.val * cyc.length + 1)
      obtain ⟨tail, htail_len, htail_some⟩ := hinf_other rem
      let l := p0 ++ (List.replicate r.val cyc).flatten ++ [!cbit] ++ tail
      refine ⟨l, ?_, ?_, tail, rfl⟩
      · simp [l, htail_len, rem]
        omega
      · simp only [l]
        rw [runList_append, runList_append, runList_append, hp0, Option.bind_some,
          runList_replicate_flatten n u cyc hcyc_run r.val, Option.bind_some,
          runList_cons, hv_other, Option.bind_some, runList_nil, Option.bind_some]
        exact htail_some
    choose fL hfL_len hfL_some hfL_eq using hex
    let fW : Fin (K + 1) → (Fin b → Bool) := fun r i => (fL r).getD i.val false
    have hfW_ne_of_lt : ∀ (r1 r2 : Fin (K + 1)), r1.val < r2.val → fW r1 ≠ fW r2 := by
      intro r1 r2 hlt heq
      obtain ⟨t1, ht1⟩ := hfL_eq r1
      obtain ⟨t2, ht2⟩ := hfL_eq r2
      let idx := p0.length + r1.val * cyc.length
      have hidx : idx < b := by
        have h1 : r1.val ≤ K := Nat.lt_succ_iff.mp r1.isLt
        have h2 : r1.val * cyc.length ≤ K * cyc.length := Nat.mul_le_mul_right _ h1
        omega
      have hlen1 : (p0 ++ (List.replicate r1.val cyc).flatten).length = idx := by simp [idx]
      have hget1 : fW r1 ⟨idx, hidx⟩ = !cbit := by
        change (fL r1).getD idx false = !cbit
        rw [ht1, List.append_assoc, ← hlen1, getD_append_at_length]
        rfl
      have hget2 : fW r2 ⟨idx, hidx⟩ = cbit := by
        have hr2 : r2.val = r1.val + (1 + (r2.val - r1.val - 1)) := by omega
        have hrep : (List.replicate r2.val cyc).flatten =
            (List.replicate r1.val cyc).flatten ++ cyc ++ (List.replicate (r2.val - r1.val - 1) cyc).flatten := by
          rw [hr2, List.replicate_add, List.flatten_append, List.replicate_add, List.flatten_append]
          simp [List.append_assoc]
        change (fL r2).getD idx false = cbit
        rw [ht2, hrep]
        have hassoc : p0 ++ ((List.replicate r1.val cyc).flatten ++ cyc ++ (List.replicate (r2.val - r1.val - 1) cyc).flatten) ++ [!cbit] ++ t2 =
            (p0 ++ (List.replicate r1.val cyc).flatten) ++ (cyc ++ (List.replicate (r2.val - r1.val - 1) cyc).flatten ++ [!cbit] ++ t2) := by
          simp [List.append_assoc]
        rw [hassoc, ← hlen1, getD_append_at_length]
        rfl
      have hsame : fW r1 ⟨idx, hidx⟩ = fW r2 ⟨idx, hidx⟩ := congrFun heq ⟨idx, hidx⟩
      rw [hget1, hget2] at hsame
      cases cbit <;> simp at hsame
    have hfW_inj : Function.Injective fW := by
      intro r1 r2 heq
      by_contra hne_r
      rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne_r) with hlt | hlt
      · exact hfW_ne_of_lt r1 r2 hlt heq
      · exact hfW_ne_of_lt r2 r1 hlt heq.symm
    have hsub : (Finset.univ : Finset (Fin (K + 1))).image fW ⊆
        (Finset.univ : Finset (Fin b → Bool)).filter (fun w => (runFrom n z b w).isSome) := by
      intro w hw
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
      obtain ⟨r, rfl⟩ := hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      unfold runFrom
      rw [ofFn_getD_eq (fL r) (hfL_len r)]
      exact hfL_some r
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hfW_inj, Finset.card_univ, Fintype.card_fin] at hcard
    omega

lemma cycle_decomp {s : ℕ} (next : Fin s → Fin s) (S : Finset (Fin s))
    (hclosed : ∀ u ∈ S, next u ∈ S)
    (hper : ∀ u ∈ S, ∃ k, 0 < k ∧ next^[k] u = u) :
    ∃ (m : ℕ) (l : Fin m → ℕ) (node : (i : Fin m) → Fin (l i) → Fin s),
      (∑ i, l i = S.card) ∧
      (∀ i, 0 < l i ∧ Function.Injective (node i)) ∧
      (∀ i j a b, node i a = node j b → i = j) ∧
      (∀ i a, node i a ∈ S) ∧
      (∀ u ∈ S, ∃ i a, node i a = u) ∧
      (∀ i a, ∃ b : Fin (l i), b.val = (a.val + 1) % l i ∧ next (node i a) = node i b) := by
  classical
  induction hcard : S.card using Nat.strong_induction_on generalizing S with
  | _ c ih =>
    by_cases hS : S = ∅
    · subst hS
      have hc : c = 0 := by simpa using hcard.symm
      subst hc
      refine ⟨0, Fin.elim0, fun i => i.elim0, by simp, ?_, ?_, ?_, ?_, ?_⟩
      · intro i; exact i.elim0
      · intro i; exact i.elim0
      · intro i; exact i.elim0
      · intro u hu; simp at hu
      · intro i; exact i.elim0
    · obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      have huper := hper u hu
      let k0 := Nat.find huper
      have hk0_spec : 0 < k0 ∧ next^[k0] u = u := Nat.find_spec huper
      have hk0_pos : 0 < k0 := hk0_spec.1
      have hk0_eq : next^[k0] u = u := hk0_spec.2
      have hk0_min : ∀ k, 0 < k → k < k0 → next^[k] u ≠ u := by
        intro k hkp hkl heq
        exact Nat.find_min huper hkl ⟨hkp, heq⟩
      have hiter_mem : ∀ r : ℕ, next^[r] u ∈ S := by
        intro r
        induction r with
        | zero => exact hu
        | succ r ihr =>
          rw [Function.iterate_succ_apply']
          exact hclosed _ ihr
      have hiter_mod : ∀ r : ℕ, next^[r] u = next^[r % k0] u := by
        intro r
        have hdiv : r = k0 * (r / k0) + r % k0 := (Nat.div_add_mod r k0).symm
        conv_lhs => rw [hdiv, add_comm, Function.iterate_add_apply]
        have hmul : ∀ q : ℕ, next^[k0 * q] u = u := by
          intro q
          induction q with
          | zero => simp
          | succ q ihq =>
            rw [Nat.mul_succ, Function.iterate_add_apply, hk0_eq, ihq]
        rw [hmul]
      let f0 : Fin k0 → Fin s := fun a => next^[a.val] u
      have hf0_ne_of_lt : ∀ (a b : Fin k0), a.val < b.val → f0 a ≠ f0 b := by
        intro a b hlt hab
        have hstep : next^[k0 - b.val + a.val] u = u := by
          rw [Function.iterate_add_apply]
          change next^[k0 - b.val] (f0 a) = u
          rw [hab]
          change next^[k0 - b.val] (next^[b.val] u) = u
          rw [← Function.iterate_add_apply]
          have hsum : k0 - b.val + b.val = k0 := by omega
          rw [hsum, hk0_eq]
        exact hk0_min (k0 - b.val + a.val) (by omega) (by omega) hstep
      have hf0_inj : Function.Injective f0 := by
        intro a b hab
        by_contra hne
        rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
        · exact hf0_ne_of_lt a b hlt hab
        · exact hf0_ne_of_lt b a hlt hab.symm
      let orb : Finset (Fin s) := Finset.univ.image f0
      have horb_sub : orb ⊆ S := by
        intro x hx
        simp only [orb, Finset.mem_image, Finset.mem_univ, true_and] at hx
        obtain ⟨a, rfl⟩ := hx
        exact hiter_mem a.val
      have horb_card : orb.card = k0 := by
        rw [Finset.card_image_of_injective _ hf0_inj, Finset.card_univ, Fintype.card_fin]
      let S' := S \ orb
      have hS'_card_eq : S'.card = S.card - k0 := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr horb_sub, horb_card]
      have hS'_card : S'.card < c := by
        have hle := Finset.card_le_card horb_sub
        omega
      have hS'_closed : ∀ v ∈ S', next v ∈ S' := by
        intro v hv
        simp only [S', Finset.mem_sdiff] at hv ⊢
        refine ⟨hclosed v hv.1, ?_⟩
        intro hnv
        simp only [orb, Finset.mem_image, Finset.mem_univ, true_and] at hnv
        obtain ⟨a, ha⟩ := hnv
        obtain ⟨r, hr_pos, hr_eq⟩ := hper v hv.1
        have hv_eq : v = next^[r - 1 + a.val] u := by
          have hr1 : r = (r - 1) + 1 := by omega
          have h1 : next^[r] v = next^[r - 1] (next v) := by
            conv_lhs => rw [hr1, Function.iterate_add_apply, Function.iterate_one]
          rw [← hr_eq, h1, ← ha, ← Function.iterate_add_apply]
        rw [hiter_mod] at hv_eq
        apply hv.2
        simp only [orb, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨⟨(r - 1 + a.val) % k0, Nat.mod_lt _ hk0_pos⟩, hv_eq.symm⟩
      have hS'_per : ∀ v ∈ S', ∃ k, 0 < k ∧ next^[k] v = v := fun v hv =>
        hper v (Finset.sdiff_subset hv)
      obtain ⟨m', l', node', hsum', hpos', hdisj', hmem', hcov', hstep'⟩ :=
        ih S'.card hS'_card S' hS'_closed hS'_per rfl
      let l : Fin (m' + 1) → ℕ := Fin.cases k0 l'
      let node : (i : Fin (m' + 1)) → Fin (l i) → Fin s :=
        Fin.cases (motive := fun i => Fin (l i) → Fin s) f0 node'
      refine ⟨m' + 1, l, node, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Fin.sum_univ_succ]
        simp only [l, Fin.cases_zero, Fin.cases_succ]
        rw [hsum', hS'_card_eq]
        have hle := Finset.card_le_card horb_sub
        omega
      · intro i
        refine Fin.cases ?_ ?_ i
        · exact ⟨hk0_pos, hf0_inj⟩
        · intro j; exact hpos' j
      · intro i j
        refine Fin.cases ?_ ?_ i
        · refine Fin.cases ?_ ?_ j
          · intro _ _ _; rfl
          · intro j' a b hab
            exfalso
            have hm1 : node 0 a ∈ orb := by
              simp only [orb, Finset.mem_image, Finset.mem_univ, true_and]
              exact ⟨a, rfl⟩
            have hm2 : node j'.succ b ∈ S' := hmem' j' b
            rw [← hab] at hm2
            exact (Finset.mem_sdiff.mp hm2).2 hm1
        · intro i'
          refine Fin.cases ?_ ?_ j
          · intro a b hab
            exfalso
            have hm1 : node i'.succ a ∈ S' := hmem' i' a
            have hm2 : node 0 b ∈ orb := by
              simp only [orb, Finset.mem_image, Finset.mem_univ, true_and]
              exact ⟨b, rfl⟩
            rw [hab] at hm1
            exact (Finset.mem_sdiff.mp hm1).2 hm2
          · intro j' a b hab
            exact congrArg Fin.succ (hdisj' i' j' a b hab)
      · intro i
        refine Fin.cases ?_ ?_ i
        · intro a; exact hiter_mem a.val
        · intro j a; exact Finset.sdiff_subset (hmem' j a)
      · intro v hv
        by_cases hvo : v ∈ orb
        · simp only [orb, Finset.mem_image, Finset.mem_univ, true_and] at hvo
          obtain ⟨a, ha⟩ := hvo
          exact ⟨0, a, ha⟩
        · obtain ⟨j, a, ha⟩ := hcov' v (Finset.mem_sdiff.mpr ⟨hv, hvo⟩)
          exact ⟨j.succ, a, ha⟩
      · intro i
        refine Fin.cases ?_ ?_ i
        · intro a
          refine ⟨⟨(a.val + 1) % k0, Nat.mod_lt _ hk0_pos⟩, rfl, ?_⟩
          change next (next^[a.val] u) = next^[(a.val + 1) % k0] u
          rw [← Function.iterate_succ_apply' next a.val u, hiter_mod]
        · intro j a
          exact hstep' j a

lemma cycle_walk {s : ℕ} (n : Fin s → Bool → Option (Fin s)) {len : ℕ}
    (u : Fin len → Fin s)
    (hstep : ∀ a : Fin len, ∃ (bit : Bool) (b : Fin len),
      b.val = (a.val + 1) % len ∧ n (u a) bit = some (u b))
    (a0 : Fin len) (k : ℕ) :
    ∃ (l : List Bool) (a1 : Fin len), l.length = k ∧ runList n (u a0) l = some (u a1) := by
  induction k generalizing a0 with
  | zero => exact ⟨[], a0, rfl, rfl⟩
  | succ k ih =>
    obtain ⟨bit, b, _, hnb⟩ := hstep a0
    obtain ⟨l, a1, hlen_l, hrun_l⟩ := ih b
    refine ⟨bit :: l, a1, by simp [hlen_l], ?_⟩
    rw [runList_cons, hnb, Option.bind_some, hrun_l]

lemma dag_int_bound {s : ℕ} (n : Fin s → Bool → Option (Fin s))
    (g : Fin s → Bool → ℤ) (v : Fin s → ℝ)
    (hbell : ∀ i, 2 * v i = ∑ bit : Bool, (n i bit).elim (g i bit : ℝ) v)
    (D : Finset (Fin s)) (reachSet : Fin s → Finset (Fin s))
    (hreachSet : ∀ u w, w ∈ reachSet u ↔ w ∈ D ∧ Reach n u w)
    (base M : ℕ)
    (hacyc : ∀ u ∈ D, ¬ ReachPos n u u)
    (hout : ∀ u ∈ D, ∀ bit : Bool, ∀ w : Fin s,
      n u bit = some w → w ∉ D → ∃ t : ℤ, ((2 ^ base * M : ℕ) : ℝ) * v w = t) :
    ∀ (k : ℕ) (u : Fin s), u ∈ D →
      (reachSet u).card ≤ k →
      ∃ t : ℤ, ((2 ^ (base + k) * M : ℕ) : ℝ) * v u = t := by
  intro k
  induction k with
  | zero =>
    intro u hu hcard
    have hmem : u ∈ reachSet u := (hreachSet u u).mpr ⟨hu, reach_refl n u⟩
    have hpos : 0 < (reachSet u).card := Finset.card_pos.mpr ⟨u, hmem⟩
    omega
  | succ k ih =>
    intro u hu hcard
    have hterm : ∀ bit : Bool, ∃ t : ℤ,
        ((2 ^ (base + k) * M : ℕ) : ℝ) * (n u bit).elim (g u bit : ℝ) v = t := by
      intro bit
      cases hnb : n u bit with
      | none =>
        refine ⟨(2 ^ (base + k) * M : ℕ) * g u bit, ?_⟩
        simp
      | some w =>
        simp only [Option.elim_some]
        by_cases hw : w ∈ D
        · have hss : reachSet w ⊂ reachSet u := by
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨?_, ?_⟩
            · intro y hy
              have hy' := (hreachSet w y).mp hy
              exact (hreachSet u y).mpr ⟨hy'.1, reach_trans n (reach_step n hnb) hy'.2⟩
            · intro heq
              have humem : u ∈ reachSet u := (hreachSet u u).mpr ⟨hu, reach_refl n u⟩
              rw [← heq] at humem
              have hwu : Reach n w u := ((hreachSet w u).mp humem).2
              exact hacyc u hu (reachPos_of_step_reach n hnb hwu)
          have hlt := Finset.card_lt_card hss
          exact ih w hw (by omega)
        · obtain ⟨t, ht⟩ := hout u hu bit w hnb hw
          refine ⟨(2 ^ k : ℕ) * t, ?_⟩
          have hpow : ((2 ^ (base + k) * M : ℕ) : ℝ) = ((2 ^ k : ℕ) : ℝ) * ((2 ^ base * M : ℕ) : ℝ) := by
            push_cast
            rw [pow_add]
            ring
          rw [hpow, mul_assoc, ht]
          push_cast
          ring
    obtain ⟨t0, ht0⟩ := hterm false
    obtain ⟨t1, ht1⟩ := hterm true
    refine ⟨t0 + t1, ?_⟩
    have hpow : ((2 ^ (base + (k + 1)) * M : ℕ) : ℝ) * v u =
        ((2 ^ (base + k) * M : ℕ) : ℝ) * (2 * v u) := by
      push_cast
      rw [← add_assoc, pow_succ]
      ring
    rw [hpow, hbell u, Fintype.sum_bool, mul_add, ht1, ht0]
    push_cast
    ring

lemma cycle_int_bound {s : ℕ} (n : Fin s → Bool → Option (Fin s))
    (g : Fin s → Bool → ℤ) (v : Fin s → ℝ)
    (hbell : ∀ i, 2 * v i = ∑ bit : Bool, (n i bit).elim (g i bit : ℝ) v)
    {len : ℕ} (hlen : 0 < len) (u : Fin len → Fin s) (f O : ℕ)
    (hdiv : (2 ^ len - 1) ∣ O)
    (hstep : ∀ a : Fin len, ∃ (bit : Bool) (b : Fin len),
      b.val = (a.val + 1) % len ∧ n (u a) bit = some (u b) ∧
      ∃ t : ℤ, ((2 ^ f : ℕ) : ℝ) * (n (u a) (!bit)).elim (g (u a) (!bit) : ℝ) v = t) :
    ∀ a : Fin len, ∃ t : ℤ, ((2 ^ f * O : ℕ) : ℝ) * v (u a) = t := by
  have htele : ∀ (k : ℕ) (_ : k ≤ len), ∃ t : ℤ,
      ((2 ^ f : ℕ) : ℝ) * (((2 ^ k : ℕ) : ℝ) * v (u ⟨0, hlen⟩) - v (u ⟨k % len, Nat.mod_lt _ hlen⟩)) = t := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨0, ?_⟩
      simp
    | succ k ih =>
      intro hk
      obtain ⟨tk, htk⟩ := ih (by omega)
      have hklt : k < len := by omega
      have hfin_k : (⟨k % len, Nat.mod_lt _ hlen⟩ : Fin len) = ⟨k, hklt⟩ :=
        Fin.ext (Nat.mod_eq_of_lt hklt)
      rw [hfin_k] at htk
      obtain ⟨bit, b, hbval, hnb, tc, htc⟩ := hstep ⟨k, hklt⟩
      have hbeq : b = ⟨(k + 1) % len, Nat.mod_lt _ hlen⟩ := Fin.ext hbval
      have hbell_k : 2 * v (u ⟨k, hklt⟩) =
          v (u ⟨(k + 1) % len, Nat.mod_lt _ hlen⟩) +
          (n (u ⟨k, hklt⟩) (!bit)).elim (g (u ⟨k, hklt⟩) (!bit) : ℝ) v := by
        have hb := hbell (u ⟨k, hklt⟩)
        have hsum : (∑ x : Bool, (n (u ⟨k, hklt⟩) x).elim (g (u ⟨k, hklt⟩) x : ℝ) v) =
            (n (u ⟨k, hklt⟩) bit).elim (g (u ⟨k, hklt⟩) bit : ℝ) v +
            (n (u ⟨k, hklt⟩) (!bit)).elim (g (u ⟨k, hklt⟩) (!bit) : ℝ) v := by
          cases bit <;> simp [add_comm]
        rw [hsum, hnb, Option.elim_some, hbeq] at hb
        exact hb
      refine ⟨2 * tk + tc, ?_⟩
      have hcalc : ((2 ^ f : ℕ) : ℝ) * (((2 ^ (k + 1) : ℕ) : ℝ) * v (u ⟨0, hlen⟩) -
            v (u ⟨(k + 1) % len, Nat.mod_lt _ hlen⟩)) =
          2 * (((2 ^ f : ℕ) : ℝ) * (((2 ^ k : ℕ) : ℝ) * v (u ⟨0, hlen⟩) - v (u ⟨k, hklt⟩))) +
          ((2 ^ f : ℕ) : ℝ) * (n (u ⟨k, hklt⟩) (!bit)).elim (g (u ⟨k, hklt⟩) (!bit) : ℝ) v := by
        have h1 : ((2 ^ (k + 1) : ℕ) : ℝ) = 2 * ((2 ^ k : ℕ) : ℝ) := by
          push_cast; rw [pow_succ]; ring
        rw [h1]
        have h2 : 2 * v (u ⟨k, hklt⟩) - v (u ⟨(k + 1) % len, Nat.mod_lt _ hlen⟩) =
            (n (u ⟨k, hklt⟩) (!bit)).elim (g (u ⟨k, hklt⟩) (!bit) : ℝ) v := by
          linarith
        rw [← h2]
        ring
      rw [hcalc, htk, htc]
      push_cast
      ring
  obtain ⟨tlen, htlen⟩ := htele len le_rfl
  have hfin_len : (⟨len % len, Nat.mod_lt _ hlen⟩ : Fin len) = ⟨0, hlen⟩ :=
    Fin.ext (Nat.mod_self len)
  rw [hfin_len] at htlen
  have h0_eq : ((2 ^ f * (2 ^ len - 1) : ℕ) : ℝ) * v (u ⟨0, hlen⟩) = tlen := by
    have hge1 : 1 ≤ 2 ^ len := Nat.one_le_two_pow
    have hcast : ((2 ^ f * (2 ^ len - 1) : ℕ) : ℝ) = ((2 ^ f : ℕ) : ℝ) * (((2 ^ len : ℕ) : ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub hge1, Nat.cast_one]
    rw [hcast]
    have hsub : ((2 ^ f : ℕ) : ℝ) * (((2 ^ len : ℕ) : ℝ) - 1) * v (u ⟨0, hlen⟩) =
        ((2 ^ f : ℕ) : ℝ) * (((2 ^ len : ℕ) : ℝ) * v (u ⟨0, hlen⟩) - v (u ⟨0, hlen⟩)) := by ring
    rw [hsub, htlen]
  obtain ⟨q, hq⟩ := hdiv
  have hO0 : ∃ t0 : ℤ, ((2 ^ f * O : ℕ) : ℝ) * v (u ⟨0, hlen⟩) = t0 := by
    refine ⟨(q : ℤ) * tlen, ?_⟩
    rw [hq]
    have hcast : ((2 ^ f * ((2 ^ len - 1) * q) : ℕ) : ℝ) =
        ((q : ℕ) : ℝ) * ((2 ^ f * (2 ^ len - 1) : ℕ) : ℝ) := by
      push_cast; ring
    rw [hcast, mul_assoc, h0_eq]
    push_cast; ring
  obtain ⟨t0, ht0⟩ := hO0
  intro a
  obtain ⟨ta, hta⟩ := htele a.val (Nat.le_of_lt a.isLt)
  have hfin_a : (⟨a.val % len, Nat.mod_lt _ hlen⟩ : Fin len) = a :=
    Fin.ext (Nat.mod_eq_of_lt a.isLt)
  rw [hfin_a] at hta
  refine ⟨(2 ^ a.val : ℕ) * t0 - (O : ℕ) * ta, ?_⟩
  have hrel : ((2 ^ f * O : ℕ) : ℝ) * v (u a) =
      ((2 ^ a.val : ℕ) : ℝ) * (((2 ^ f * O : ℕ) : ℝ) * v (u ⟨0, hlen⟩)) -
      ((O : ℕ) : ℝ) * (((2 ^ f : ℕ) : ℝ) * (((2 ^ a.val : ℕ) : ℝ) * v (u ⟨0, hlen⟩) - v (u a))) := by
    push_cast; ring
  rw [hrel, ht0, hta]
  push_cast; ring

theorem main :
    ∀ (s : ℕ) (z : Fin s) (n : Fin s → Bool → Option (Fin s)) (K : ℕ),
      let run := fun (b : ℕ) (w : Fin b → Bool) =>
        (List.ofFn w).foldl (fun (x : Option (Fin s)) (bit : Bool) =>
          x.bind (fun i => n i bit)) (some z)
      let live := fun b : ℕ =>
        ((Finset.univ : Finset (Fin b → Bool)).filter (fun w => (run b w).isSome)).card
      (∀ B : ℕ, ∃ b ≥ B, live b ≤ K) →
        ∃ (m : ℕ) (l : Fin m → ℕ) (node : (i : Fin m) → Fin (l i) → Fin s),
          let T := ∑ i, l i
          let O := (Finset.univ : Finset (Fin m)).lcm (fun i => 2^(l i)-1)
          m ≤ K ∧ T ≤ s ∧ (∀ i, 0 < l i ∧ Function.Injective (node i)) ∧
          (∀ i j a b, node i a = node j b → i = j) ∧
          (∀ i, ∃ (b : ℕ) (w : Fin b → Bool) (j : Fin (l i)), run b w = some (node i j)) ∧
          (∀ i a, ∃ (bit : Bool) (b : Fin (l i)), b.val = (a.val+1) % l i ∧ n (node i a) bit = some (node i b)) ∧
          ∀ (g : Fin s → Bool → ℤ) (v : Fin s → ℝ),
            (∀ i, 2*v i = ∑ bit : Bool, (n i bit).elim (g i bit : ℝ) v) →
            ∃ t : ℤ, ((2^(s-T)*O : ℕ) : ℝ)*v z = t := by
  classical
  intro s z n K run live hlive
  have hlive' : ∀ B : ℕ, ∃ b ≥ B,
      ((Finset.univ : Finset (Fin b → Bool)).filter (fun w => (runFrom n z b w).isSome)).card ≤ K :=
    hlive
  let S : Finset (Fin s) := Finset.univ.filter (fun u => Reach n z u ∧ ReachPos n u u)
  have hS_step : ∀ u : Fin s, u ∈ S →
      ∃ (bit : Bool) (v : Fin s), n u bit = some v ∧ v ∈ S := by
    intro u hu
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    obtain ⟨hzu, p, hpne, hprun⟩ := hu
    cases p with
    | nil => exact (hpne rfl).elim
    | cons bit rest =>
      rw [runList_cons] at hprun
      cases hnb : n u bit with
      | none => rw [hnb] at hprun; simp at hprun
      | some v =>
        rw [hnb, Option.bind_some] at hprun
        refine ⟨bit, v, hnb, ?_⟩
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨reach_trans n hzu (reach_step n hnb), ?_⟩
        refine ⟨rest ++ [bit], by simp, ?_⟩
        rw [runList_append, hprun, Option.bind_some, runList_cons, hnb, Option.bind_some]
        rfl
  let nextBit : Fin s → Bool := fun u =>
    if hu : u ∈ S then (hS_step u hu).choose else false
  let next : Fin s → Fin s := fun u =>
    if hu : u ∈ S then (hS_step u hu).choose_spec.choose else u
  have hnext_spec : ∀ u (hu : u ∈ S), n u (nextBit u) = some (next u) ∧ next u ∈ S := by
    intro u hu
    simp only [nextBit, next, hu, ↓reduceDIte]
    exact (hS_step u hu).choose_spec.choose_spec
  have hnext_unique : ∀ u ∈ S, ∀ (bit : Bool) (v : Fin s),
      n u bit = some v → InfState n v → bit = nextBit u ∧ v = next u := by
    intro u hu bit v hnb hinfv
    have hspec := hnext_spec u hu
    have hu_r : Reach n z u ∧ ReachPos n u u := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      exact hu
    have hinf_next : InfState n (next u) := by
      have hns := hspec.2
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hns
      exact inf_of_reachPos_self n hns.2
    have hbit : bit = nextBit u :=
      unique_inf_step z n K hlive' hu_r.1 hu_r.2 hnb hinfv hspec.1 hinf_next
    refine ⟨hbit, ?_⟩
    rw [hbit] at hnb
    rw [hspec.1] at hnb
    exact Option.some.inj hnb.symm
  have hS_closed : ∀ u ∈ S, next u ∈ S := fun u hu => (hnext_spec u hu).2
  have hS_per : ∀ u ∈ S, ∃ k, 0 < k ∧ next^[k] u = u := by
    intro u hu
    have hu_r : Reach n z u ∧ ReachPos n u u := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      exact hu
    obtain ⟨p, hpne, hprun⟩ := hu_r.2
    have hfollow : ∀ (l : List Bool) (x : Fin s),
        x ∈ S → runList n x l = some u → next^[l.length] x = u := by
      intro l
      induction l with
      | nil =>
        intro x _ hx
        simp [runList_nil] at hx
        exact hx
      | cons bit rest ih =>
        intro x hx hrun
        rw [runList_cons] at hrun
        cases hnb : n x bit with
        | none => rw [hnb] at hrun; simp at hrun
        | some y =>
          rw [hnb, Option.bind_some] at hrun
          have hy_inf : InfState n y := by
            have hiu : InfState n u := inf_of_reachPos_self n hu_r.2
            intro k
            obtain ⟨l2, hl2_len, hl2_some⟩ := hiu k
            have hrun2 : (runList n y (rest ++ l2)).isSome := by
              rw [runList_append, hrun, Option.bind_some]
              exact hl2_some
            have hlen2 : k ≤ (rest ++ l2).length := by
              rw [List.length_append, hl2_len]
              omega
            exact ⟨(rest ++ l2).take k, by rw [List.length_take, min_eq_left hlen2],
              runList_take_isSome n y _ k hrun2⟩
          have hyeq := (hnext_unique x hx bit y hnb hy_inf).2
          rw [List.length_cons, Function.iterate_succ_apply, ← hyeq]
          exact ih y (hyeq ▸ hS_closed x hx) hrun
    exact ⟨p.length, List.length_pos_of_ne_nil hpne, hfollow p u hu hprun⟩
  obtain ⟨m, l, node, hT_eq, hpos_inj, hdisj, hmemS, hcovS, hstep_next⟩ :=
    cycle_decomp next S hS_closed hS_per
  have hstep_n : ∀ i a, ∃ (bit : Bool) (b : Fin (l i)),
      b.val = (a.val + 1) % l i ∧ n (node i a) bit = some (node i b) := by
    intro i a
    obtain ⟨b, hbval, hbn⟩ := hstep_next i a
    have hspec := hnext_spec (node i a) (hmemS i a)
    exact ⟨nextBit (node i a), b, hbval, by rw [hspec.1, hbn]⟩
  have hreach_node : ∀ i, ∃ (b : ℕ) (w : Fin b → Bool) (j : Fin (l i)),
      run b w = some (node i j) := by
    intro i
    let j0 : Fin (l i) := ⟨0, (hpos_inj i).1⟩
    have hm := hmemS i j0
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    obtain ⟨p, hp⟩ := hm.1
    refine ⟨p.length, fun k => p.getD k.val false, j0, ?_⟩
    change runFrom n z p.length (fun k => p.getD k.val false) = some (node i j0)
    unfold runFrom
    rw [ofFn_getD_eq p rfl]
    exact hp
  have hm_le : m ≤ K := by
    have h0reach : ∀ i : Fin m, ∃ p : List Bool, runList n z p = some (node i ⟨0, (hpos_inj i).1⟩) := by
      intro i
      have hm := hmemS i ⟨0, (hpos_inj i).1⟩
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hm
      exact hm.1
    choose fp hfp using h0reach
    let B := (Finset.univ : Finset (Fin m)).sup (fun i => (fp i).length)
    obtain ⟨b, hb_ge, hb_le⟩ := hlive' B
    have hex : ∀ i : Fin m, ∃ (lw : List Bool) (a1 : Fin (l i)),
        lw.length = b ∧ runList n z lw = some (node i a1) := by
      intro i
      have hpi : (fp i).length ≤ b := le_trans (Finset.le_sup (f := fun j => (fp j).length) (Finset.mem_univ i)) hb_ge
      obtain ⟨cl, a1, hcl_len, hcl_run⟩ :=
        cycle_walk n (node i) (hstep_n i) ⟨0, (hpos_inj i).1⟩ (b - (fp i).length)
      refine ⟨fp i ++ cl, a1, by simp [hcl_len]; omega, ?_⟩
      rw [runList_append, hfp i, Option.bind_some, hcl_run]
    choose flw fa1 hflw_len hflw_run using hex
    let fW : Fin m → (Fin b → Bool) := fun i k => (flw i).getD k.val false
    have hfW_inj : Function.Injective fW := by
      intro i j hij
      have hrun_eq : runFrom n z b (fW i) = runFrom n z b (fW j) := by rw [hij]
      unfold runFrom at hrun_eq
      rw [ofFn_getD_eq (flw i) (hflw_len i), ofFn_getD_eq (flw j) (hflw_len j)] at hrun_eq
      change runList n z (flw i) = runList n z (flw j) at hrun_eq
      rw [hflw_run i, hflw_run j] at hrun_eq
      exact hdisj i j (fa1 i) (fa1 j) (Option.some.inj hrun_eq)
    have hsub : (Finset.univ : Finset (Fin m)).image fW ⊆
        (Finset.univ : Finset (Fin b → Bool)).filter (fun w => (runFrom n z b w).isSome) := by
      intro w hw
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
      obtain ⟨i, rfl⟩ := hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      unfold runFrom
      rw [ofFn_getD_eq (flw i) (hflw_len i)]
      change (runList n z (flw i)).isSome
      rw [hflw_run i]
      rfl
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hfW_inj, Finset.card_univ, Fintype.card_fin] at hcard
    omega
  refine ⟨m, l, node, ?_, ?_, hpos_inj, hdisj, hreach_node, hstep_n, ?_⟩
  · exact hm_le
  · rw [hT_eq]
    exact le_trans (Finset.card_le_univ S) (by simp)
  · intro g v hbell
    let T := ∑ i, l i
    let O := (Finset.univ : Finset (Fin m)).lcm (fun i => 2 ^ (l i) - 1)
    let Fset : Finset (Fin s) := Finset.univ.filter (fun u => ¬ InfState n u)
    let Aset : Finset (Fin s) := Finset.univ.filter (fun u => Reach n z u ∧ InfState n u ∧ ¬ ReachPos n u u)
    have hF_int : ∀ u ∈ Fset, ∃ t : ℤ, ((2 ^ Fset.card : ℕ) : ℝ) * v u = t := by
      intro u hu
      have h1 := dag_int_bound n g v hbell Fset (fun x => Fset.filter (fun w => Reach n x w))
        (fun x w => Finset.mem_filter) 0 1
        (fun x hx hcyc => (Finset.mem_filter.mp hx).2 (inf_of_reachPos_self n hcyc))
        (fun x hx bit w hnb hw => by
          exfalso
          have hw_inf : InfState n w := by
            simp only [Fset, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hw
            exact hw
          exact (Finset.mem_filter.mp hx).2 (inf_of_step n hnb hw_inf))
        Fset.card u hu (Finset.card_filter_le _ _)
      simpa using h1
    have hS_int : ∀ u ∈ S, ∃ t : ℤ, ((2 ^ Fset.card * O : ℕ) : ℝ) * v u = t := by
      intro u hu
      obtain ⟨i, a, rfl⟩ := hcovS u hu
      have hdiv : (2 ^ l i - 1) ∣ O := Finset.dvd_lcm (Finset.mem_univ i)
      refine cycle_int_bound n g v hbell (hpos_inj i).1 (node i) Fset.card O hdiv ?_ a
      intro a'
      obtain ⟨b, hbval, hbn⟩ := hstep_next i a'
      have hspec := hnext_spec (node i a') (hmemS i a')
      refine ⟨nextBit (node i a'), b, hbval, by rw [hspec.1, hbn], ?_⟩
      cases hoth : n (node i a') (!(nextBit (node i a'))) with
      | none =>
        refine ⟨(2 ^ Fset.card : ℕ) * g (node i a') (!(nextBit (node i a'))), ?_⟩
        simp
      | some w =>
        simp only [Option.elim_some]
        have hwF : w ∈ Fset := by
          simp only [Fset, Finset.mem_filter, Finset.mem_univ, true_and]
          intro hinfw
          have hbit_eq := (hnext_unique (node i a') (hmemS i a') (!(nextBit (node i a'))) w hoth hinfw).1
          cases nextBit (node i a') <;> simp at hbit_eq
        exact hF_int w hwF
    have hA_int : ∀ u ∈ Aset, ∃ t : ℤ, ((2 ^ (Fset.card + Aset.card) * O : ℕ) : ℝ) * v u = t := by
      intro u hu
      refine dag_int_bound n g v hbell Aset (fun x => Aset.filter (fun w => Reach n x w))
        (fun x w => Finset.mem_filter) Fset.card O
        (fun x hx => (Finset.mem_filter.mp hx).2.2.2)
        (fun x hx bit w hnb hw => ?_)
        Aset.card u hu (Finset.card_filter_le _ _)
      by_cases hinfw : InfState n w
      · have hzw : Reach n z w := reach_trans n (Finset.mem_filter.mp hx).2.1 (reach_step n hnb)
        have hwS : w ∈ S := by
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨hzw, ?_⟩
          by_contra hnc
          exact hw (Finset.mem_filter.mpr ⟨Finset.mem_univ w, hzw, hinfw, hnc⟩)
        exact hS_int w hwS
      · have hwF : w ∈ Fset := Finset.mem_filter.mpr ⟨Finset.mem_univ w, hinfw⟩
        obtain ⟨t, ht⟩ := hF_int w hwF
        refine ⟨(O : ℕ) * t, ?_⟩
        have hcast : ((2 ^ Fset.card * O : ℕ) : ℝ) * v w =
            ((O : ℕ) : ℝ) * (((2 ^ Fset.card : ℕ) : ℝ) * v w) := by
          push_cast; ring
        rw [hcast, ht]
        push_cast; ring
    have hdisj_FA : Disjoint Fset Aset := by
      rw [Finset.disjoint_left]
      intro x hxF hxA
      exact (Finset.mem_filter.mp hxF).2 (Finset.mem_filter.mp hxA).2.2.1
    have hdisj_FS : Disjoint Fset S := by
      rw [Finset.disjoint_left]
      intro x hxF hxS
      exact (Finset.mem_filter.mp hxF).2 (inf_of_reachPos_self n (Finset.mem_filter.mp hxS).2.2)
    have hdisj_AS : Disjoint Aset S := by
      rw [Finset.disjoint_left]
      intro x hxA hxS
      exact (Finset.mem_filter.mp hxA).2.2.2 (Finset.mem_filter.mp hxS).2.2
    have hcard_sum : Fset.card + Aset.card + S.card ≤ s := by
      have hu1 : Disjoint (Fset ∪ Aset) S := Finset.disjoint_union_left.mpr ⟨hdisj_FS, hdisj_AS⟩
      have hcard_u : (Fset ∪ Aset ∪ S).card = Fset.card + Aset.card + S.card := by
        rw [Finset.card_union_of_disjoint hu1, Finset.card_union_of_disjoint hdisj_FA]
      have hle : (Fset ∪ Aset ∪ S).card ≤ s := le_trans (Finset.card_le_univ _) (by simp)
      omega
    have hFA_le : Fset.card + Aset.card ≤ s - T := by omega
    have hz_base : ∃ t : ℤ, ((2 ^ (Fset.card + Aset.card) * O : ℕ) : ℝ) * v z = t := by
      by_cases hinfz : InfState n z
      · by_cases hcycz : ReachPos n z z
        · have hzS : z ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ z, reach_refl n z, hcycz⟩
          obtain ⟨t, ht⟩ := hS_int z hzS
          refine ⟨(2 ^ Aset.card : ℕ) * t, ?_⟩
          have hcast : ((2 ^ (Fset.card + Aset.card) * O : ℕ) : ℝ) * v z =
              ((2 ^ Aset.card : ℕ) : ℝ) * (((2 ^ Fset.card * O : ℕ) : ℝ) * v z) := by
            push_cast; rw [pow_add]; ring
          rw [hcast, ht]; push_cast; ring
        · have hzA : z ∈ Aset :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ z, reach_refl n z, hinfz, hcycz⟩
          exact hA_int z hzA
      · have hzF : z ∈ Fset := Finset.mem_filter.mpr ⟨Finset.mem_univ z, hinfz⟩
        obtain ⟨t, ht⟩ := hF_int z hzF
        refine ⟨(2 ^ Aset.card * O : ℕ) * t, ?_⟩
        have hcast : ((2 ^ (Fset.card + Aset.card) * O : ℕ) : ℝ) * v z =
            ((2 ^ Aset.card * O : ℕ) : ℝ) * (((2 ^ Fset.card : ℕ) : ℝ) * v z) := by
          push_cast; rw [pow_add]; ring
        rw [hcast, ht]; push_cast; ring
    obtain ⟨tz, htz⟩ := hz_base
    refine ⟨(2 ^ (s - T - (Fset.card + Aset.card)) : ℕ) * tz, ?_⟩
    have hsplit : s - T = (Fset.card + Aset.card) + (s - T - (Fset.card + Aset.card)) := by omega
    have hcast : ((2 ^ (s - T) * O : ℕ) : ℝ) * v z =
        ((2 ^ (s - T - (Fset.card + Aset.card)) : ℕ) : ℝ) *
        (((2 ^ (Fset.card + Aset.card) * O : ℕ) : ℝ) * v z) := by
      conv_lhs => rw [hsplit]
      push_cast; rw [pow_add]; ring
    rw [hcast, htz]
    push_cast; ring

end PEqualNP.Outside.L_lib_852

theorem PEqualNP.Outside.L_lib_852 :
    ∀ (s : ℕ) (z : Fin s) (n : Fin s → Bool → Option (Fin s)) (K : ℕ),
      let run := fun (b : ℕ) (w : Fin b → Bool) =>
        (List.ofFn w).foldl (fun (x : Option (Fin s)) (bit : Bool) =>
          x.bind (fun i => n i bit)) (some z)
      let live := fun b : ℕ =>
        ((Finset.univ : Finset (Fin b → Bool)).filter (fun w => (run b w).isSome)).card
      (∀ B : ℕ, ∃ b ≥ B, live b ≤ K) →
        ∃ (m : ℕ) (l : Fin m → ℕ) (node : (i : Fin m) → Fin (l i) → Fin s),
          let T := ∑ i, l i
          let O := (Finset.univ : Finset (Fin m)).lcm (fun i => 2^(l i)-1)
          m ≤ K ∧ T ≤ s ∧ (∀ i, 0 < l i ∧ Function.Injective (node i)) ∧
          (∀ i j a b, node i a = node j b → i = j) ∧
          (∀ i, ∃ (b : ℕ) (w : Fin b → Bool) (j : Fin (l i)), run b w = some (node i j)) ∧
          (∀ i a, ∃ (bit : Bool) (b : Fin (l i)), b.val = (a.val+1) % l i ∧ n (node i a) bit = some (node i b)) ∧
          ∀ (g : Fin s → Bool → ℤ) (v : Fin s → ℝ),
            (∀ i, 2*v i = ∑ bit : Bool, (n i bit).elim (g i bit : ℝ) v) →
            ∃ t : ℤ, ((2^(s-T)*O : ℕ) : ℝ)*v z = t :=
  PEqualNP.Outside.L_lib_852.main
