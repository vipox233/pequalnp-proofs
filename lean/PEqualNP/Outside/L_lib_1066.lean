import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Perm

namespace PEqualNP.Outside.L_lib_1066

def res {n k : ℕ} (hn : 0 < n) (w : Fin k) : Fin n :=
  ⟨w.val % n, Nat.mod_lt w.val hn⟩

def next {m : ℕ} (hm : 0 < m) (x : Fin m) : Fin m :=
  ⟨(x.val + 1) % m, Nat.mod_lt _ hm⟩

def prev {m : ℕ} (hm : 0 < m) (x : Fin m) : Fin m :=
  ⟨(x.val + m - 1) % m, Nat.mod_lt _ hm⟩

def step {m : ℕ} (hm : 0 < m) (x : Fin m) (a : ℕ) : Fin m :=
  ⟨(x.val + a) % m, Nat.mod_lt _ hm⟩

def divP {n p : ℕ} (hp : 0 < p) (t : Fin (p * n)) : Fin n :=
  ⟨t.val / p, (Nat.div_lt_iff_lt_mul hp).mpr (Nat.lt_of_lt_of_eq t.isLt (Nat.mul_comm p n))⟩

def modP {n p : ℕ} (hp : 0 < p) (t : Fin (p * n)) : Fin p :=
  ⟨t.val % p, Nat.mod_lt t.val hp⟩

def mkBlock {n p : ℕ} (b : Fin n) (c : Fin p) : Fin (p * n) :=
  ⟨b.val * p + c.val, by
    have hc := c.isLt
    have hb : (b.val + 1) * p ≤ n * p := Nat.mul_le_mul_right p b.isLt
    rw [Nat.succ_mul, Nat.mul_comm n p] at hb; omega⟩

lemma divP_mkBlock {n p : ℕ} (hp : 0 < p) (b : Fin n) (c : Fin p) :
    divP hp (mkBlock b c) = b := by
  ext
  simp only [divP, mkBlock]
  rw [Nat.mul_comm b.val p, Nat.mul_add_div hp, Nat.div_eq_of_lt c.isLt, Nat.add_zero]

lemma modP_mkBlock {n p : ℕ} (hp : 0 < p) (b : Fin n) (c : Fin p) :
    modP hp (mkBlock b c) = c := by
  ext
  simp only [modP, mkBlock, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt c.isLt]

lemma mkBlock_divP_modP {n p : ℕ} (hp : 0 < p) (t : Fin (p * n)) :
    mkBlock (divP hp t) (modP hp t) = t := by
  ext
  simp only [mkBlock, divP, modP]
  rw [Nat.mul_comm (t.val / p) p]
  exact Nat.div_add_mod t.val p

lemma next_prev {m : ℕ} (hm : 0 < m) (x : Fin m) : next hm (prev hm x) = x := by
  ext
  simp only [next, prev]
  have hx := x.isLt
  have h1 : (x.val + m - 1) % m + 1 = if x.val = 0 then m else x.val := by
    by_cases h0 : x.val = 0
    · simp [h0]; omega
    · have : x.val + m - 1 = (x.val - 1) + m := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      simp [h0]; omega
  rw [h1]
  split_ifs with h0
  · simp [h0]
  · exact Nat.mod_eq_of_lt hx

lemma prev_next {m : ℕ} (hm : 0 < m) (x : Fin m) : prev hm (next hm x) = x := by
  ext
  simp only [next, prev]
  have hx := x.isLt
  by_cases h1 : x.val + 1 = m
  · simp [h1, Nat.mod_eq_of_lt (by omega : m - 1 < m)]; omega
  · have hlt : x.val + 1 < m := by omega
    rw [Nat.mod_eq_of_lt hlt]
    have h2 : x.val + 1 + m - 1 = x.val + m := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hx]

lemma next_injective {m : ℕ} (hm : 0 < m) : Function.Injective (next hm) :=
  Function.LeftInverse.injective (prev_next hm)

lemma prev_injective {m : ℕ} (hm : 0 < m) : Function.Injective (prev hm) :=
  Function.LeftInverse.injective (next_prev hm)

lemma prev_ne_self {m : ℕ} (hm : 2 ≤ m) (x : Fin m) : prev (by omega) x ≠ x := by
  intro h
  have hv := congrArg Fin.val h
  simp only [prev] at hv
  have hx := x.isLt
  by_cases h0 : x.val = 0
  · rw [h0] at hv
    simp only [Nat.zero_add] at hv
    rw [Nat.mod_eq_of_lt (by omega : m - 1 < m)] at hv
    omega
  · have h1 : x.val + m - 1 = (x.val - 1) + m := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hv
    omega

lemma step_zero {m : ℕ} (hm : 0 < m) (x : Fin m) : step hm x 0 = x := by
  ext; simp [step, Nat.mod_eq_of_lt x.isLt]

lemma step_succ {m : ℕ} (hm : 0 < m) (x : Fin m) (a : ℕ) :
    step hm x (a + 1) = next hm (step hm x a) := by
  ext
  simp only [step, next, Nat.mod_add_mod, Nat.add_assoc]

lemma step_succ' {m : ℕ} (hm : 0 < m) (x : Fin m) (a : ℕ) :
    step hm x (a + 1) = step hm (next hm x) a := by
  ext
  simp only [step, next, Nat.mod_add_mod]
  congr 1; omega

lemma step_add {m : ℕ} (hm : 0 < m) (x : Fin m) (a b : ℕ) :
    step hm (step hm x a) b = step hm x (a + b) := by
  ext
  simp only [step, Nat.mod_add_mod, Nat.add_assoc]

lemma step_prev_comm {m : ℕ} (hm : 0 < m) (x : Fin m) (a : ℕ) :
    prev hm (step hm x a) = step hm (prev hm x) a := by
  apply next_injective hm
  rw [next_prev, ← step_succ, step_succ', next_prev]

lemma step_prev_iter {m : ℕ} (hm : 0 < m) (x : Fin m) :
    ∀ t : ℕ, step hm ((prev hm)^[t] x) t = x
  | 0 => step_zero hm x
  | t + 1 => by
      rw [Function.iterate_succ_apply', step_succ', next_prev]
      exact step_prev_iter hm x t

lemma prev_iter_step {m : ℕ} (hm : 0 < m) (x : Fin m) :
    ∀ t : ℕ, (prev hm)^[t] (step hm x t) = x
  | 0 => by simp [step_zero]
  | t + 1 => by
      rw [step_succ, Function.iterate_succ_apply, prev_next]
      exact prev_iter_step hm x t

lemma res_prev {n p : ℕ} (hn : 0 < n) (hp : 0 < p) (w : Fin (p * n)) :
    res hn (prev (Nat.mul_pos hp hn) w) = prev hn (res hn w) := by
  ext
  simp only [res, prev]
  have hdvd : n ∣ p * n := Nat.dvd_mul_left n p
  rw [Nat.mod_mod_of_dvd _ hdvd]
  have h1 : w.val + p * n - 1 = (w.val + n - 1) + (p - 1) * n := by
    have : p * n = n + (p - 1) * n := by
      cases p with
      | zero => omega
      | succ p' => simp [Nat.succ_mul]; omega
    omega
  rw [h1, Nat.add_mul_mod_self_right]
  have h2 : (w.val + n - 1) % n = (w.val % n + n - 1) % n := by
    have hdiv := Nat.div_add_mod w.val n
    have h3 : w.val + n - 1 = (w.val % n + n - 1) + (w.val / n) * n := by
      rw [Nat.mul_comm (w.val / n) n]; omega
    rw [h3, Nat.add_mul_mod_self_right]
  exact h2

lemma res_next {n p : ℕ} (hn : 0 < n) (hp : 0 < p) (w : Fin (p * n)) :
    res hn (next (Nat.mul_pos hp hn) w) = next hn (res hn w) := by
  ext
  simp only [res, next]
  have hdvd : n ∣ p * n := Nat.dvd_mul_left n p
  rw [Nat.mod_mod_of_dvd _ hdvd, Nat.mod_add_mod]

def coordSub (n : ℕ) (A : Finset (Fin n)) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  { carrier := { v | ∀ j, j ∉ A → v j = 0 }, add_mem' := fun ha hb j hj => by simp [ha j hj, hb j hj],
    zero_mem' := fun _ _ => rfl, smul_mem' := fun _ _ hv j hj => by simp [hv j hj] }

lemma span_single_eq_coordSub (n : ℕ) (A : Finset (Fin n)) :
    Submodule.span (ZMod 2) ((fun j : Fin n => (Pi.single j (1 : ZMod 2) : Fin n → ZMod 2)) '' (A : Set (Fin n))) =
      coordSub n A := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro v ⟨j, hj, rfl⟩ i hi
    have hne : i ≠ j := fun h => hi (h ▸ hj)
    exact Pi.single_eq_of_ne hne 1
  · intro v hv
    have hv_eq : v = ∑ j ∈ A, v j • (Pi.single j (1 : ZMod 2) : Fin n → ZMod 2) := by
      funext i
      rw [Finset.sum_apply]
      by_cases hi : i ∈ A
      · rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          simp [Pi.single_eq_of_ne (Ne.symm hji)]
        · intro h; exact absurd hi h
      · rw [hv i hi]
        symm
        apply Finset.sum_eq_zero
        intro j hj
        have hne : i ≠ j := fun h => hi (h ▸ hj)
        simp [Pi.single_eq_of_ne hne]
    rw [hv_eq]
    refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨j, hj, rfl⟩

lemma coordSub_inf (n : ℕ) (A B : Finset (Fin n)) :
    coordSub n A ⊓ coordSub n B = coordSub n (A ∩ B) := by
  ext v
  simp only [Submodule.mem_inf, coordSub, Submodule.mem_mk, AddSubmonoid.mem_mk,
    AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, Finset.mem_inter, not_and_or]
  constructor
  · rintro ⟨ha, hb⟩ j (hj | hj)
    · exact ha j hj
    · exact hb j hj
  · intro h
    exact ⟨fun j hj => h j (Or.inl hj), fun j hj => h j (Or.inr hj)⟩

lemma finrank_coordSub (n : ℕ) (C : Finset (Fin n)) :
    Module.finrank (ZMod 2) (coordSub n C) = C.card := by
  have hrange : Set.range (fun j : C => (Pi.single j.1 (1 : ZMod 2) : Fin n → ZMod 2)) =
      (fun j : Fin n => (Pi.single j (1 : ZMod 2) : Fin n → ZMod 2)) '' (C : Set (Fin n)) := by
    ext v; simp
  rw [← span_single_eq_coordSub, ← hrange]
  have hli : LinearIndependent (ZMod 2) (fun j : C => (Pi.single j.1 (1 : ZMod 2) : Fin n → ZMod 2)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hi := congrFun hc i.1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
    rw [Finset.sum_eq_single i] at hi
    · simpa using hi
    · intro j _ hji
      have hne : i.1 ≠ j.1 := fun h => hji (Subtype.ext h.symm)
      simp [Pi.single_eq_of_ne hne]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [finrank_span_eq_card hli, Fintype.card_coe]

lemma mem_take_ofFn_iff {k : ℕ} (o : Fin k → Fin k) (u : ℕ) (hu : u ≤ k) (w : Fin k) :
    w ∈ (List.ofFn o).take u ↔ ∃ t : Fin k, t.val < u ∧ o t = w := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨m, hm, rfl⟩
    have hm' : m < u := by
      rw [List.length_take, List.length_ofFn, Nat.min_eq_left hu] at hm
      exact hm
    refine ⟨⟨m, by omega⟩, hm', ?_⟩
    simp [List.getElem_take, List.getElem_ofFn]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t.val, ?_, ?_⟩
    · rw [List.length_take, List.length_ofFn, Nat.min_eq_left hu]
      exact ht
    · simp [List.getElem_take, List.getElem_ofFn]

lemma mem_drop_ofFn_iff {k : ℕ} (o : Fin k → Fin k) (u : ℕ) (hu : u ≤ k) (w : Fin k) :
    w ∈ (List.ofFn o).drop u ↔ ∃ t : Fin k, u ≤ t.val ∧ o t = w := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [List.length_drop, List.length_ofFn] at hm
    refine ⟨⟨u + m, by omega⟩, by dsimp; omega, ?_⟩
    simp [List.getElem_drop, List.getElem_ofFn]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t.val - u, ?_, ?_⟩
    · rw [List.length_drop, List.length_ofFn]; omega
    · simp only [List.getElem_drop, List.getElem_ofFn]
      congr 1; ext; dsimp; omega

def runStarts {m : ℕ} (hm : 0 < m) (S : Finset (Fin m)) : Finset (Fin m) :=
  Finset.univ.filter (fun j => j ∈ S ∧ prev hm j ∉ S)

lemma runStarts_eq_stmt {m : ℕ} (hm : 0 < m) (S : Finset (Fin m))
    (d : ∀ P : Prop, Decidable P) :
    @Finset.filter (Fin m) (fun j => j ∈ S ∧ ∀ z ∈ S, (z.val + 1) % m ≠ j.val) (fun _ => d _)
      Finset.univ = runStarts hm S := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, runStarts]
  constructor
  · rintro ⟨hj, hprev⟩
    refine ⟨hj, fun hp => hprev (prev hm j) hp ?_⟩
    have := congrArg Fin.val (next_prev hm j)
    simpa [next] using this
  · rintro ⟨hj, hprev⟩
    refine ⟨hj, fun z hz heq => hprev ?_⟩
    have hnz : next hm z = j := by ext; exact heq
    rw [← hnz, prev_next]
    exact hz

lemma exists_runStart_between {m : ℕ} (hm : 0 < m) (S : Finset (Fin m)) (x : Fin m) :
    ∀ d : ℕ, x ∉ S → step hm x d ∈ S → ∃ t < d, step hm x (t + 1) ∈ runStarts hm S
  | 0, hx, hs => by rw [step_zero] at hs; exact absurd hs hx
  | d + 1, hx, hs => by
      by_cases hd : step hm x d ∈ S
      · obtain ⟨t, ht, hrun⟩ := exists_runStart_between hm S x d hx hd
        exact ⟨t, Nat.lt_succ_of_lt ht, hrun⟩
      · refine ⟨d, Nat.lt_succ_self d, ?_⟩
        simp only [runStarts, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hs, ?_⟩
        rw [step_succ, prev_next]
        exact hd

lemma card_runStarts_ge_p_of_full_and_empty {n p : ℕ} (hn : 0 < n) (hp : 0 < p)
    (S : Finset (Fin (p * n))) (j_full j_empty : Fin n)
    (hfull : ∀ w : Fin (p * n), res hn w = j_full → w ∈ S)
    (hempty : ∀ w : Fin (p * n), res hn w = j_empty → w ∉ S) :
    p ≤ (runStarts (Nat.mul_pos hp hn) S).card := by
  have hk : 0 < p * n := Nat.mul_pos hp hn
  let d := (j_full.val + n - j_empty.val) % n
  have hd_lt : d < n := Nat.mod_lt _ hn
  have hd_mod : (j_empty.val + d) % n = j_full.val := by
    dsimp [d]
    rw [Nat.add_mod_mod]
    have h1 : j_empty.val + (j_full.val + n - j_empty.val) = j_full.val + n := by
      have := j_empty.isLt; omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt j_full.isLt]
  have hex : ∀ q : Fin p, ∃ t < d,
      step hk ⟨q.val * n + j_empty.val, by
        have := j_empty.isLt
        have : (q.val + 1) * n ≤ p * n := Nat.mul_le_mul_right n q.isLt
        rw [Nat.succ_mul] at this; omega⟩ (t + 1) ∈ runStarts hk S := by
    intro q
    let xq : Fin (p * n) := ⟨q.val * n + j_empty.val, by
      have := j_empty.isLt
      have : (q.val + 1) * n ≤ p * n := Nat.mul_le_mul_right n q.isLt
      rw [Nat.succ_mul] at this; omega⟩
    have hxq : xq ∉ S := by
      apply hempty
      ext
      simp only [res, xq, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt j_empty.isLt]
    have hstep : step hk xq d ∈ S := by
      apply hfull
      ext
      simp only [res, step, xq]
      rw [Nat.mod_mod_of_dvd _ (Nat.dvd_mul_left n p)]
      have h1 : q.val * n + j_empty.val + d = q.val * n + (j_empty.val + d) := by omega
      rw [h1, Nat.mul_add_mod_self_right, hd_mod]
    exact exists_runStart_between hk S xq d hxq hstep
  choose f hf_lt hf_mem using hex
  let g : Fin p → Fin (p * n) := fun q =>
    step hk ⟨q.val * n + j_empty.val, by
      have := j_empty.isLt
      have : (q.val + 1) * n ≤ p * n := Nat.mul_le_mul_right n q.isLt
      rw [Nat.succ_mul] at this; omega⟩ (f q + 1)
  have hg_inj : Function.Injective g := by
    intro q1 q2 heq
    let off := fun (w : Fin (p * n)) => (w.val + p * n - j_empty.val) % (p * n)
    have hoff : ∀ q : Fin p, off (g q) = q.val * n + (f q + 1) := by
      intro q
      dsimp only [off, g, step]
      have hje : j_empty.val < p * n := by
        calc j_empty.val < n := j_empty.isLt
          _ = 1 * n := (Nat.one_mul n).symm
          _ ≤ p * n := Nat.mul_le_mul_right n hp
      have h1 : (q.val * n + j_empty.val + (f q + 1)) % (p * n) + p * n - j_empty.val =
          ((q.val * n + j_empty.val + (f q + 1)) % (p * n) + (p * n - j_empty.val)) := by
        omega
      rw [h1, Nat.mod_add_mod]
      have h2 : q.val * n + j_empty.val + (f q + 1) + (p * n - j_empty.val) =
          (q.val * n + (f q + 1)) + p * n := by
        omega
      rw [h2, Nat.add_mod_right]
      apply Nat.mod_eq_of_lt
      have hfq : f q + 1 < n := by have := hf_lt q; omega
      have hqn : (q.val + 1) * n ≤ p * n := Nat.mul_le_mul_right n q.isLt
      rw [Nat.succ_mul] at hqn
      omega
    have hdiv : ∀ q : Fin p, off (g q) / n = q.val := by
      intro q
      rw [hoff q, Nat.mul_comm q.val n, Nat.mul_add_div hn,
        Nat.div_eq_of_lt (by have := hf_lt q; omega), Nat.add_zero]
    ext
    rw [← hdiv q1, ← hdiv q2, heq]
  have hsub : (Finset.univ : Finset (Fin p)).image g ⊆ runStarts hk S := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨q, _, rfl⟩
    exact hf_mem q
  calc p = (Finset.univ : Finset (Fin p)).card := (Fintype.card_fin p).symm
    _ = ((Finset.univ : Finset (Fin p)).image g).card := (Finset.card_image_of_injective _ hg_inj).symm
    _ ≤ (runStarts hk S).card := Finset.card_le_card hsub

lemma card_ends_eq_runStarts {m : ℕ} (hm : 0 < m) (S : Finset (Fin m)) :
    (Finset.univ.filter (fun w : Fin m => w ∉ S ∧ prev hm w ∈ S)).card =
      (runStarts hm S).card := by
  let S' := S.image (next hm)
  have hcard : S'.card = S.card := Finset.card_image_of_injective S (next_injective hm)
  have hrun : runStarts hm S = S \ S' := by
    ext w
    simp only [runStarts, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      S', Finset.mem_image]
    constructor
    · rintro ⟨hw, hp⟩
      refine ⟨hw, ?_⟩
      rintro ⟨x, hx, hnx⟩
      rw [← hnx, prev_next] at hp
      exact hp hx
    · rintro ⟨hw, hnot⟩
      refine ⟨hw, fun hp => hnot ⟨prev hm w, hp, next_prev hm w⟩⟩
  have hends : Finset.univ.filter (fun w : Fin m => w ∉ S ∧ prev hm w ∈ S) = S' \ S := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, S', Finset.mem_image]
    constructor
    · rintro ⟨hw, hp⟩
      exact ⟨⟨prev hm w, hp, next_prev hm w⟩, hw⟩
    · rintro ⟨⟨x, hx, hnx⟩, hw⟩
      refine ⟨hw, ?_⟩
      rw [← hnx, prev_next]
      exact hx
  rw [hrun, hends]
  have h1 := Finset.card_sdiff_add_card_inter S S'
  have h2 := Finset.card_sdiff_add_card_inter S' S
  rw [Finset.inter_comm] at h2
  omega

lemma exists_flip (f : ℕ → Prop) (d a b : ℕ) (ha : a ≤ d) (hb : b ≤ d) (hfa : f a) (hfb : ¬ f b) :
    ∃ t < d, (f t ∧ ¬ f (t + 1)) ∨ (¬ f t ∧ f (t + 1)) := by
  by_contra h
  push Not at h
  have hall : ∀ m ≤ d, f m ↔ f 0 := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      have hm' : m < d := by omega
      have hstep := h m hm'
      have him := ih (by omega)
      tauto
  have h0a := (hall a ha).mp hfa
  exact hfb ((hall b hb).mpr h0a)

def labelsList {n k : ℕ} (hn : 0 < n) (ps : List (Fin k)) : Finset (Fin n) :=
  Finset.univ.filter (fun j : Fin n => ∃ w ∈ ps, res hn w = j)

def chargeClean {n p : ℕ} (hn : 0 < n) (o : Fin (p * n) → Fin (p * n)) (i : Fin (p * n)) : ℕ :=
  (labelsList hn ((List.ofFn o).take i.val) ∩ labelsList hn ((List.ofFn o).drop i.val)).card

def peakClean {n p : ℕ} (hn : 0 < n) (o : Fin (p * n) → Fin (p * n)) : ℕ :=
  (Finset.univ : Finset (Fin (p * n))).sup (chargeClean hn o)

def arcClean {k : ℕ} (hk : 0 < k) (r : ℕ) (w : Fin k) : Finset (Fin k) :=
  (Finset.univ : Finset (Fin (5 * r - 2))).image (fun a => step hk w a.val)

def poolClean {k : ℕ} (hk : 0 < k) (r : ℕ) (ps : List (Fin k)) : Finset (Fin k) :=
  ps.toFinset.biUnion (arcClean hk r)

def widthClean {n p : ℕ} (hn : 0 < n) (hp : 0 < p) (r : ℕ) (o : Fin (p * n) → Fin (p * n)) : ℕ :=
  (Finset.univ : Finset (Fin (p * n))).sup (fun i =>
    let L := (List.ofFn o).take i.val
    let R := (List.ofFn o).drop i.val
    ((poolClean (Nat.mul_pos hp hn) r L ∩ poolClean (Nat.mul_pos hp hn) r R) ∪
      arcClean (Nat.mul_pos hp hn) r (o i)).card + chargeClean hn o i)

def allowedClean {k : ℕ} (hk : 0 < k) (h : ℕ) (o : Fin k → Fin k) : Prop :=
  Function.Bijective o ∧ ∀ u : Fin (k + 1),
    (runStarts hk (((List.ofFn o).take u.val).toFinset)).card ≤ h

lemma chargeClean_le_n {n p : ℕ} (hn : 0 < n) (o : Fin (p * n) → Fin (p * n)) (i : Fin (p * n)) :
    chargeClean hn o i ≤ n := by
  calc chargeClean hn o i ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = n := Fintype.card_fin n

lemma peakClean_le_n {n p : ℕ} (hn : 0 < n) (o : Fin (p * n) → Fin (p * n)) :
    peakClean hn o ≤ n :=
  Finset.sup_le fun i _ => chargeClean_le_n hn o i

lemma exists_two_copies {n p : ℕ} (hn : 0 < n) (hp : 2 ≤ p) (j : Fin n) (w0 : Fin (p * n)) :
    ∃ w : Fin (p * n), w ≠ w0 ∧ res hn w = j := by
  let w1 : Fin (p * n) := ⟨j.val, by
    calc j.val < n := j.isLt
      _ = 1 * n := (Nat.one_mul n).symm
      _ ≤ p * n := Nat.mul_le_mul_right n (by omega)⟩
  let w2 : Fin (p * n) := ⟨n + j.val, by
    have hj := j.isLt
    have h2 : 2 * n ≤ p * n := Nat.mul_le_mul_right n hp
    omega⟩
  have h12 : w1 ≠ w2 := by intro h; have := congrArg Fin.val h; dsimp [w1, w2] at this; omega
  have hr1 : res hn w1 = j := by ext; exact Nat.mod_eq_of_lt j.isLt
  have hr2 : res hn w2 = j := by
    ext; simp only [res, w2, Nat.add_mod_left, Nat.mod_eq_of_lt j.isLt]
  by_cases h : w1 = w0
  · exact ⟨w2, fun heq => h12 (h.trans heq.symm), hr2⟩
  · exact ⟨w1, h, hr1⟩

lemma one_le_peakClean {n p : ℕ} (hn : 0 < n) (hp : 2 ≤ p)
    (o : Fin (p * n) → Fin (p * n)) (ho : Function.Bijective o) :
    1 ≤ peakClean hn o := by
  have hk2 : 2 ≤ p * n := by
    calc 2 = 2 * 1 := rfl
      _ ≤ p * n := Nat.mul_le_mul hp hn
  let i1 : Fin (p * n) := ⟨1, by omega⟩
  let j0 : Fin n := res hn (o ⟨0, by omega⟩)
  obtain ⟨w, hwne, hwres⟩ := exists_two_copies hn hp j0 (o ⟨0, by omega⟩)
  obtain ⟨t, rfl⟩ := ho.2 w
  have ht0 : 1 ≤ t.val := by
    by_contra h
    have ht0' : t = ⟨0, by omega⟩ := by ext; dsimp; omega
    exact hwne (congrArg o ht0')
  have hjL : j0 ∈ labelsList hn ((List.ofFn o).take i1.val) := by
    simp only [labelsList, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨o ⟨0, by omega⟩, ?_, rfl⟩
    rw [mem_take_ofFn_iff o i1.val (by omega)]
    exact ⟨⟨0, by omega⟩, by simp [i1], rfl⟩
  have hjR : j0 ∈ labelsList hn ((List.ofFn o).drop i1.val) := by
    simp only [labelsList, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨o t, ?_, hwres⟩
    rw [mem_drop_ofFn_iff o i1.val (by omega)]
    exact ⟨t, ht0, rfl⟩
  have hpos : 1 ≤ chargeClean hn o i1 :=
    Finset.card_pos.mpr ⟨j0, Finset.mem_inter.mpr ⟨hjL, hjR⟩⟩
  exact hpos.trans (Finset.le_sup (f := chargeClean hn o) (Finset.mem_univ i1))

lemma mem_drop_iff_not_mem_take {k : ℕ} (o : Fin k → Fin k) (ho : Function.Bijective o)
    (u : ℕ) (hu : u ≤ k) (w : Fin k) :
    w ∈ (List.ofFn o).drop u ↔ w ∉ (List.ofFn o).take u := by
  rw [mem_drop_ofFn_iff o u hu, mem_take_ofFn_iff o u hu]
  constructor
  · rintro ⟨t, ht, rfl⟩ ⟨t', ht', heq⟩
    have := ho.1 heq
    subst this; omega
  · intro hnot
    obtain ⟨t, rfl⟩ := ho.2 w
    refine ⟨t, ?_, rfl⟩
    by_contra hlt
    exact hnot ⟨t, by omega, rfl⟩

lemma first_completion_dichotomy {n p r : ℕ} (hn : 0 < n) (hp : 2 ≤ p) (hr : 4 ≤ r)
    (o : Fin (p * n) → Fin (p * n)) (ho : Function.Bijective o) :
    (∃ i : Fin (p * n), chargeClean hn o i = n) ∨
      (∃ u : Fin (p * n + 1),
        p ≤ (runStarts (Nat.mul_pos (by omega : 0 < p) hn)
          (((List.ofFn o).take u.val).toFinset)).card ∧
        p ≤ widthClean hn (by omega : 0 < p) r o) := by
  classical
  have hp0 : 0 < p := by omega
  have hk : 0 < p * n := Nat.mul_pos hp0 hn
  let fullAt : ℕ → Prop := fun u =>
    ∃ j : Fin n, ∀ w : Fin (p * n), res hn w = j → w ∈ ((List.ofFn o).take u).toFinset
  have hfullk : fullAt (p * n) := by
    refine ⟨⟨0, hn⟩, fun w _ => ?_⟩
    rw [List.mem_toFinset, mem_take_ofFn_iff o (p * n) le_rfl]
    obtain ⟨t, rfl⟩ := ho.2 w
    exact ⟨t, t.isLt, rfl⟩
  have hexk : ∃ u, fullAt u := ⟨p * n, hfullk⟩
  let u := Nat.find hexk
  have hu_full : fullAt u := Nat.find_spec hexk
  have hu_le : u ≤ p * n := Nat.find_min' hexk hfullk
  rcases hu_full with ⟨j_full, hj_full⟩
  have hu_ge2 : 2 ≤ u := by
    let w1 : Fin (p * n) := ⟨j_full.val, by
      calc j_full.val < n := j_full.isLt
        _ = 1 * n := (Nat.one_mul n).symm
        _ ≤ p * n := Nat.mul_le_mul_right n hp0⟩
    obtain ⟨w2, hw2ne, hw2res⟩ := exists_two_copies hn hp j_full w1
    have h1 : w1 ∈ ((List.ofFn o).take u).toFinset :=
      hj_full w1 (by ext; exact Nat.mod_eq_of_lt j_full.isLt)
    have h2 : w2 ∈ ((List.ofFn o).take u).toFinset := hj_full w2 hw2res
    have hcard : 2 ≤ (((List.ofFn o).take u).toFinset).card := by
      have : ({w1, w2} : Finset (Fin (p * n))) ⊆ ((List.ofFn o).take u).toFinset := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      calc 2 = ({w1, w2} : Finset (Fin (p * n))).card := (Finset.card_pair hw2ne.symm).symm
        _ ≤ (((List.ofFn o).take u).toFinset).card := Finset.card_le_card this
    have hle : (((List.ofFn o).take u).toFinset).card ≤ u := by
      calc (((List.ofFn o).take u).toFinset).card
          ≤ ((List.ofFn o).take u).length := List.toFinset_card_le _
        _ ≤ u := List.length_take_le u _
    omega
  let i : Fin (p * n) := ⟨u - 1, by omega⟩
  have hi_succ : i.val + 1 = u := by dsimp [i]; omega
  have hnot_prev : ¬ fullAt i.val := Nat.find_min hexk (by omega : i.val < u)
  let Su := ((List.ofFn o).take u).toFinset
  let L := (List.ofFn o).take i.val
  let R := (List.ofFn o).drop i.val
  have hSu_eq : ∀ w : Fin (p * n), w ∈ Su ↔ w ∈ L ∨ w = o i := by
    intro w
    simp only [Su, L, List.mem_toFinset, mem_take_ofFn_iff o u hu_le,
      mem_take_ofFn_iff o i.val (by omega)]
    constructor
    · rintro ⟨t, ht, rfl⟩
      by_cases hti : t.val < i.val
      · exact Or.inl ⟨t, hti, rfl⟩
      · have : t = i := by ext; omega
        exact Or.inr (congrArg o this)
    · rintro (⟨t, ht, rfl⟩ | rfl)
      · exact ⟨t, by omega, rfl⟩
      · exact ⟨i, by omega, rfl⟩
  by_cases hempty : ∃ j_empty : Fin n, ∀ w : Fin (p * n), res hn w = j_empty → w ∉ Su
  · right
    rcases hempty with ⟨j_empty, hj_empty⟩
    have hge : p ≤ (runStarts hk Su).card :=
      card_runStarts_ge_p_of_full_and_empty hn hp0 Su j_full j_empty hj_full hj_empty
    refine ⟨⟨u, by omega⟩, hge, ?_⟩
    have hsub : runStarts hk Su ⊆
        (poolClean hk r L ∩ poolClean hk r R) ∪ arcClean hk r (o i) := by
      intro x hx
      simp only [runStarts, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rcases hx with ⟨hxSu, hprevNotSu⟩
      have hprevR : prev hk x ∈ R := by
        rw [mem_drop_iff_not_mem_take o ho i.val (by omega)]
        intro hL
        exact hprevNotSu ((hSu_eq (prev hk x)).mpr (Or.inl hL))
      have hxPoolR : x ∈ poolClean hk r R := by
        simp only [poolClean, Finset.mem_biUnion, List.mem_toFinset]
        refine ⟨prev hk x, hprevR, ?_⟩
        simp only [arcClean, Finset.mem_image, Finset.mem_univ, true_and]
        refine ⟨⟨1, by omega⟩, ?_⟩
        rw [step_succ, step_zero, next_prev]
      rcases (hSu_eq x).mp hxSu with hxL | rfl
      · apply Finset.mem_union_left
        apply Finset.mem_inter.mpr
        refine ⟨?_, hxPoolR⟩
        simp only [poolClean, Finset.mem_biUnion, List.mem_toFinset]
        refine ⟨x, hxL, ?_⟩
        simp only [arcClean, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨⟨0, by omega⟩, step_zero hk x⟩
      · apply Finset.mem_union_right
        simp only [arcClean, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨⟨0, by omega⟩, step_zero hk (o i)⟩
    have hcard : p ≤ ((poolClean hk r L ∩ poolClean hk r R) ∪ arcClean hk r (o i)).card :=
      hge.trans (Finset.card_le_card hsub)
    have hle_w : ((poolClean hk r L ∩ poolClean hk r R) ∪ arcClean hk r (o i)).card +
        chargeClean hn o i ≤ widthClean hn hp0 r o :=
      Finset.le_sup (f := fun i =>
        let L := (List.ofFn o).take i.val
        let R := (List.ofFn o).drop i.val
        ((poolClean hk r L ∩ poolClean hk r R) ∪ arcClean hk r (o i)).card + chargeClean hn o i)
        (Finset.mem_univ i)
    omega
  · left
    push Not at hempty
    have hoi_res : res hn (o i) = j_full := by
      have hnot_j : ¬ ∀ w : Fin (p * n), res hn w = j_full → w ∈ L.toFinset :=
        fun h => hnot_prev ⟨j_full, h⟩
      push Not at hnot_j
      rcases hnot_j with ⟨w, hwres, hwL⟩
      rw [List.mem_toFinset] at hwL
      have hwSu : w ∈ Su := hj_full w hwres
      rcases (hSu_eq w).mp hwSu with h | rfl
      · exact absurd h hwL
      · exact hwres
    refine ⟨i, ?_⟩
    have htop : labelsList hn L ∩ labelsList hn R = Finset.univ := by
      ext j
      simp only [Finset.mem_inter, labelsList, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      constructor
      · by_cases hjeq : j = j_full
        · subst hjeq
          obtain ⟨w, hwne, hwres⟩ := exists_two_copies hn hp j (o i)
          have hwSu : w ∈ Su := hj_full w hwres
          rcases (hSu_eq w).mp hwSu with hwL | heq
          · exact ⟨w, hwL, hwres⟩
          · exact absurd heq hwne
        · obtain ⟨w, hwres, hwSu⟩ := hempty j
          rcases (hSu_eq w).mp hwSu with hwL | rfl
          · exact ⟨w, hwL, hwres⟩
          · exact absurd (hwres.symm.trans hoi_res) hjeq
      · have hnot_j : ¬ ∀ w : Fin (p * n), res hn w = j → w ∈ L.toFinset :=
          fun h => hnot_prev ⟨j, h⟩
        push Not at hnot_j
        rcases hnot_j with ⟨w, hwres, hwL⟩
        rw [List.mem_toFinset] at hwL
        exact ⟨w, (mem_drop_iff_not_mem_take o ho i.val (by omega) w).mpr hwL, hwres⟩
    simp only [chargeClean, L, R] at htop ⊢
    rw [htop, Finset.card_univ, Fintype.card_fin]

lemma part1_clean {n p r : ℕ} (hn : 0 < n) (hp : 2 ≤ p) (hr : 4 ≤ r)
    (o : Fin (p * n) → Fin (p * n)) (ho : Function.Bijective o) :
    min p n ≤ widthClean hn (by omega : 0 < p) r o ∧ 1 ≤ peakClean hn o := by
  refine ⟨?_, one_le_peakClean hn hp o ho⟩
  rcases first_completion_dichotomy hn hp hr o ho with ⟨i, hi⟩ | ⟨_, _, hw⟩
  · have hle : chargeClean hn o i ≤ widthClean hn (by omega : 0 < p) r o := by
      have hsup : ((poolClean (Nat.mul_pos (by omega : 0 < p) hn) r ((List.ofFn o).take i.val) ∩
          poolClean (Nat.mul_pos (by omega : 0 < p) hn) r ((List.ofFn o).drop i.val)) ∪
          arcClean (Nat.mul_pos (by omega : 0 < p) hn) r (o i)).card + chargeClean hn o i ≤
          widthClean hn (by omega : 0 < p) r o :=
        Finset.le_sup (f := fun i =>
          let L := (List.ofFn o).take i.val
          let R := (List.ofFn o).drop i.val
          ((poolClean (Nat.mul_pos (by omega : 0 < p) hn) r L ∩
            poolClean (Nat.mul_pos (by omega : 0 < p) hn) r R) ∪
            arcClean (Nat.mul_pos (by omega : 0 < p) hn) r (o i)).card + chargeClean hn o i)
          (Finset.mem_univ i)
      exact Nat.le_trans (Nat.le_add_left _ _) hsup
    calc min p n ≤ n := Nat.min_le_right p n
      _ = chargeClean hn o i := hi.symm
      _ ≤ widthClean hn (by omega : 0 < p) r o := hle
  · exact (Nat.min_le_left p n).trans hw

lemma part2_clean {n p : ℕ} (hn : 0 < n) (hp : 2 ≤ p)
    (o : Fin (p * n) → Fin (p * n))
    (hall : allowedClean (Nat.mul_pos (by omega : 0 < p) hn) (p - 1) o) :
    peakClean hn o = n := by
  rcases first_completion_dichotomy hn hp (by omega : 4 ≤ 4) o hall.1 with ⟨i, hi⟩ | ⟨u, hu, _⟩
  · apply le_antisymm (peakClean_le_n hn o)
    calc n = chargeClean hn o i := hi.symm
      _ ≤ peakClean hn o := Finset.le_sup (f := chargeClean hn o) (Finset.mem_univ i)
  · have hle := hall.2 u
    omega

lemma widthClean_le_of_allowed_peak_one {n p r : ℕ} (hn : 0 < n) (hp : 2 ≤ p) (hr : 4 ≤ r)
    (o : Fin (p * n) → Fin (p * n))
    (hall : allowedClean (Nat.mul_pos (by omega : 0 < p) hn) p o)
    (hpeak : peakClean hn o = 1) :
    widthClean hn (by omega : 0 < p) r o ≤ min (p * n) ((2 * p + 1) * (5 * r - 3) + 1) + 1 := by
  have hp0 : 0 < p := by omega
  have hk : 0 < p * n := Nat.mul_pos hp0 hn
  apply Finset.sup_le
  intro i _
  let L := (List.ofFn o).take i.val
  let R := (List.ofFn o).drop i.val
  let S := L.toFinset
  have hchg : chargeClean hn o i ≤ 1 := by
    rw [← hpeak]
    exact Finset.le_sup (f := chargeClean hn o) (Finset.mem_univ i)
  have hcard_k : ((poolClean hk r L ∩ poolClean hk r R) ∪ arcClean hk r (o i)).card ≤ p * n := by
    calc ((poolClean hk r L ∩ poolClean hk r R) ∪ arcClean hk r (o i)).card
        ≤ (Finset.univ : Finset (Fin (p * n))).card := Finset.card_le_card (Finset.subset_univ _)
      _ = p * n := Fintype.card_fin (p * n)
  let Ends := Finset.univ.filter (fun w : Fin (p * n) => w ∉ S ∧ prev hk w ∈ S)
  let strip : Fin (p * n) → Finset (Fin (p * n)) := fun w =>
    (Finset.univ : Finset (Fin (5 * r - 3))).image (fun a => step hk w a.val)
  have hsub : poolClean hk r L ∩ poolClean hk r R ⊆ (runStarts hk S ∪ Ends).biUnion strip := by
    intro z hz
    rcases Finset.mem_inter.mp hz with ⟨hzL, hzR⟩
    simp only [poolClean, Finset.mem_biUnion, List.mem_toFinset, arcClean, Finset.mem_image,
      Finset.mem_univ, true_and] at hzL hzR
    rcases hzL with ⟨x, hxL, ⟨a, rfl⟩⟩
    rcases hzR with ⟨y, hyR, ⟨b, hyb⟩⟩
    have hxS : (prev hk)^[a.val] (step hk x a.val) ∈ S := by
      rw [prev_iter_step]
      exact List.mem_toFinset.mpr hxL
    have hyNotS : (prev hk)^[b.val] (step hk x a.val) ∉ S := by
      rw [← hyb, prev_iter_step, List.mem_toFinset]
      exact (mem_drop_iff_not_mem_take o hall.1 i.val (by omega) y).mp hyR
    obtain ⟨t, ht, hflip⟩ := exists_flip (fun m => (prev hk)^[m] (step hk x a.val) ∈ S)
      (5 * r - 3) a.val b.val (by have := a.isLt; omega) (by have := b.isLt; omega) hxS hyNotS
    simp only [Finset.mem_biUnion]
    refine ⟨(prev hk)^[t] (step hk x a.val), ?_, ?_⟩
    · simp only [Finset.mem_union, runStarts, Ends, Finset.mem_filter, Finset.mem_univ, true_and]
      rwa [Function.iterate_succ_apply'] at hflip
    · simp only [strip, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨t, ht⟩, step_prev_iter hk (step hk x a.val) t⟩
  have hruns : (runStarts hk S).card ≤ p := hall.2 ⟨i.val, by omega⟩
  have hends : Ends.card = (runStarts hk S).card := card_ends_eq_runStarts hk S
  have hpool : (poolClean hk r L ∩ poolClean hk r R).card ≤ 2 * p * (5 * r - 3) := by
    calc (poolClean hk r L ∩ poolClean hk r R).card
        ≤ ((runStarts hk S ∪ Ends).biUnion strip).card := Finset.card_le_card hsub
      _ ≤ ∑ w ∈ runStarts hk S ∪ Ends, (strip w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ runStarts hk S ∪ Ends, (5 * r - 3) := by
          apply Finset.sum_le_sum
          intro w _
          calc (strip w).card ≤ (Finset.univ : Finset (Fin (5 * r - 3))).card := Finset.card_image_le
            _ = 5 * r - 3 := Fintype.card_fin _
      _ = (runStarts hk S ∪ Ends).card * (5 * r - 3) := by simp
      _ ≤ ((runStarts hk S).card + Ends.card) * (5 * r - 3) :=
          Nat.mul_le_mul_right _ (Finset.card_union_le _ _)
      _ ≤ (2 * p) * (5 * r - 3) := by
          apply Nat.mul_le_mul_right; omega
  have harc : (arcClean hk r (o i)).card ≤ 5 * r - 2 := by
    calc (arcClean hk r (o i)).card ≤ (Finset.univ : Finset (Fin (5 * r - 2))).card :=
          Finset.card_image_le
      _ = 5 * r - 2 := Fintype.card_fin _
  have hcard_b : ((poolClean hk r L ∩ poolClean hk r R) ∪ arcClean hk r (o i)).card ≤
      (2 * p + 1) * (5 * r - 3) + 1 := by
    have h1 := Finset.card_union_le (poolClean hk r L ∩ poolClean hk r R) (arcClean hk r (o i))
    have h2 : (2 * p + 1) * (5 * r - 3) + 1 = 2 * p * (5 * r - 3) + (5 * r - 2) := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    omega
  have hmin : ((poolClean hk r L ∩ poolClean hk r R) ∪ arcClean hk r (o i)).card ≤
      min (p * n) ((2 * p + 1) * (5 * r - 3) + 1) :=
    le_min hcard_k hcard_b
  exact Nat.add_le_add hmin hchg

def pack {n p : ℕ} (_hn : 0 < n) (hp : 0 < p)
    (π : Equiv.Perm (Fin n)) (σ : Fin n → Equiv.Perm (Fin p)) (t : Fin (p * n)) : Fin (p * n) :=
  let b := divP hp t
  let c := modP hp t
  ⟨(σ b c).val * n + (π b).val, by
    have h1 := (π b).isLt
    have h2 : ((σ b c).val + 1) * n ≤ p * n := Nat.mul_le_mul_right n (σ b c).isLt
    rw [Nat.succ_mul] at h2; omega⟩

lemma res_pack {n p : ℕ} (hn : 0 < n) (hp : 0 < p)
    (π : Equiv.Perm (Fin n)) (σ : Fin n → Equiv.Perm (Fin p)) (t : Fin (p * n)) :
    res hn (pack hn hp π σ t) = π (divP hp t) := by
  ext
  simp only [res, pack, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (π _).isLt]

lemma div_pack {n p : ℕ} (hn : 0 < n) (hp : 0 < p)
    (π : Equiv.Perm (Fin n)) (σ : Fin n → Equiv.Perm (Fin p)) (t : Fin (p * n)) :
    (pack hn hp π σ t).val / n = (σ (divP hp t) (modP hp t)).val := by
  simp only [pack]
  rw [Nat.mul_comm _ n, Nat.mul_add_div hn, Nat.div_eq_of_lt (π _).isLt, Nat.add_zero]

lemma pack_bijective {n p : ℕ} (hn : 0 < n) (hp : 0 < p)
    (π : Equiv.Perm (Fin n)) (σ : Fin n → Equiv.Perm (Fin p)) :
    Function.Bijective (pack hn hp π σ) := by
  let inv : Fin (p * n) → Fin (p * n) := fun w =>
    let j : Fin n := res hn w
    let q : Fin p := ⟨w.val / n, (Nat.div_lt_iff_lt_mul hn).mpr w.isLt⟩
    let b : Fin n := π.symm j
    let c : Fin p := (σ b).symm q
    mkBlock b c
  refine Function.bijective_iff_has_inverse.mpr ⟨inv, ?_, ?_⟩
  · intro t
    dsimp only [inv]
    have hb : π.symm (res hn (pack hn hp π σ t)) = divP hp t := by
      rw [res_pack, Equiv.symm_apply_apply]
    have hq : (⟨(pack hn hp π σ t).val / n, (Nat.div_lt_iff_lt_mul hn).mpr (pack hn hp π σ t).isLt⟩ : Fin p) =
        σ (divP hp t) (modP hp t) := by
      ext; exact div_pack hn hp π σ t
    rw [hb, hq, Equiv.symm_apply_apply]
    exact mkBlock_divP_modP hp t
  · intro w
    ext
    dsimp only [pack, inv]
    set j : Fin n := res hn w
    set q : Fin p := ⟨w.val / n, (Nat.div_lt_iff_lt_mul hn).mpr w.isLt⟩
    set b : Fin n := π.symm j
    set c : Fin p := (σ b).symm q
    rw [divP_mkBlock hp b c, modP_mkBlock hp b c, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    dsimp only [q, j, res]
    rw [Nat.mul_comm (w.val / n) n]
    exact Nat.div_add_mod w.val n

lemma pack_injective {n p : ℕ} (hn : 0 < n) (hp : 0 < p)
    {π1 π2 : Equiv.Perm (Fin n)} {σ1 σ2 : Fin n → Equiv.Perm (Fin p)}
    (h : pack hn hp π1 σ1 = pack hn hp π2 σ2) :
    π1 = π2 ∧ σ1 = σ2 := by
  have hπ : π1 = π2 := by
    ext b
    let t := mkBlock b ⟨0, hp⟩
    have ht := congrArg (fun f => (res hn (f t)).val) h
    rw [res_pack, res_pack, divP_mkBlock] at ht
    exact ht
  subst hπ
  refine ⟨rfl, ?_⟩
  funext b
  ext c
  let t := mkBlock b c
  have ht := congrArg (fun f => (f t).val / n) h
  rw [div_pack, div_pack, divP_mkBlock, modP_mkBlock] at ht
  exact ht

lemma peakClean_pack {n p : ℕ} (hn : 0 < n) (hp : 2 ≤ p)
    (π : Equiv.Perm (Fin n)) (σ : Fin n → Equiv.Perm (Fin p)) :
    peakClean hn (pack hn (by omega : 0 < p) π σ) = 1 := by
  have hp0 : 0 < p := by omega
  apply le_antisymm
  · apply Finset.sup_le
    intro i _
    let b0 : Fin n := divP hp0 i
    have hsub : labelsList hn ((List.ofFn (pack hn hp0 π σ)).take i.val) ∩
        labelsList hn ((List.ofFn (pack hn hp0 π σ)).drop i.val) ⊆ {π b0} := by
      intro j hj
      rcases Finset.mem_inter.mp hj with ⟨hL, hR⟩
      simp only [labelsList, Finset.mem_filter, Finset.mem_univ, true_and] at hL hR
      rcases hL with ⟨w1, hw1, rfl⟩
      rcases hR with ⟨w2, hw2, hres2⟩
      rw [mem_take_ofFn_iff _ i.val (by omega)] at hw1
      rw [mem_drop_ofFn_iff _ i.val (by omega)] at hw2
      rcases hw1 with ⟨t1, ht1, rfl⟩
      rcases hw2 with ⟨t2, ht2, rfl⟩
      rw [res_pack, res_pack] at hres2
      rw [res_pack]
      have heq := π.injective hres2
      have hv := congrArg Fin.val heq
      dsimp only [divP] at hv
      have hle1 : t1.val / p ≤ i.val / p := Nat.div_le_div_right (by omega)
      have hle2 : i.val / p ≤ t2.val / p := Nat.div_le_div_right ht2
      have hb : divP hp0 t1 = b0 := by ext; dsimp [divP, b0]; omega
      rw [hb]
      exact Finset.mem_singleton_self _
    calc chargeClean hn (pack hn hp0 π σ) i
        ≤ ({π b0} : Finset (Fin n)).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton _
  · exact one_le_peakClean hn hp _ (pack_bijective hn hp0 π σ)

lemma contiguity_of_peak_one {n p : ℕ} (hn : 0 < n) (hp : 2 ≤ p)
    (o : Fin (p * n) → Fin (p * n)) (ho : Function.Bijective o)
    (hpeak : peakClean hn o = 1)
    (t1 t2 t3 : Fin (p * n)) (h12 : t1.val < t2.val) (h23 : t2.val < t3.val)
    (h13 : res hn (o t1) = res hn (o t3)) :
    res hn (o t2) = res hn (o t1) := by
  by_contra hne
  obtain ⟨w, hwne, hwres⟩ := exists_two_copies hn hp (res hn (o t2)) (o t2)
  obtain ⟨t2', rfl⟩ := ho.2 w
  have ht2'_ne : t2' ≠ t2 := fun h => hwne (congrArg o h)
  have hval_ne : t2'.val ≠ t2.val := fun h => ht2'_ne (Fin.ext h)
  rcases lt_or_gt_of_ne hval_ne with hlt | hgt
  · have h2le : 2 ≤ chargeClean hn o t2 := by
      have hsub : ({res hn (o t1), res hn (o t2)} : Finset (Fin n)) ⊆
          labelsList hn ((List.ofFn o).take t2.val) ∩ labelsList hn ((List.ofFn o).drop t2.val) := by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        simp only [Finset.mem_inter, labelsList, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hj with rfl | rfl
        · exact ⟨⟨o t1, (mem_take_ofFn_iff o t2.val (by omega) _).mpr ⟨t1, h12, rfl⟩, rfl⟩,
                 ⟨o t3, (mem_drop_ofFn_iff o t2.val (by omega) _).mpr ⟨t3, by omega, rfl⟩, h13.symm⟩⟩
        · exact ⟨⟨o t2', (mem_take_ofFn_iff o t2.val (by omega) _).mpr ⟨t2', hlt, rfl⟩, hwres⟩,
                 ⟨o t2, (mem_drop_ofFn_iff o t2.val (by omega) _).mpr ⟨t2, le_rfl, rfl⟩, rfl⟩⟩
      calc 2 = ({res hn (o t1), res hn (o t2)} : Finset (Fin n)).card :=
            (Finset.card_pair (Ne.symm hne)).symm
        _ ≤ chargeClean hn o t2 := Finset.card_le_card hsub
    have hle1 : chargeClean hn o t2 ≤ 1 := by
      rw [← hpeak]; exact Finset.le_sup (f := chargeClean hn o) (Finset.mem_univ t2)
    omega
  · let i : Fin (p * n) := ⟨t2.val + 1, by omega⟩
    have h2le : 2 ≤ chargeClean hn o i := by
      have hsub : ({res hn (o t1), res hn (o t2)} : Finset (Fin n)) ⊆
          labelsList hn ((List.ofFn o).take i.val) ∩ labelsList hn ((List.ofFn o).drop i.val) := by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        simp only [Finset.mem_inter, labelsList, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hj with rfl | rfl
        · exact ⟨⟨o t1, (mem_take_ofFn_iff o i.val (by omega) _).mpr ⟨t1, by dsimp [i]; omega, rfl⟩, rfl⟩,
                 ⟨o t3, (mem_drop_ofFn_iff o i.val (by omega) _).mpr ⟨t3, by dsimp [i]; omega, rfl⟩, h13.symm⟩⟩
        · exact ⟨⟨o t2, (mem_take_ofFn_iff o i.val (by omega) _).mpr ⟨t2, by dsimp [i]; omega, rfl⟩, rfl⟩,
                 ⟨o t2', (mem_drop_ofFn_iff o i.val (by omega) _).mpr ⟨t2', by dsimp [i]; omega, rfl⟩, hwres⟩⟩
      calc 2 = ({res hn (o t1), res hn (o t2)} : Finset (Fin n)).card :=
            (Finset.card_pair (Ne.symm hne)).symm
        _ ≤ chargeClean hn o i := Finset.card_le_card hsub
    have hle1 : chargeClean hn o i ≤ 1 := by
      rw [← hpeak]; exact Finset.le_sup (f := chargeClean hn o) (Finset.mem_univ i)
    omega

lemma card_fiber_eq_p {n p : ℕ} (hn : 0 < n)
    (o : Fin (p * n) → Fin (p * n)) (ho : Function.Bijective o) (j : Fin n) :
    (Finset.univ.filter (fun t : Fin (p * n) => res hn (o t) = j)).card = p := by
  let e := Equiv.ofBijective o ho
  let f : Fin p → Fin (p * n) := fun q =>
    e.symm ⟨q.val * n + j.val, by
      have := j.isLt
      have h : (q.val + 1) * n ≤ p * n := Nat.mul_le_mul_right n q.isLt
      rw [Nat.succ_mul] at h; omega⟩
  have hfinj : Function.Injective f := by
    intro q1 q2 heq
    have hv := congrArg (fun x => (e x).val / n) heq
    simp only [f, Equiv.apply_symm_apply] at hv
    rw [Nat.mul_comm q1.val n, Nat.mul_add_div hn, Nat.div_eq_of_lt j.isLt, Nat.add_zero,
      Nat.mul_comm q2.val n, Nat.mul_add_div hn, Nat.div_eq_of_lt j.isLt, Nat.add_zero] at hv
    exact Fin.ext hv
  have himg : (Finset.univ : Finset (Fin p)).image f =
      Finset.univ.filter (fun t : Fin (p * n) => res hn (o t) = j) := by
    ext t
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨q, rfl⟩
      have h1 : o (f q) = ⟨q.val * n + j.val, by
        have := j.isLt
        have h : (q.val + 1) * n ≤ p * n := Nat.mul_le_mul_right n q.isLt
        rw [Nat.succ_mul] at h; omega⟩ := by
        change e (e.symm _) = _; exact Equiv.apply_symm_apply e _
      rw [h1]
      ext
      simp only [res, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt j.isLt]
    · intro hres
      let q : Fin p := ⟨(o t).val / n, (Nat.div_lt_iff_lt_mul hn).mpr (o t).isLt⟩
      refine ⟨q, ?_⟩
      apply e.injective
      change e (f q) = o t
      dsimp only [f]
      rw [Equiv.apply_symm_apply]
      ext
      dsimp only [q]
      have hrv : (o t).val % n = j.val := congrArg Fin.val hres
      rw [← hrv, Nat.mul_comm ((o t).val / n) n]
      exact Nat.div_add_mod (o t).val n
  rw [← himg, Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_fin]

lemma card_fin_interval {k : ℕ} (a m : ℕ) (ham : a ≤ m) (hmk : m < k) :
    (Finset.univ.filter (fun t : Fin k => a ≤ t.val ∧ t.val ≤ m)).card = m - a + 1 := by
  let f : Fin (m - a + 1) → Fin k := fun d => ⟨a + d.val, by have := d.isLt; omega⟩
  have hfinj : Function.Injective f := by
    intro d1 d2 heq
    have := congrArg Fin.val heq
    dsimp [f] at this
    exact Fin.ext (by omega)
  have himg : (Finset.univ : Finset (Fin (m - a + 1))).image f =
      Finset.univ.filter (fun t : Fin k => a ≤ t.val ∧ t.val ≤ m) := by
    ext t
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨d, rfl⟩; dsimp [f]; have := d.isLt; omega
    · rintro ⟨ha, hm⟩
      refine ⟨⟨t.val - a, by omega⟩, ?_⟩
      ext; dsimp [f]; omega
  rw [← himg, Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_fin]

lemma exists_pack_of_peak_one {n p : ℕ} (hn : 0 < n) (hp : 2 ≤ p)
    (o : Fin (p * n) → Fin (p * n)) (ho : Function.Bijective o)
    (hpeak : peakClean hn o = 1) :
    ∃ (π : Equiv.Perm (Fin n)) (σ : Fin n → Equiv.Perm (Fin p)),
      pack hn (by omega : 0 < p) π σ = o := by
  have hp0 : 0 < p := by omega
  have hblocks : ∀ (b : ℕ), b ≤ n → ∀ (b' : Fin n), b'.val < b → ∀ (c : Fin p),
      res hn (o (mkBlock b' c)) = res hn (o (mkBlock b' ⟨0, hp0⟩)) := by
    intro b
    induction b with
    | zero => intro _ b' hb'; omega
    | succ b ih =>
      intro hbn
      have hih := ih (by omega)
      have hb_lt : b < n := by omega
      let bf : Fin n := ⟨b, hb_lt⟩
      let t0 : Fin (p * n) := mkBlock bf ⟨0, hp0⟩
      let j : Fin n := res hn (o t0)
      let Tj := Finset.univ.filter (fun t : Fin (p * n) => res hn (o t) = j)
      have hTj_card : Tj.card = p := card_fiber_eq_p hn o ho j
      have ht0_mem : t0 ∈ Tj := by simp [Tj, j]
      have hge_t0 : ∀ t ∈ Tj, b * p ≤ t.val := by
        intro t ht
        by_contra hlt
        push Not at hlt
        have htres : res hn (o t) = j := (Finset.mem_filter.mp ht).2
        let b' : Fin n := divP hp0 t
        have hb' : b'.val < b := (Nat.div_lt_iff_lt_mul hp0).mpr hlt
        let c0 : Fin p := modP hp0 t
        have hteq : mkBlock b' c0 = t := mkBlock_divP_modP hp0 t
        have hbase : res hn (o (mkBlock b' ⟨0, hp0⟩)) = j := by
          rw [← hih b' hb' c0, hteq]; exact htres
        let f : Fin p → Fin (p * n) := fun c => mkBlock b' c
        have hfinj : Function.Injective f := by
          intro c1 c2 heq; have := congrArg Fin.val heq; dsimp [f, mkBlock] at this; exact Fin.ext (by omega)
        have hsub : insert t0 ((Finset.univ : Finset (Fin p)).image f) ⊆ Tj := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hx
          rcases hx with rfl | ⟨c, rfl⟩
          · exact ht0_mem
          · simp only [Tj, Finset.mem_filter, Finset.mem_univ, true_and]
            rw [hih b' hb' c, hbase]
        have ht0_not : t0 ∉ (Finset.univ : Finset (Fin p)).image f := by
          simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
          intro c heq
          have hv := congrArg Fin.val heq
          dsimp [f, t0, mkBlock, bf] at hv
          have h1 : (b'.val + 1) * p ≤ b * p := Nat.mul_le_mul_right p hb'
          rw [Nat.succ_mul] at h1
          have := c.isLt; omega
        have hbig : p + 1 ≤ Tj.card := by
          calc p + 1 = ((Finset.univ : Finset (Fin p)).image f).card + 1 := by
                rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_fin]
            _ = (insert t0 ((Finset.univ : Finset (Fin p)).image f)).card :=
                (Finset.card_insert_of_notMem ht0_not).symm
            _ ≤ Tj.card := Finset.card_le_card hsub
        omega
      let hi := Tj.max' ⟨t0, ht0_mem⟩
      have hhi_mem : hi ∈ Tj := Finset.max'_mem Tj ⟨t0, ht0_mem⟩
      have hhi_ge : b * p ≤ hi.val := hge_t0 hi hhi_mem
      have hTj_eq : Tj = Finset.univ.filter (fun t : Fin (p * n) => b * p ≤ t.val ∧ t.val ≤ hi.val) := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro ht
          exact ⟨hge_t0 t ht, Finset.le_max' Tj t ht⟩
        · rintro ⟨hle1, hle2⟩
          by_cases h1 : t.val = b * p
          · have : t = t0 := by ext; dsimp [t0, mkBlock, bf]; omega
            subst this; exact ht0_mem
          · by_cases h2 : t.val = hi.val
            · have : t = hi := Fin.ext h2; subst this; exact hhi_mem
            · have hres_hi : res hn (o hi) = j := (Finset.mem_filter.mp hhi_mem).2
              have hres_t := contiguity_of_peak_one hn hp o ho hpeak t0 t hi
                (by dsimp [t0, mkBlock, bf]; omega) (by omega) hres_hi.symm
              simp only [Tj, Finset.mem_filter, Finset.mem_univ, true_and]
              exact hres_t
      have hhi_val : hi.val = b * p + p - 1 := by
        have h1 := card_fin_interval (b * p) hi.val hhi_ge hi.isLt
        rw [← hTj_eq, hTj_card] at h1
        omega
      intro b' hb' c
      by_cases hbb : b'.val < b
      · exact hih b' hbb c
      · have hbeq : b' = bf := by ext; dsimp [bf]; omega
        subst hbeq
        have hmem : mkBlock bf c ∈ Tj := by
          rw [hTj_eq]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, mkBlock, bf]
          have := c.isLt; omega
        exact (Finset.mem_filter.mp hmem).2
  have hbl : ∀ (b : Fin n) (c : Fin p),
      res hn (o (mkBlock b c)) = res hn (o (mkBlock b ⟨0, hp0⟩)) :=
    fun b c => hblocks n le_rfl b b.isLt c
  let fπ : Fin n → Fin n := fun b => res hn (o (mkBlock b ⟨0, hp0⟩))
  have hfπ_inj : Function.Injective fπ := by
    intro b1 b2 heq
    by_contra hne
    let j := fπ b1
    let Tj := Finset.univ.filter (fun t : Fin (p * n) => res hn (o t) = j)
    let f : Fin p → Fin (p * n) := fun c => mkBlock b1 c
    let t2 : Fin (p * n) := mkBlock b2 ⟨0, hp0⟩
    have hfinj : Function.Injective f := by
      intro c1 c2 h; have := congrArg Fin.val h; dsimp [f, mkBlock] at this; exact Fin.ext (by omega)
    have ht2_not : t2 ∉ (Finset.univ : Finset (Fin p)).image f := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
      intro c hc
      have hdiv := congrArg (divP hp0) hc
      rw [divP_mkBlock, divP_mkBlock] at hdiv
      exact hne hdiv
    have hsub : insert t2 ((Finset.univ : Finset (Fin p)).image f) ⊆ Tj := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hx
      simp only [Tj, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hx with rfl | ⟨c, rfl⟩
      · exact heq.symm
      · exact hbl b1 c
    have hbig : p + 1 ≤ Tj.card := by
      calc p + 1 = ((Finset.univ : Finset (Fin p)).image f).card + 1 := by
            rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_fin]
        _ = (insert t2 ((Finset.univ : Finset (Fin p)).image f)).card :=
            (Finset.card_insert_of_notMem ht2_not).symm
        _ ≤ Tj.card := Finset.card_le_card hsub
    have hcard : Tj.card = p := card_fiber_eq_p hn o ho j
    omega
  let π : Equiv.Perm (Fin n) := Equiv.ofBijective fπ (Finite.injective_iff_bijective.mp hfπ_inj)
  let fσ : Fin n → Fin p → Fin p := fun b c =>
    ⟨(o (mkBlock b c)).val / n, (Nat.div_lt_iff_lt_mul hn).mpr (o _).isLt⟩
  have hfσ_inj : ∀ b : Fin n, Function.Injective (fσ b) := by
    intro b c1 c2 heq
    have hdiv : (o (mkBlock b c1)).val / n = (o (mkBlock b c2)).val / n := congrArg Fin.val heq
    have hmod : (o (mkBlock b c1)).val % n = (o (mkBlock b c2)).val % n :=
      congrArg Fin.val ((hbl b c1).trans (hbl b c2).symm)
    have hoeq : o (mkBlock b c1) = o (mkBlock b c2) := by
      ext
      rw [← Nat.div_add_mod (o (mkBlock b c1)).val n,
        ← Nat.div_add_mod (o (mkBlock b c2)).val n, hdiv, hmod]
    have hidx := congrArg (modP hp0) (ho.1 hoeq)
    rwa [modP_mkBlock, modP_mkBlock] at hidx
  let σ : Fin n → Equiv.Perm (Fin p) := fun b =>
    Equiv.ofBijective (fσ b) (Finite.injective_iff_bijective.mp (hfσ_inj b))
  refine ⟨π, σ, ?_⟩
  funext t
  ext
  dsimp only [pack, π, σ, Equiv.ofBijective_apply, fπ, fσ]
  have ht_eq : mkBlock (divP hp0 t) (modP hp0 t) = t := mkBlock_divP_modP hp0 t
  have hmod : (res hn (o (mkBlock (divP hp0 t) ⟨0, hp0⟩))).val = (o t).val % n := by
    rw [← hbl (divP hp0 t) (modP hp0 t), ht_eq]; rfl
  rw [ht_eq, hmod, Nat.mul_comm ((o t).val / n) n]
  exact Nat.div_add_mod (o t).val n

def prefixImg {n : ℕ} (π : Equiv.Perm (Fin n)) (b : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter (fun i : Fin n => i.val < b)).image π

def IsCyclicGrowth {n : ℕ} (hn : 0 < n) (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ b : Fin (n + 1), (runStarts hn (prefixImg π b.val)).card ≤ 1

lemma card_runStarts_lift {n p : ℕ} (hn : 0 < n) (hp : 0 < p) (A : Finset (Fin n)) :
    (runStarts (Nat.mul_pos hp hn) (Finset.univ.filter (fun w : Fin (p * n) => res hn w ∈ A))).card =
      p * (runStarts hn A).card := by
  have hk : 0 < p * n := Nat.mul_pos hp hn
  let f : Fin p × Fin n → Fin (p * n) := fun x =>
    ⟨x.1.val * n + x.2.val, by
      have := x.2.isLt
      have h : (x.1.val + 1) * n ≤ p * n := Nat.mul_le_mul_right n x.1.isLt
      rw [Nat.succ_mul] at h; omega⟩
  have hfinj : Function.Injective f := by
    rintro ⟨q1, j1⟩ ⟨q2, j2⟩ heq
    have hv := congrArg Fin.val heq
    dsimp [f] at hv
    have hj : j1.val = j2.val := by
      have hmod := congrArg (· % n) hv
      rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt j1.isLt,
        Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt j2.isLt] at hmod
      exact hmod
    have hq : q1.val = q2.val := by
      have hdiv := congrArg (· / n) hv
      rw [Nat.mul_comm q1.val n, Nat.mul_add_div hn, Nat.div_eq_of_lt j1.isLt, Nat.add_zero,
        Nat.mul_comm q2.val n, Nat.mul_add_div hn, Nat.div_eq_of_lt j2.isLt, Nat.add_zero] at hdiv
      exact hdiv
    exact Prod.ext (Fin.ext hq) (Fin.ext hj)
  have himg : ((Finset.univ : Finset (Fin p)) ×ˢ runStarts hn A).image f =
      runStarts hk (Finset.univ.filter (fun w : Fin (p * n) => res hn w ∈ A)) := by
    ext w
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and,
      runStarts, Finset.mem_filter]
    constructor
    · rintro ⟨⟨q, j⟩, ⟨hjA, hprev⟩, rfl⟩
      have hres : res hn (f (q, j)) = j := by
        ext; simp only [res, f, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt j.isLt]
      rw [res_prev hn hp, hres]
      exact ⟨hjA, hprev⟩
    · rintro ⟨hwA, hprev⟩
      rw [res_prev hn hp] at hprev
      let q : Fin p := ⟨w.val / n, (Nat.div_lt_iff_lt_mul hn).mpr w.isLt⟩
      refine ⟨(q, res hn w), ⟨hwA, hprev⟩, ?_⟩
      ext
      dsimp only [f, q, res]
      rw [Nat.mul_comm (w.val / n) n]
      exact Nat.div_add_mod w.val n
  rw [← himg, Finset.card_image_of_injective _ hfinj, Finset.card_product,
    Finset.card_univ, Fintype.card_fin]

lemma runStarts_nonempty_of_ne {m : ℕ} (hm : 0 < m) (A : Finset (Fin m))
    (hne : A.Nonempty) (hnot : ∃ y : Fin m, y ∉ A) :
    (runStarts hm A).Nonempty := by
  rcases hne with ⟨x, hx⟩
  rcases hnot with ⟨y, hy⟩
  let d := (x.val + m - y.val) % m
  have hstep : step hm y d = x := by
    ext
    simp only [step, d]
    rw [Nat.add_mod_mod]
    have : y.val + (x.val + m - y.val) = x.val + m := by have := y.isLt; omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt]
  obtain ⟨t, _, ht⟩ := exists_runStart_between hm A y d hy (hstep ▸ hx)
  exact ⟨step hm y (t + 1), ht⟩

lemma prev_or_next_mem_of_runStarts_le_one {n : ℕ} (hn : 0 < n) (A : Finset (Fin n))
    (hne : A.Nonempty) (j : Fin n) (hj : j ∉ A)
    (hle : (runStarts hn (insert j A)).card ≤ 1) :
    prev hn j ∈ A ∨ next hn j ∈ A := by
  rcases hne with ⟨a, ha⟩
  have haj : a ≠ j := fun h => hj (h ▸ ha)
  have hn2 : 2 ≤ n := by
    calc 2 = ({a, j} : Finset (Fin n)).card := (Finset.card_pair haj).symm
      _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = n := Fintype.card_fin n
  by_contra hboth
  push Not at hboth
  rcases hboth with ⟨hprev, hnext⟩
  obtain ⟨x, hx⟩ := runStarts_nonempty_of_ne hn A ⟨a, ha⟩ ⟨j, hj⟩
  have hxA : x ∈ A := (Finset.mem_filter.mp hx).2.1
  have hxprev : prev hn x ∉ A := (Finset.mem_filter.mp hx).2.2
  have hxj : x ≠ j := fun h => hj (h ▸ hxA)
  have hx_in : x ∈ runStarts hn (insert j A) := by
    simp only [runStarts, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, not_or]
    refine ⟨Or.inr hxA, ?_, hxprev⟩
    intro heq
    have : x = next hn j := by rw [← heq, next_prev]
    exact hnext (this ▸ hxA)
  have hj_in : j ∈ runStarts hn (insert j A) := by
    simp only [runStarts, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, not_or]
    exact ⟨Or.inl trivial, prev_ne_self hn2 j, hprev⟩
  have hsub : ({x, j} : Finset (Fin n)) ⊆ runStarts hn (insert j A) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have h2 : 2 ≤ (runStarts hn (insert j A)).card := by
    calc 2 = ({x, j} : Finset (Fin n)).card := (Finset.card_pair hxj).symm
      _ ≤ (runStarts hn (insert j A)).card := Finset.card_le_card hsub
  omega

lemma take_pack_block {n p : ℕ} (hn : 0 < n) (hp : 0 < p)
    (π : Equiv.Perm (Fin n)) (σ : Fin n → Equiv.Perm (Fin p)) (b : ℕ) (hb : b ≤ n) :
    ((List.ofFn (pack hn hp π σ)).take (b * p)).toFinset =
      Finset.univ.filter (fun w : Fin (p * n) => res hn w ∈ prefixImg π b) := by
  have hbp : b * p ≤ p * n := by rw [Nat.mul_comm p n]; exact Nat.mul_le_mul_right p hb
  ext w
  simp only [List.mem_toFinset, mem_take_ofFn_iff _ (b * p) hbp, Finset.mem_filter,
    Finset.mem_univ, true_and, prefixImg, Finset.mem_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [res_pack]
    exact ⟨divP hp t, (Nat.div_lt_iff_lt_mul hp).mpr ht, rfl⟩
  · rintro ⟨i, hi, hres⟩
    let q : Fin p := ⟨w.val / n, (Nat.div_lt_iff_lt_mul hn).mpr w.isLt⟩
    let c : Fin p := (σ i).symm q
    let t : Fin (p * n) := mkBlock i c
    refine ⟨t, ?_, ?_⟩
    · have : (i.val + 1) * p ≤ b * p := Nat.mul_le_mul_right p hi
      rw [Nat.succ_mul] at this; have := c.isLt; dsimp [t, mkBlock]; omega
    · ext
      dsimp only [pack, t]
      rw [divP_mkBlock hp i c, modP_mkBlock hp i c, Equiv.apply_symm_apply]
      dsimp only [q]
      have hrv : (π i).val = w.val % n := congrArg Fin.val hres
      rw [hrv, Nat.mul_comm (w.val / n) n]
      exact Nat.div_add_mod w.val n

lemma allowedClean_pack_iff {n p : ℕ} (hn : 0 < n) (hp : 2 ≤ p)
    (π : Equiv.Perm (Fin n)) (σ : Fin n → Equiv.Perm (Fin p)) :
    allowedClean (Nat.mul_pos (by omega : 0 < p) hn) p (pack hn (by omega : 0 < p) π σ) ↔
      IsCyclicGrowth hn π := by
  have hp0 : 0 < p := by omega
  have hk : 0 < p * n := Nat.mul_pos hp0 hn
  constructor
  · intro hall b
    have hbp : b.val * p < p * n + 1 := by
      have : b.val * p ≤ n * p := Nat.mul_le_mul_right p (Nat.lt_succ_iff.mp b.isLt)
      rw [Nat.mul_comm n p] at this; omega
    have h1 := hall.2 ⟨b.val * p, hbp⟩
    rw [take_pack_block hn hp0 π σ b.val (Nat.lt_succ_iff.mp b.isLt),
      card_runStarts_lift hn hp0] at h1
    have h2 : p * (runStarts hn (prefixImg π b.val)).card ≤ p * 1 := by simpa using h1
    exact Nat.le_of_mul_le_mul_left h2 hp0
  · intro hcg
    refine ⟨pack_bijective hn hp0 π σ, ?_⟩
    intro u
    by_cases huk : u.val = p * n
    · have hall_u : ((List.ofFn (pack hn hp0 π σ)).take u.val).toFinset = Finset.univ := by
        ext w
        simp only [List.mem_toFinset, Finset.mem_univ, iff_true, huk,
          mem_take_ofFn_iff _ (p * n) le_rfl]
        obtain ⟨t, rfl⟩ := (pack_bijective hn hp0 π σ).2 w
        exact ⟨t, t.isLt, rfl⟩
      rw [hall_u]
      have hempty : runStarts hk (Finset.univ : Finset (Fin (p * n))) = ∅ := by
        ext w; simp [runStarts]
      rw [hempty, Finset.card_empty]
      exact Nat.zero_le p
    · have hu_lt : u.val < p * n := by have := u.isLt; omega
      have hu_le : u.val ≤ p * n := Nat.le_of_lt hu_lt
      let b := u.val / p
      have hb_lt : b < n := (Nat.div_lt_iff_lt_mul hp0).mpr (by rw [Nat.mul_comm n p]; exact hu_lt)
      have hbp_le_u : b * p ≤ u.val := by
        dsimp [b]; rw [Nat.mul_comm]; exact Nat.mul_div_le u.val p
      have hbp_le_k : b * p ≤ p * n := hbp_le_u.trans hu_le
      by_cases hb0 : b = 0
      · have hu_lt_p : u.val < p := by
          have := Nat.div_add_mod u.val p
          have hmod := Nat.mod_lt u.val hp0
          dsimp [b] at hb0; rw [hb0] at this; omega
        calc (runStarts hk (((List.ofFn (pack hn hp0 π σ)).take u.val).toFinset)).card
            ≤ (((List.ofFn (pack hn hp0 π σ)).take u.val).toFinset).card :=
              Finset.card_le_card (fun w hw => (Finset.mem_filter.mp hw).2.1)
          _ ≤ ((List.ofFn (pack hn hp0 π σ)).take u.val).length := List.toFinset_card_le _
          _ ≤ u.val := List.length_take_le _ _
          _ ≤ p := by omega
      · have hb_pos : 0 < b := Nat.pos_of_ne_zero hb0
        let A := prefixImg π b
        let j : Fin n := π ⟨b, hb_lt⟩
        let Su := ((List.ofFn (pack hn hp0 π σ)).take u.val).toFinset
        let liftA := Finset.univ.filter (fun w : Fin (p * n) => res hn w ∈ A)
        let C := Su.filter (fun w : Fin (p * n) => res hn w = j)
        have hSu_decomp : Su = liftA ∪ C := by
          ext w
          simp only [Finset.mem_union, liftA, C, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro hw
            have hw' := hw
            rw [List.mem_toFinset, mem_take_ofFn_iff _ u.val hu_le] at hw'
            rcases hw' with ⟨t, ht, rfl⟩
            rw [res_pack]
            have htdiv : (divP hp0 t).val ≤ b := Nat.div_le_div_right (Nat.le_of_lt ht)
            by_cases hlt : (divP hp0 t).val < b
            · left
              exact Finset.mem_image.mpr ⟨divP hp0 t,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, rfl⟩
            · right
              refine ⟨hw, ?_⟩
              congr 1; ext; dsimp; omega
          · rintro (hA | ⟨hw, _⟩)
            · have hmem : w ∈ ((List.ofFn (pack hn hp0 π σ)).take (b * p)).toFinset := by
                rw [take_pack_block hn hp0 π σ b (Nat.le_of_lt hb_lt)]
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩
              rw [List.mem_toFinset, mem_take_ofFn_iff _ (b * p) hbp_le_k] at hmem
              rcases hmem with ⟨t, ht, rfl⟩
              rw [List.mem_toFinset, mem_take_ofFn_iff _ u.val hu_le]
              exact ⟨t, lt_of_lt_of_le ht hbp_le_u, rfl⟩
            · exact hw
        have hA_ne : A.Nonempty := ⟨π ⟨0, hn⟩, Finset.mem_image.mpr
          ⟨⟨0, hn⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb_pos⟩, rfl⟩⟩
        have hj_notA : j ∉ A := by
          simp only [A, prefixImg, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
            not_exists, not_and]
          intro i hi heq
          have := congrArg Fin.val (π.injective heq)
          dsimp at this; omega
        have hins : insert j A = prefixImg π (b + 1) := by
          ext x
          simp only [Finset.mem_insert, A, prefixImg, Finset.mem_image, Finset.mem_filter,
            Finset.mem_univ, true_and]
          constructor
          · rintro (rfl | ⟨i, hi, rfl⟩)
            · exact ⟨⟨b, hb_lt⟩, by dsimp; omega, rfl⟩
            · exact ⟨i, by omega, rfl⟩
          · rintro ⟨i, hi, rfl⟩
            by_cases hlt : i.val < b
            · exact Or.inr ⟨i, hlt, rfl⟩
            · left; congr 1; ext; dsimp; omega
        have hcg_b : (runStarts hn A).card ≤ 1 := hcg ⟨b, by omega⟩
        have hcg_b1 : (runStarts hn (insert j A)).card ≤ 1 := by
          rw [hins]; exact hcg ⟨b + 1, by omega⟩
        have hlift_card : (runStarts hk liftA).card ≤ p := by
          rw [card_runStarts_lift hn hp0 A]
          calc p * (runStarts hn A).card ≤ p * 1 := Nat.mul_le_mul_left p hcg_b
            _ = p := Nat.mul_one p
        rcases prev_or_next_mem_of_runStarts_le_one hn A hA_ne j hj_notA hcg_b1 with hprevA | hnextA
        · have hsub : runStarts hk Su ⊆ runStarts hk liftA := by
            intro w hw
            simp only [runStarts, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
            rcases hw with ⟨hwSu, hprevNot⟩
            have hw_lift : w ∈ liftA := by
              rw [hSu_decomp] at hwSu
              rcases Finset.mem_union.mp hwSu with h | hC
              · exact h
              · exfalso
                have hresw : res hn w = j := (Finset.mem_filter.mp hC).2
                have hpLift : prev hk w ∈ liftA := by
                  simp only [liftA, Finset.mem_filter, Finset.mem_univ, true_and]
                  rw [res_prev hn hp0, hresw]
                  exact hprevA
                exact hprevNot (hSu_decomp ▸ Finset.mem_union_left C hpLift)
            exact ⟨hw_lift, fun hpLift => hprevNot (hSu_decomp ▸ Finset.mem_union_left C hpLift)⟩
          exact (Finset.card_le_card hsub).trans hlift_card
        · let φ : Fin (p * n) → Fin (p * n) := fun w => if w ∈ C then next hk w else w
          have hle_lift : (runStarts hk Su).card ≤ (runStarts hk liftA).card := by
            apply Finset.card_le_card_of_injOn φ
            · intro w hw
              simp only [Finset.mem_coe, runStarts, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
              rcases hw with ⟨hwSu, hprevNot⟩
              dsimp only [φ]
              split_ifs with hwC
              · have hresw : res hn w = j := (Finset.mem_filter.mp hwC).2
                simp only [liftA, Finset.mem_filter, Finset.mem_univ, true_and]
                rw [res_next hn hp0, prev_next, hresw]
                exact ⟨hnextA, hj_notA⟩
              · have hw_lift : w ∈ liftA := by
                  rw [hSu_decomp] at hwSu
                  rcases Finset.mem_union.mp hwSu with h | h
                  · exact h
                  · exact absurd h hwC
                exact ⟨hw_lift, fun hpLift => hprevNot (hSu_decomp ▸ Finset.mem_union_left C hpLift)⟩
            · intro w1 hw1 w2 hw2 heq
              simp only [Finset.mem_coe, runStarts, Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
              dsimp only [φ] at heq
              split_ifs at heq with h1 h2 h2
              · exact next_injective hk heq
              · exfalso
                have hp2 : prev hk w2 = w1 := by rw [← heq, prev_next]
                exact hw2.2 (hp2 ▸ (Finset.mem_filter.mp h1).1)
              · exfalso
                have hp1 : prev hk w1 = w2 := by rw [heq, prev_next]
                exact hw1.2 (hp1 ▸ (Finset.mem_filter.mp h2).1)
              · exact heq
          exact hle_lift.trans hlift_card

def stepEquiv {n : ℕ} (hn : 0 < n) (s : Fin n) : Equiv.Perm (Fin n) where
  toFun x := step hn x s.val
  invFun x := (prev hn)^[s.val] x
  left_inv x := prev_iter_step hn x s.val
  right_inv x := step_prev_iter hn x s.val

lemma runStarts_image_stepEquiv {n : ℕ} (hn : 0 < n) (s : Fin n) (A : Finset (Fin n)) :
    runStarts hn (A.image (stepEquiv hn s)) = (runStarts hn A).image (stepEquiv hn s) := by
  ext y
  simp only [runStarts, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨⟨x, hxA, rfl⟩, hprev⟩
    refine ⟨x, ⟨hxA, fun hpx => hprev ⟨prev hn x, hpx, ?_⟩⟩, rfl⟩
    exact (step_prev_comm hn x s.val).symm
  · rintro ⟨x, ⟨hxA, hpx⟩, rfl⟩
    refine ⟨⟨x, hxA, rfl⟩, ?_⟩
    rintro ⟨z, hzA, hz⟩
    have h1 : stepEquiv hn s z = stepEquiv hn s (prev hn x) :=
      hz.trans (step_prev_comm hn x s.val)
    have hzx : z = prev hn x := (stepEquiv hn s).injective h1
    exact hpx (hzx ▸ hzA)

lemma isCyclicGrowth_trans_stepEquiv {n : ℕ} (hn : 0 < n) (s : Fin n) (π : Equiv.Perm (Fin n)) :
    IsCyclicGrowth hn (π.trans (stepEquiv hn s)) ↔ IsCyclicGrowth hn π := by
  constructor <;> intro h b
  · have hb := h b
    have himg : prefixImg (π.trans (stepEquiv hn s)) b.val =
        (prefixImg π b.val).image (stepEquiv hn s) := by
      simp only [prefixImg, Finset.image_image]; rfl
    rw [himg, runStarts_image_stepEquiv,
      Finset.card_image_of_injective _ (stepEquiv hn s).injective] at hb
    exact hb
  · have himg : prefixImg (π.trans (stepEquiv hn s)) b.val =
        (prefixImg π b.val).image (stepEquiv hn s) := by
      simp only [prefixImg, Finset.image_image]; rfl
    rw [himg, runStarts_image_stepEquiv,
      Finset.card_image_of_injective _ (stepEquiv hn s).injective]
    exact h b

def cyclicGrowthEquivProd {n : ℕ} (hn : 0 < n) :
    {π : Equiv.Perm (Fin n) // IsCyclicGrowth hn π} ≃
      Fin n × {π : Equiv.Perm (Fin n) // IsCyclicGrowth hn π ∧ π ⟨0, hn⟩ = ⟨0, hn⟩} where
  toFun x :=
    (x.1 ⟨0, hn⟩,
      ⟨x.1.trans (stepEquiv hn (x.1 ⟨0, hn⟩)).symm,
        by
          have h := (isCyclicGrowth_trans_stepEquiv hn (x.1 ⟨0, hn⟩)
            (x.1.trans (stepEquiv hn (x.1 ⟨0, hn⟩)).symm)).mp
          have heq : (x.1.trans (stepEquiv hn (x.1 ⟨0, hn⟩)).symm).trans
              (stepEquiv hn (x.1 ⟨0, hn⟩)) = x.1 := by
            ext i; simp
          rw [heq] at h
          exact h x.2,
        by
          simp only [Equiv.trans_apply]
          apply (stepEquiv hn (x.1 ⟨0, hn⟩)).injective
          rw [Equiv.apply_symm_apply]
          ext; simp [stepEquiv, step, Nat.mod_eq_of_lt (x.1 ⟨0, hn⟩).isLt]⟩)
  invFun y :=
    ⟨y.2.1.trans (stepEquiv hn y.1),
      (isCyclicGrowth_trans_stepEquiv hn y.1 y.2.1).mpr y.2.2.1⟩
  left_inv x := by
    ext i
    simp
  right_inv y := by
    rcases y with ⟨s, ⟨π, hcg, h0⟩⟩
    have hs : (π.trans (stepEquiv hn s)) ⟨0, hn⟩ = s := by
      simp only [Equiv.trans_apply, h0]
      ext; simp [stepEquiv, step, Nat.mod_eq_of_lt s.isLt]
    apply Prod.ext hs
    apply Subtype.ext
    ext i
    simp [hs]

def interval {n : ℕ} (hn : 0 < n) (a : Fin n) (len : ℕ) : Finset (Fin n) :=
  (Finset.range len).image (fun t => step hn a t)

lemma insert_step_interval {n : ℕ} (hn : 0 < n) (a : Fin n) (len : ℕ) :
    insert (step hn a len) (interval hn a len) = interval hn a (len + 1) := by
  simp only [interval, Finset.range_add_one, Finset.image_insert]

lemma insert_prev_interval {n : ℕ} (hn : 0 < n) (a : Fin n) (len : ℕ) :
    insert (prev hn a) (interval hn a len) = interval hn (prev hn a) (len + 1) := by
  ext x
  simp only [Finset.mem_insert, interval, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro (rfl | ⟨t, ht, rfl⟩)
    · exact ⟨0, Nat.zero_lt_succ len, step_zero hn _⟩
    · refine ⟨t + 1, by omega, ?_⟩
      rw [step_succ', next_prev]
  · rintro ⟨t, ht, rfl⟩
    cases t with
    | zero => exact Or.inl (step_zero hn _)
    | succ t =>
      right
      refine ⟨t, by omega, ?_⟩
      rw [step_succ', next_prev]

lemma interval_full {n : ℕ} (hn : 0 < n) (a : Fin n) :
    interval hn a n = Finset.univ := by
  ext x
  simp only [interval, Finset.mem_image, Finset.mem_range, Finset.mem_univ, iff_true]
  refine ⟨(x.val + n - a.val) % n, Nat.mod_lt _ hn, ?_⟩
  ext
  simp only [step]
  rw [Nat.add_mod_mod]
  have : a.val + (x.val + n - a.val) = x.val + n := by have := a.isLt; omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt]

lemma card_runStarts_interval_le_one {n : ℕ} (hn : 0 < n) (a : Fin n) (len : ℕ) :
    (runStarts hn (interval hn a len)).card ≤ 1 := by
  have hsub : runStarts hn (interval hn a len) ⊆ {a} := by
    intro x hx
    simp only [runStarts, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rcases hx with ⟨hxI, hprev⟩
    simp only [interval, Finset.mem_image, Finset.mem_range] at hxI
    rcases hxI with ⟨t, ht, rfl⟩
    cases t with
    | zero => rw [step_zero]; exact Finset.mem_singleton_self a
    | succ t =>
      exfalso
      apply hprev
      rw [step_succ, prev_next]
      exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (by omega), rfl⟩
  exact (Finset.card_le_card hsub).trans (by simp)

def dirExt (n : ℕ) (dir : Fin (n - 2) → Bool) (m : ℕ) : Bool :=
  if h : m < n - 2 then dir ⟨m, h⟩ else true

def leftCnt (n : ℕ) (dir : Fin (n - 2) → Bool) : ℕ → ℕ
  | 0 => 0
  | m + 1 => leftCnt n dir m + if dirExt n dir m then 1 else 0

lemma leftCnt_le (n : ℕ) (dir : Fin (n - 2) → Bool) : ∀ m, leftCnt n dir m ≤ m
  | 0 => le_rfl
  | m + 1 => by
      dsimp [leftCnt]
      have := leftCnt_le n dir m
      split_ifs <;> omega

def buildFun {n : ℕ} (hn : 0 < n) (dir : Fin (n - 2) → Bool) (b : Fin n) : Fin n :=
  match b.val with
  | 0 => ⟨0, hn⟩
  | m + 1 =>
    if dirExt n dir m then
      (prev hn)^[leftCnt n dir m + 1] ⟨0, hn⟩
    else
      step hn ⟨0, hn⟩ (m + 1 - leftCnt n dir m)

lemma buildFun_prefix {n : ℕ} (hn : 0 < n) (dir : Fin (n - 2) → Bool) :
    ∀ b : ℕ, 1 ≤ b → b ≤ n →
      (Finset.univ.filter (fun i : Fin n => i.val < b)).image (buildFun hn dir) =
        interval hn ((prev hn)^[leftCnt n dir (b - 1)] ⟨0, hn⟩) b := by
  intro b
  induction b with
  | zero => intro h; omega
  | succ b ih =>
    intro _ hbn
    cases b with
    | zero =>
      ext x
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        interval, Finset.mem_range, Nat.sub_self, leftCnt, Function.iterate_zero_apply]
      constructor
      · rintro ⟨i, hi, rfl⟩
        have hi0 : i.val = 0 := by omega
        refine ⟨0, Nat.zero_lt_one, ?_⟩
        rw [step_zero]
        simp [buildFun, hi0]
      · rintro ⟨t, ht, rfl⟩
        have ht0 : t = 0 := by omega
        subst ht0
        refine ⟨⟨0, hn⟩, Nat.zero_lt_one, ?_⟩
        rw [step_zero]
        simp [buildFun]
    | succ m =>
      have hih := ih (by omega) (by omega)
      have hsplit : (Finset.univ.filter (fun i : Fin n => i.val < m + 2)).image (buildFun hn dir) =
          insert (buildFun hn dir ⟨m + 1, by omega⟩)
            ((Finset.univ.filter (fun i : Fin n => i.val < m + 1)).image (buildFun hn dir)) := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨i, hi, rfl⟩
          by_cases hlt : i.val < m + 1
          · exact Or.inr ⟨i, hlt, rfl⟩
          · left; congr 1; ext; dsimp; omega
        · rintro (rfl | ⟨i, hi, rfl⟩)
          · exact ⟨⟨m + 1, by omega⟩, by dsimp; omega, rfl⟩
          · exact ⟨i, by omega, rfl⟩
      rw [hsplit, hih]
      have hsub1 : m + 1 - 1 = m := by omega
      have hsub2 : m + 2 - 1 = m + 1 := by omega
      rw [hsub1, hsub2]
      dsimp only [buildFun, leftCnt]
      cases hdir : dirExt n dir m
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        have hcle : leftCnt n dir m ≤ m := leftCnt_le n dir m
        have hstep_eq : step hn ⟨0, hn⟩ (m + 1 - leftCnt n dir m) =
            step hn ((prev hn)^[leftCnt n dir m] ⟨0, hn⟩) (m + 1) := by
          have hsum : leftCnt n dir m + (m + 1 - leftCnt n dir m) = m + 1 := by omega
          conv_rhs => rw [← hsum, ← step_add, step_prev_iter]
        rw [hstep_eq, insert_step_interval]
      · simp only [↓reduceIte]
        rw [Function.iterate_succ_apply', insert_prev_interval]

lemma buildFun_bijective {n : ℕ} (hn : 0 < n) (dir : Fin (n - 2) → Bool) :
    Function.Bijective (buildFun hn dir) := by
  apply Finite.surjective_iff_bijective.mp
  intro y
  have hfull := buildFun_prefix hn dir n hn le_rfl
  rw [interval_full] at hfull
  have hy : y ∈ (Finset.univ.filter (fun i : Fin n => i.val < n)).image (buildFun hn dir) := by
    rw [hfull]; exact Finset.mem_univ y
  rcases Finset.mem_image.mp hy with ⟨i, _, hi⟩
  exact ⟨i, hi⟩

noncomputable def buildPerm {n : ℕ} (hn : 0 < n) (dir : Fin (n - 2) → Bool) :
    {π : Equiv.Perm (Fin n) // IsCyclicGrowth hn π ∧ π ⟨0, hn⟩ = ⟨0, hn⟩} :=
  ⟨Equiv.ofBijective (buildFun hn dir) (buildFun_bijective hn dir),
    by
      intro b
      by_cases hb0 : b.val = 0
      · have hemp : prefixImg (Equiv.ofBijective (buildFun hn dir) (buildFun_bijective hn dir)) b.val = ∅ := by
          ext x; simp [prefixImg, hb0]
        rw [hemp]
        have : runStarts hn (∅ : Finset (Fin n)) = ∅ := by ext x; simp [runStarts]
        rw [this, Finset.card_empty]; exact Nat.zero_le 1
      · have hpref : prefixImg (Equiv.ofBijective (buildFun hn dir) (buildFun_bijective hn dir)) b.val =
            (Finset.univ.filter (fun i : Fin n => i.val < b.val)).image (buildFun hn dir) := rfl
        rw [hpref, buildFun_prefix hn dir b.val (by omega) (Nat.lt_succ_iff.mp b.isLt)]
        exact card_runStarts_interval_le_one hn _ b.val,
    by simp [buildFun]⟩

lemma buildPerm_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (buildPerm hn) := by
  intro d1 d2 heq
  by_contra hne
  have hex : ∃ m : ℕ, ∃ hm : m < n - 2, d1 ⟨m, hm⟩ ≠ d2 ⟨m, hm⟩ := by
    by_contra hall
    push Not at hall
    apply hne; funext m; exact hall m.val m.isLt
  let m := Nat.find hex
  obtain ⟨hm, hdiff⟩ := Nat.find_spec hex
  have hagree : ∀ t < m, ∀ ht : t < n - 2, d1 ⟨t, ht⟩ = d2 ⟨t, ht⟩ := by
    intro t ht ht'
    by_contra hd
    exact Nat.find_min hex ht ⟨ht', hd⟩
  have hcnt : leftCnt n d1 m = leftCnt n d2 m := by
    suffices ∀ t ≤ m, leftCnt n d1 t = leftCnt n d2 t from this m le_rfl
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro htm
      simp only [leftCnt, dirExt, show t < n - 2 by omega, ↓reduceDIte]
      rw [ih (by omega), hagree t (by omega) (by omega)]
  have hval : buildFun hn d1 ⟨m + 1, by omega⟩ = buildFun hn d2 ⟨m + 1, by omega⟩ := by
    have := congrArg (fun x => x.1 ⟨m + 1, by omega⟩) heq
    simpa [buildPerm] using this
  have hde1 : dirExt n d1 m = d1 ⟨m, hm⟩ := by
    dsimp only [dirExt]; split_ifs with h
    · rfl
    · exact absurd hm h
  have hde2 : dirExt n d2 m = d2 ⟨m, hm⟩ := by
    dsimp only [dirExt]; split_ifs with h
    · rfl
    · exact absurd hm h
  simp only [buildFun, hde1, hde2, hcnt] at hval
  cases hd1 : d1 ⟨m, hm⟩ <;> cases hd2 : d2 ⟨m, hm⟩
  · exact hdiff (hd1.trans hd2.symm)
  · simp only [hd1, hd2, Bool.false_eq_true, ↓reduceIte] at hval
    have hstep := congrArg (fun x => step hn x (leftCnt n d2 m + 1)) hval
    rw [step_prev_iter, step_add] at hstep
    have hsum : m + 1 - leftCnt n d2 m + (leftCnt n d2 m + 1) = m + 2 := by
      have := leftCnt_le n d2 m; omega
    rw [hsum] at hstep
    have hv := congrArg Fin.val hstep
    simp only [step, Nat.zero_add, Nat.mod_eq_of_lt (by omega : m + 2 < n)] at hv
    omega
  · simp only [hd1, hd2, Bool.false_eq_true, ↓reduceIte] at hval
    have hstep := congrArg (fun x => step hn x (leftCnt n d2 m + 1)) hval
    rw [step_prev_iter, step_add] at hstep
    have hsum : m + 1 - leftCnt n d2 m + (leftCnt n d2 m + 1) = m + 2 := by
      have := leftCnt_le n d2 m; omega
    rw [hsum] at hstep
    have hv := congrArg Fin.val hstep
    simp only [step, Nat.zero_add, Nat.mod_eq_of_lt (by omega : m + 2 < n)] at hv
    omega
  · exact hdiff (hd1.trans hd2.symm)

lemma buildPerm_surjective {n : ℕ} (hn : 0 < n) :
    Function.Surjective (buildPerm hn) := by
  rintro ⟨π, hcg, h0⟩
  let dir : Fin (n - 2) → Bool := fun m =>
    decide (next hn (π ⟨m.val + 1, by have := m.isLt; omega⟩) ∈ prefixImg π (m.val + 1))
  refine ⟨dir, ?_⟩
  apply Subtype.ext
  have hall : ∀ b : ℕ, ∀ hb : b < n, buildFun hn dir ⟨b, hb⟩ = π ⟨b, hb⟩ := by
    intro b
    induction b using Nat.strong_induction_on with
    | ind b ih =>
      intro hb
      cases b with
      | zero => simp [buildFun, h0]
      | succ m =>
        by_cases hm : m < n - 2
        · have hA_eq : prefixImg π (m + 1) =
              interval hn ((prev hn)^[leftCnt n dir m] ⟨0, hn⟩) (m + 1) := by
            have h1 : prefixImg π (m + 1) =
                (Finset.univ.filter (fun i : Fin n => i.val < m + 1)).image (buildFun hn dir) := by
              ext x
              simp only [prefixImg, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · rintro ⟨i, hi, rfl⟩
                exact ⟨i, hi, ih i.val hi i.isLt⟩
              · rintro ⟨i, hi, rfl⟩
                exact ⟨i, hi, (ih i.val hi i.isLt).symm⟩
            rw [h1]
            have hp := buildFun_prefix hn dir (m + 1) (by omega) (by omega)
            simpa using hp
          let a := (prev hn)^[leftCnt n dir m] ⟨0, hn⟩
          let j := π ⟨m + 1, hb⟩
          have hj_not : j ∉ prefixImg π (m + 1) := by
            simp only [prefixImg, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
              not_exists, not_and]
            intro i hi heq
            have := congrArg Fin.val (π.injective heq)
            dsimp at this; omega
          have hA_ne : (prefixImg π (m + 1)).Nonempty :=
            ⟨π ⟨0, hn⟩, Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩, rfl⟩⟩
          have hins : insert j (prefixImg π (m + 1)) = prefixImg π (m + 2) := by
            ext x
            simp only [Finset.mem_insert, prefixImg, Finset.mem_image, Finset.mem_filter,
              Finset.mem_univ, true_and]
            constructor
            · rintro (rfl | ⟨i, hi, rfl⟩)
              · exact ⟨⟨m + 1, hb⟩, by dsimp; omega, rfl⟩
              · exact ⟨i, by omega, rfl⟩
            · rintro ⟨i, hi, rfl⟩
              by_cases hlt : i.val < m + 1
              · exact Or.inr ⟨i, hlt, rfl⟩
              · left; congr 1; ext; dsimp; omega
          have hle1 : (runStarts hn (insert j (prefixImg π (m + 1)))).card ≤ 1 := by
            rw [hins]; exact hcg ⟨m + 2, by omega⟩
          have hpn := prev_or_next_mem_of_runStarts_le_one hn (prefixImg π (m + 1)) hA_ne j hj_not hle1
          have hde : dirExt n dir m = dir ⟨m, hm⟩ := by simp [dirExt, hm]
          simp only [buildFun, hde]
          by_cases hnext : next hn j ∈ prefixImg π (m + 1)
          · have hdir : dir ⟨m, hm⟩ = true := by simp [dir, j, hnext]
            simp only [hdir, ↓reduceIte]
            rw [hA_eq] at hnext hj_not
            simp only [interval, Finset.mem_image, Finset.mem_range] at hnext
            rcases hnext with ⟨t, ht, ht_eq⟩
            cases t with
            | zero =>
              rw [step_zero] at ht_eq
              have hj_eq : j = prev hn a := by rw [← prev_next hn j, ← ht_eq]
              change (prev hn)^[leftCnt n dir m + 1] ⟨0, hn⟩ = j
              rw [hj_eq]
              exact Function.iterate_succ_apply' (prev hn) (leftCnt n dir m) ⟨0, hn⟩
            | succ t =>
              exfalso
              have hj_eq : j = step hn a t := by
                apply next_injective hn
                rw [← step_succ]
                exact ht_eq.symm
              apply hj_not
              rw [hj_eq]
              exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (by omega), rfl⟩
          · have hdir : dir ⟨m, hm⟩ = false := by simp [dir, j, hnext]
            simp only [hdir, Bool.false_eq_true, ↓reduceIte]
            have hprev : prev hn j ∈ prefixImg π (m + 1) := by
              rcases hpn with h | h
              · exact h
              · exact absurd h hnext
            rw [hA_eq] at hprev hj_not
            simp only [interval, Finset.mem_image, Finset.mem_range] at hprev
            rcases hprev with ⟨t, ht, ht_eq⟩
            have hj_eq : j = step hn a (t + 1) := by
              rw [step_succ, ht_eq, next_prev]
            have ht_eq_m : t = m := by
              by_contra hne
              apply hj_not
              rw [hj_eq]
              exact Finset.mem_image.mpr ⟨t + 1, Finset.mem_range.mpr (by omega), rfl⟩
            rw [ht_eq_m] at hj_eq
            have hcle : leftCnt n dir m ≤ m := leftCnt_le n dir m
            have hsum : leftCnt n dir m + (m + 1 - leftCnt n dir m) = m + 1 := by omega
            change step hn ⟨0, hn⟩ (m + 1 - leftCnt n dir m) = j
            rw [hj_eq]
            dsimp only [a]
            conv_rhs => rw [← hsum, ← step_add, step_prev_iter]
        · have hm_eq : m + 1 = n - 1 := by omega
          by_contra hne
          obtain ⟨i, hi⟩ := π.surjective (buildFun hn dir ⟨m + 1, hb⟩)
          have hine : i ≠ ⟨m + 1, hb⟩ := fun h => hne (h ▸ hi).symm
          have hilt : i.val < m + 1 := by
            have := i.isLt
            have hv : i.val ≠ m + 1 := fun h => hine (Fin.ext h)
            omega
          have heq := (ih i.val hilt i.isLt).trans hi
          exact hine ((buildFun_bijective hn dir).1 heq)
  apply Equiv.ext
  intro b
  exact hall b.val b.isLt

noncomputable def fullEquiv {n p : ℕ} (hn : 0 < n) (hp : 2 ≤ p) :
    ((Fin n × (Fin (n - 2) → Bool)) × (Fin n → Equiv.Perm (Fin p))) ≃
      {o : Fin (p * n) → Fin (p * n) //
        allowedClean (Nat.mul_pos (by omega : 0 < p) hn) p o ∧ peakClean hn o = 1} := by
  have hp0 : 0 < p := by omega
  let eDir : (Fin (n - 2) → Bool) ≃ {π : Equiv.Perm (Fin n) // IsCyclicGrowth hn π ∧ π ⟨0, hn⟩ = ⟨0, hn⟩} :=
    Equiv.ofBijective (buildPerm hn) ⟨buildPerm_injective hn, buildPerm_surjective hn⟩
  let eGrowth : Fin n × (Fin (n - 2) → Bool) ≃ {π : Equiv.Perm (Fin n) // IsCyclicGrowth hn π} :=
    (Equiv.prodCongr (Equiv.refl (Fin n)) eDir).trans (cyclicGrowthEquivProd hn).symm
  let f : {π : Equiv.Perm (Fin n) // IsCyclicGrowth hn π} × (Fin n → Equiv.Perm (Fin p)) →
      {o : Fin (p * n) → Fin (p * n) // allowedClean (Nat.mul_pos hp0 hn) p o ∧ peakClean hn o = 1} :=
    fun x => ⟨pack hn hp0 x.1.1 x.2,
      (allowedClean_pack_iff hn hp x.1.1 x.2).mpr x.1.2,
      peakClean_pack hn hp x.1.1 x.2⟩
  have hf_bij : Function.Bijective f := by
    constructor
    · rintro ⟨⟨π1, h1⟩, σ1⟩ ⟨⟨π2, h2⟩, σ2⟩ heq
      have hpack : pack hn hp0 π1 σ1 = pack hn hp0 π2 σ2 := congrArg Subtype.val heq
      rcases pack_injective hn hp0 hpack with ⟨rfl, rfl⟩
      rfl
    · rintro ⟨o, hall, hpeak⟩
      obtain ⟨π, σ, hpack⟩ := exists_pack_of_peak_one hn hp o hall.1 hpeak
      have hcg : IsCyclicGrowth hn π :=
        (allowedClean_pack_iff hn hp π σ).mp (hpack.symm ▸ hall)
      exact ⟨(⟨π, hcg⟩, σ), Subtype.ext hpack⟩
  exact (Equiv.prodCongr eGrowth (Equiv.refl _)).trans (Equiv.ofBijective f hf_bij)

lemma part3_clean {n p r : ℕ} (hn : 0 < n) (hp : 2 ≤ p) (hr : 4 ≤ r) :
    ∃ o : Fin (p * n) → Fin (p * n),
      allowedClean (Nat.mul_pos (by omega : 0 < p) hn) p o ∧
      peakClean hn o = 1 ∧
      widthClean hn (by omega : 0 < p) r o ≤ min (p * n) ((2 * p + 1) * (5 * r - 3) + 1) + 1 := by
  let x := fullEquiv hn hp ((⟨0, hn⟩, fun _ => false), fun _ => Equiv.refl (Fin p))
  exact ⟨x.1, x.2.1, x.2.2, widthClean_le_of_allowed_peak_one hn hp hr x.1 x.2.1 x.2.2⟩

lemma part4_clean {n p : ℕ} (hn : 0 < n) (hp : 2 ≤ p) :
    Nat.card {o : Fin (p * n) → Fin (p * n) //
      allowedClean (Nat.mul_pos (by omega : 0 < p) hn) p o ∧ peakClean hn o = 1} =
      n * 2 ^ (n - 2) * (Nat.factorial p) ^ n := by
  rw [Nat.card_congr (fullEquiv hn hp).symm, Nat.card_eq_fintype_card]
  simp only [Fintype.card_prod, Fintype.card_pi, Fintype.card_perm,
    Fintype.card_fin, Fintype.card_bool, Finset.prod_const, Finset.card_univ]

lemma span_stmt_eq_coordSub {n k : ℕ} (hn : 0 < n) (ps : List (Fin k)) :
    (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
     Submodule.span (ZMod 2)
       (↑((ps.map (fun (q : Fin k) (j : Fin n) =>
         if q.val % n = j.val then (1 : ZMod 2) else 0)).toFinset) : Set (Fin n → ZMod 2))) =
      coordSub n (labelsList hn ps) := by
  let mcol := fun (q : Fin k) (j : Fin n) =>
    @ite (ZMod 2) (q.val % n = j.val) (Classical.propDecidable _) (1 : ZMod 2) 0
  have hmcol : ∀ q : Fin k, mcol q = (Pi.single (res hn q) (1 : ZMod 2) : Fin n → ZMod 2) := by
    intro q
    funext j
    simp only [mcol, Pi.single_apply, res]
    split_ifs with h1 h2 h3
    · rfl
    · exact absurd (Fin.ext h1.symm) h2
    · exact absurd (congrArg Fin.val h3).symm h1
    · rfl
  have hset : (↑(@List.toFinset _ (fun a b => Classical.propDecidable (a = b)) (ps.map mcol)) :
      Set (Fin n → ZMod 2)) =
      (fun j : Fin n => (Pi.single j (1 : ZMod 2) : Fin n → ZMod 2)) '' (labelsList hn ps : Set (Fin n)) := by
    ext v
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map, Set.mem_image,
      labelsList, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨res hn q, ⟨q, hq, rfl⟩, (hmcol q).symm⟩
    · rintro ⟨j, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨q, hq, hmcol q⟩
  change Submodule.span (ZMod 2)
    (↑(@List.toFinset _ (fun a b => Classical.propDecidable (a = b)) (ps.map mcol)) :
      Set (Fin n → ZMod 2)) = _
  rw [hset]
  exact span_single_eq_coordSub n (labelsList hn ps)

lemma width_term_stmt_eq {k : ℕ} (hk : 0 < k) (r : ℕ)
    (L R : List (Fin k)) (w : Fin k) :
    (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
     let arc := fun (q : Fin k) => (Finset.univ : Finset (Fin k)).filter (fun z =>
       ∃ a : Fin (5 * r - 2), (q.val + a.val) % k = z.val)
     let pool := fun (ps : List (Fin k)) => ps.toFinset.biUnion arc
     ((pool L ∩ pool R) ∪ arc w).card) =
    ((poolClean hk r L ∩ poolClean hk r R) ∪ arcClean hk r w).card := by
  dsimp only
  congr 1
  ext z
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_biUnion, List.mem_toFinset,
    Finset.mem_filter, Finset.mem_univ, true_and, poolClean, arcClean, Finset.mem_image]
  have harc : ∀ q : Fin k,
      (∃ a : Fin (5 * r - 2), (q.val + a.val) % k = z.val) ↔
      (∃ a : Fin (5 * r - 2), step hk q a.val = z) := fun q =>
    ⟨fun ⟨a, ha⟩ => ⟨a, Fin.ext ha⟩, fun ⟨a, ha⟩ => ⟨a, congrArg Fin.val ha⟩⟩
  simp only [harc]

lemma runStarts_card_stmt_eq {k : ℕ} (hk : 0 < k) (ps : List (Fin k)) :
    (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
     let S := ps.toFinset
     ((Finset.univ : Finset (Fin k)).filter (fun j => j ∈ S ∧
       ∀ z ∈ S, (z.val + 1) % k ≠ j.val)).card) =
    (runStarts hk ps.toFinset).card := by
  dsimp only
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset, runStarts]
  constructor
  · rintro ⟨hj, hprev⟩
    refine ⟨hj, fun hp => hprev (prev hk j) hp ?_⟩
    have := congrArg Fin.val (next_prev hk j)
    simpa [next] using this
  · rintro ⟨hj, hprev⟩
    refine ⟨hj, fun z hz heq => hprev ?_⟩
    have hnz : next hk z = j := by ext; exact heq
    rw [← hnz, prev_next]
    exact hz

end PEqualNP.Outside.L_lib_1066

theorem PEqualNP.Outside.L_lib_1066 :
  ∀ (n p r : Nat), 0 < n → 2 ≤ p → 4 ≤ r →
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  let k := p*n
  let W := Fin k
  let V := Fin n → ZMod 2
  let mcol := fun (p : W) (j : Fin n) =>
    if p.val % n = j.val then (1 : ZMod 2) else 0
  let span := fun (ps : List W) => Submodule.span (ZMod 2)
    (↑((ps.map mcol).toFinset) : Set V)
  let arc := fun (p : W) => (Finset.univ : Finset W).filter (fun z =>
    ∃ a : Fin (5*r-2), (p.val+a.val)%k = z.val)
  let pool := fun (ps : List W) => ps.toFinset.biUnion arc
  let charge := fun (o : W → W) (i : W) =>
    let L := (List.ofFn o).take i.val
    let R := (List.ofFn o).drop i.val
    Module.finrank (ZMod 2) (span L ⊓ span R : Submodule (ZMod 2) V)
  let peak := fun (o : W → W) => (Finset.univ : Finset W).sup (charge o)
  let width := fun (o : W → W) => (Finset.univ : Finset W).sup (fun i =>
    let L := (List.ofFn o).take i.val
    let R := (List.ofFn o).drop i.val
    ((pool L ∩ pool R) ∪ arc (o i)).card + charge o i)
  let allowed := fun (h : Nat) (o : W → W) => Function.Bijective o ∧ ∀ u : Fin (k+1),
    let S := ((List.ofFn o).take u.val).toFinset
    ((Finset.univ : Finset W).filter (fun j => j ∈ S ∧
      ∀ z ∈ S, (z.val+1)%k ≠ j.val)).card ≤ h
  (∀ o : W → W, Function.Bijective o → min p n ≤ width o ∧ 1 ≤ peak o) ∧
    (∀ o : W → W, allowed (p-1) o → peak o = n) ∧
    (∃ o : W → W, allowed p o ∧ peak o = 1 ∧ width o ≤ min k ((2*p+1)*(5*r-3)+1)+1) ∧
    Nat.card {o : W → W // allowed p o ∧ peak o = 1} =
      n*2^(n-2)*(Nat.factorial p)^n := by
  intro n p r hn hp hr
  have hp0 : 0 < p := by omega
  have hk : 0 < p * n := Nat.mul_pos hp0 hn
  have hcharge : ∀ (o : Fin (p * n) → Fin (p * n)) (i : Fin (p * n)),
      (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
       Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (↑((((List.ofFn o).take i.val).map
          (fun (q : Fin (p * n)) (j : Fin n) => if q.val % n = j.val then (1 : ZMod 2) else 0)).toFinset) :
            Set (Fin n → ZMod 2)) ⊓
         Submodule.span (ZMod 2) (↑((((List.ofFn o).drop i.val).map
          (fun (q : Fin (p * n)) (j : Fin n) => if q.val % n = j.val then (1 : ZMod 2) else 0)).toFinset) :
            Set (Fin n → ZMod 2)) : Submodule (ZMod 2) (Fin n → ZMod 2))) =
      PEqualNP.Outside.L_lib_1066.chargeClean hn o i := by
    intro o i
    rw [PEqualNP.Outside.L_lib_1066.span_stmt_eq_coordSub hn,
      PEqualNP.Outside.L_lib_1066.span_stmt_eq_coordSub hn,
      PEqualNP.Outside.L_lib_1066.coordSub_inf,
      PEqualNP.Outside.L_lib_1066.finrank_coordSub]
    rfl
  have hpeak : ∀ (o : Fin (p * n) → Fin (p * n)),
      (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
       (Finset.univ : Finset (Fin (p * n))).sup (fun i =>
        Module.finrank (ZMod 2)
          (Submodule.span (ZMod 2) (↑((((List.ofFn o).take i.val).map
            (fun (q : Fin (p * n)) (j : Fin n) => if q.val % n = j.val then (1 : ZMod 2) else 0)).toFinset) :
              Set (Fin n → ZMod 2)) ⊓
           Submodule.span (ZMod 2) (↑((((List.ofFn o).drop i.val).map
            (fun (q : Fin (p * n)) (j : Fin n) => if q.val % n = j.val then (1 : ZMod 2) else 0)).toFinset) :
              Set (Fin n → ZMod 2)) : Submodule (ZMod 2) (Fin n → ZMod 2)))) =
      PEqualNP.Outside.L_lib_1066.peakClean hn o := by
    intro o
    exact Finset.sup_congr rfl fun i _ => hcharge o i
  have hwidth : ∀ (o : Fin (p * n) → Fin (p * n)),
      (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
       (Finset.univ : Finset (Fin (p * n))).sup (fun i =>
        let L := (List.ofFn o).take i.val
        let R := (List.ofFn o).drop i.val
        let arc := fun (q : Fin (p * n)) => (Finset.univ : Finset (Fin (p * n))).filter (fun z =>
          ∃ a : Fin (5 * r - 2), (q.val + a.val) % (p * n) = z.val)
        let pool := fun (ps : List (Fin (p * n))) => ps.toFinset.biUnion arc
        ((pool L ∩ pool R) ∪ arc (o i)).card +
        Module.finrank (ZMod 2)
          (Submodule.span (ZMod 2) (↑((L.map
            (fun (q : Fin (p * n)) (j : Fin n) => if q.val % n = j.val then (1 : ZMod 2) else 0)).toFinset) :
              Set (Fin n → ZMod 2)) ⊓
           Submodule.span (ZMod 2) (↑((R.map
            (fun (q : Fin (p * n)) (j : Fin n) => if q.val % n = j.val then (1 : ZMod 2) else 0)).toFinset) :
              Set (Fin n → ZMod 2)) : Submodule (ZMod 2) (Fin n → ZMod 2)))) =
      PEqualNP.Outside.L_lib_1066.widthClean hn hp0 r o := by
    intro o
    apply Finset.sup_congr rfl
    intro i _
    dsimp only
    rw [PEqualNP.Outside.L_lib_1066.width_term_stmt_eq hk r, hcharge o i]
  have hall_iff : ∀ (h : ℕ) (o : Fin (p * n) → Fin (p * n)),
      (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
       Function.Bijective o ∧ ∀ u : Fin (p * n + 1),
        let S := ((List.ofFn o).take u.val).toFinset
        ((Finset.univ : Finset (Fin (p * n))).filter (fun j => j ∈ S ∧
          ∀ z ∈ S, (z.val + 1) % (p * n) ≠ j.val)).card ≤ h) ↔
      PEqualNP.Outside.L_lib_1066.allowedClean hk h o := by
    intro h o
    refine and_congr Iff.rfl (forall_congr' fun u => ?_)
    dsimp only
    rw [PEqualNP.Outside.L_lib_1066.runStarts_card_stmt_eq hk]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro o ho
    dsimp only
    rw [hwidth o, hpeak o]
    exact PEqualNP.Outside.L_lib_1066.part1_clean hn hp hr o ho
  · intro o hall
    dsimp only at hall ⊢
    rw [hpeak o]
    exact PEqualNP.Outside.L_lib_1066.part2_clean hn hp o ((hall_iff (p - 1) o).mp hall)
  · obtain ⟨o, hall, hp1, hw⟩ := PEqualNP.Outside.L_lib_1066.part3_clean hn hp hr
    refine ⟨o, ?_, ?_, ?_⟩
    · dsimp only; exact (hall_iff p o).mpr hall
    · dsimp only; rw [hpeak o]; exact hp1
    · dsimp only; rw [hwidth o]; exact hw
  · have heq : {o : Fin (p * n) → Fin (p * n) //
        (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
         Function.Bijective o ∧ ∀ u : Fin (p * n + 1),
          let S := ((List.ofFn o).take u.val).toFinset
          ((Finset.univ : Finset (Fin (p * n))).filter (fun j => j ∈ S ∧
            ∀ z ∈ S, (z.val + 1) % (p * n) ≠ j.val)).card ≤ p) ∧
        (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
         (Finset.univ : Finset (Fin (p * n))).sup (fun i =>
          Module.finrank (ZMod 2)
            (Submodule.span (ZMod 2) (↑((((List.ofFn o).take i.val).map
              (fun (q : Fin (p * n)) (j : Fin n) => if q.val % n = j.val then (1 : ZMod 2) else 0)).toFinset) :
                Set (Fin n → ZMod 2)) ⊓
             Submodule.span (ZMod 2) (↑((((List.ofFn o).drop i.val).map
              (fun (q : Fin (p * n)) (j : Fin n) => if q.val % n = j.val then (1 : ZMod 2) else 0)).toFinset) :
                Set (Fin n → ZMod 2)) : Submodule (ZMod 2) (Fin n → ZMod 2)))) = 1} ≃
        {o : Fin (p * n) → Fin (p * n) //
          PEqualNP.Outside.L_lib_1066.allowedClean hk p o ∧
          PEqualNP.Outside.L_lib_1066.peakClean hn o = 1} :=
      Equiv.subtypeEquivRight fun o => and_congr (hall_iff p o) (by rw [hpeak o])
    dsimp only
    rw [Nat.card_congr heq]
    exact PEqualNP.Outside.L_lib_1066.part4_clean hn hp
