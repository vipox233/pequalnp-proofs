import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_951

def nextFn {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

def moveFn {n : ℕ} (i : Fin n) (v : ℕ) : Fin n :=
  ⟨(i.val + v) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

def exitsFn {n : ℕ} (S : Finset (Fin n)) : Finset (Fin n) :=
  S.filter (fun i => nextFn i ∉ S)

def gapFn {n : ℕ} (S : Finset (Fin n)) (i : Fin n) : ℕ :=
  ((Finset.range n).filter (fun k => ∀ j : Fin (k + 1), moveFn i (j.val + 1) ∉ S)).card

def runConstSpace {n : ℕ} (S : Finset (Fin n)) : Submodule (ZMod 2) (Fin n → ZMod 2) where
  carrier := {x | (∀ i, i ∉ S → x i = 0) ∧ (∀ i ∈ S, nextFn i ∈ S → x i = x (nextFn i))}
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩; add_mem' := fun hx hy => ⟨fun i hi => by simp [hx.1 i hi, hy.1 i hi],
    fun i hi hni => by simp [hx.2 i hi hni, hy.2 i hi hni]⟩
  smul_mem' := fun c x hx => ⟨fun i hi => by simp [hx.1 i hi],
    fun i hi hni => by simp [hx.2 i hi hni]⟩

def pathPt {n : ℕ} (S : Finset (Fin n)) (i : Fin n) (t : Fin (gapFn S i - 2)) : Fin n :=
  moveFn i (t.val + 2)

def pathSet {n : ℕ} (S : Finset (Fin n)) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.image (pathPt S i)

def allPaths {n : ℕ} (S : Finset (Fin n)) : Finset (Fin n) :=
  (exitsFn S).biUnion (pathSet S)

private lemma mod_eq_of_lt_two_mul {x n : ℕ} (hx : x < 2 * n) :
    x % n = if x < n then x else x - n := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

private lemma moveFn_zero {n : ℕ} (i : Fin n) : moveFn i 0 = i := by
  apply Fin.ext
  simp [moveFn, Nat.mod_eq_of_lt i.isLt]

private lemma moveFn_one {n : ℕ} (i : Fin n) : moveFn i 1 = nextFn i := rfl

private lemma moveFn_add {n : ℕ} (i : Fin n) (a b : ℕ) :
    moveFn (moveFn i a) b = moveFn i (a + b) := by
  apply Fin.ext
  simp [moveFn, Nat.add_assoc]

private lemma nextFn_moveFn {n : ℕ} (i : Fin n) (a : ℕ) :
    nextFn (moveFn i a) = moveFn i (a + 1) :=
  moveFn_add i a 1

private lemma moveFn_n {n : ℕ} (i : Fin n) : moveFn i n = i := by
  apply Fin.ext
  simp [moveFn, Nat.mod_eq_of_lt i.isLt]

private lemma nextFn_injective {n : ℕ} : Function.Injective (@nextFn n) := by
  intro i j h
  have hval : (i.val + 1) % n = (j.val + 1) % n := congrArg Fin.val h
  rw [mod_eq_of_lt_two_mul (by omega), mod_eq_of_lt_two_mul (by omega)] at hval
  apply Fin.ext
  split_ifs at hval <;> omega

private lemma moveFn_cancel_right {n : ℕ} {i j : Fin n} (k : ℕ)
    (h : moveFn i k = moveFn j k) : i = j := by
  induction k generalizing i j with
  | zero => simpa [moveFn_zero] using h
  | succ k ih =>
    apply ih
    apply nextFn_injective
    rwa [nextFn_moveFn, nextFn_moveFn]

private lemma moveFn_inj_of_lt {n : ℕ} (i : Fin n) {a b : ℕ}
    (ha : a < n) (hb : b < n) (h : moveFn i a = moveFn i b) : a = b := by
  have hval : (i.val + a) % n = (i.val + b) % n := congrArg Fin.val h
  rw [mod_eq_of_lt_two_mul (by omega), mod_eq_of_lt_two_mul (by omega)] at hval
  split_ifs at hval <;> omega

private lemma moveFn_surj {n : ℕ} (i j : Fin n) : ∃ k < n, moveFn i k = j := by
  by_cases h : i.val ≤ j.val
  · refine ⟨j.val - i.val, by omega, Fin.ext ?_⟩
    have : i.val + (j.val - i.val) = j.val := by omega
    simp [moveFn, this, Nat.mod_eq_of_lt j.isLt]
  · refine ⟨j.val + n - i.val, by omega, Fin.ext ?_⟩
    have : i.val + (j.val + n - i.val) = j.val + n := by omega
    simp [moveFn, this, Nat.mod_eq_of_lt j.isLt]

private lemma exists_moveFn_not_mem {n : ℕ} (S : Finset (Fin n)) (hSnu : S ≠ Finset.univ)
    (i : Fin n) : ∃ k, moveFn i k ∉ S := by
  have hne : (Finset.univ \ S).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    exact hSnu (Finset.eq_univ_iff_forall.mpr fun x => hsub (Finset.mem_univ x))
  rcases hne with ⟨w, hw⟩
  rw [Finset.mem_sdiff] at hw
  rcases moveFn_surj i w with ⟨k, _, rfl⟩
  exact ⟨k, hw.2⟩

private noncomputable def stepOut {n : ℕ} (S : Finset (Fin n)) (hSnu : S ≠ Finset.univ)
    (i : Fin n) : ℕ :=
  Nat.find (exists_moveFn_not_mem S hSnu i)

private lemma stepOut_pos {n : ℕ} (S : Finset (Fin n)) (hSnu : S ≠ Finset.univ)
    {i : Fin n} (hi : i ∈ S) : 1 ≤ stepOut S hSnu i := by
  by_contra h
  have h0 : stepOut S hSnu i = 0 := by omega
  have hspec := Nat.find_spec (exists_moveFn_not_mem S hSnu i)
  change moveFn i (stepOut S hSnu i) ∉ S at hspec
  rw [h0, moveFn_zero] at hspec
  exact hspec hi

private lemma stepOut_mem {n : ℕ} (S : Finset (Fin n)) (hSnu : S ≠ Finset.univ)
    (i : Fin n) {k : ℕ} (hk : k < stepOut S hSnu i) : moveFn i k ∈ S := by
  by_contra h
  exact Nat.find_min (exists_moveFn_not_mem S hSnu i) hk h

private lemma stepOut_not_mem {n : ℕ} (S : Finset (Fin n)) (hSnu : S ≠ Finset.univ)
    (i : Fin n) : moveFn i (stepOut S hSnu i) ∉ S :=
  Nat.find_spec (exists_moveFn_not_mem S hSnu i)

private noncomputable def exitOf {n : ℕ} (S : Finset (Fin n)) (hSnu : S ≠ Finset.univ)
    (i : Fin n) : Fin n :=
  moveFn i (stepOut S hSnu i - 1)

private lemma exitOf_mem_exitsFn {n : ℕ} (S : Finset (Fin n)) (hSnu : S ≠ Finset.univ)
    {i : Fin n} (hi : i ∈ S) : exitOf S hSnu i ∈ exitsFn S := by
  have hpos := stepOut_pos S hSnu hi
  rw [exitsFn, Finset.mem_filter]
  refine ⟨stepOut_mem S hSnu i (by omega), ?_⟩
  rw [exitOf, nextFn_moveFn, Nat.sub_add_cancel hpos]
  exact stepOut_not_mem S hSnu i

private lemma exitOf_eq_self {n : ℕ} (S : Finset (Fin n)) (hSnu : S ≠ Finset.univ)
    {i : Fin n} (hi : i ∈ exitsFn S) : exitOf S hSnu i = i := by
  rw [exitsFn, Finset.mem_filter] at hi
  have hpos := stepOut_pos S hSnu hi.1
  have hle : stepOut S hSnu i ≤ 1 := Nat.find_min' (exists_moveFn_not_mem S hSnu i) hi.2
  have h1 : stepOut S hSnu i = 1 := by omega
  simp [exitOf, h1, moveFn_zero]

private lemma exitOf_nextFn {n : ℕ} (S : Finset (Fin n)) (hSnu : S ≠ Finset.univ)
    {i : Fin n} (hi : i ∈ S) (hni : nextFn i ∈ S) :
    exitOf S hSnu i = exitOf S hSnu (nextFn i) := by
  have hpos := stepOut_pos S hSnu hi
  have hge2 : 2 ≤ stepOut S hSnu i := by
    by_contra h
    have h1 : stepOut S hSnu i = 1 := by omega
    have hnm := stepOut_not_mem S hSnu i
    rw [h1, moveFn_one] at hnm
    exact hnm hni
  have hstep : stepOut S hSnu (nextFn i) = stepOut S hSnu i - 1 := by
    apply le_antisymm
    · apply Nat.find_min' (exists_moveFn_not_mem S hSnu (nextFn i))
      rw [show moveFn (nextFn i) (stepOut S hSnu i - 1) = moveFn i (stepOut S hSnu i) by
        rw [← moveFn_one, moveFn_add]; congr 1; omega]
      exact stepOut_not_mem S hSnu i
    · by_contra hlt
      have hnm : moveFn (nextFn i) (stepOut S hSnu (nextFn i)) ∉ S :=
        stepOut_not_mem S hSnu (nextFn i)
      have hmem : moveFn i (1 + stepOut S hSnu (nextFn i)) ∈ S :=
        stepOut_mem S hSnu i (by omega)
      rw [← moveFn_add, moveFn_one] at hmem
      exact hnm hmem
  rw [exitOf, exitOf, hstep, ← moveFn_one, moveFn_add]
  congr 1
  omega

private lemma runConstSpace_eq_moveFn {n : ℕ} (S : Finset (Fin n)) (hSnu : S ≠ Finset.univ)
    {x : Fin n → ZMod 2} (hx : x ∈ runConstSpace S) {i : Fin n}
    (k : ℕ) (hk : k < stepOut S hSnu i) : x i = x (moveFn i k) := by
  induction k with
  | zero => simp [moveFn_zero]
  | succ k ih =>
    rw [ih (by omega), ← nextFn_moveFn]
    exact hx.2 (moveFn i k) (stepOut_mem S hSnu i (by omega))
      (by rw [nextFn_moveFn]; exact stepOut_mem S hSnu i hk)

lemma finrank_runConstSpace {n : ℕ} (hn : 3 ≤ n) (S : Finset (Fin n))
    (hSne : S.Nonempty) (hSnu : S ≠ Finset.univ) :
    Module.finrank (ZMod 2) (runConstSpace S) = (exitsFn S).card := by
  classical
  have _ := hn
  have _ := hSne
  let e : runConstSpace S ≃ₗ[ZMod 2] (exitsFn S → ZMod 2) :=
    { toFun := fun x j => x.1 j.1
      map_add' := fun x y => by ext j; rfl
      map_smul' := fun c x => by ext j; rfl
      invFun := fun f =>
        ⟨fun i => if hi : i ∈ S then f ⟨exitOf S hSnu i, exitOf_mem_exitsFn S hSnu hi⟩ else 0,
          ⟨fun i hi => by simp [hi], fun i hi hni => by
            simp only [hi, hni, ↓reduceDIte]
            congr 1
            exact Subtype.ext (exitOf_nextFn S hSnu hi hni)⟩⟩
      left_inv := fun x => by
        apply Subtype.ext
        funext i
        by_cases hi : i ∈ S
        · simp only [hi, ↓reduceDIte]
          have hpos := stepOut_pos S hSnu hi
          exact (runConstSpace_eq_moveFn S hSnu x.2 (stepOut S hSnu i - 1) (by omega)).symm
        · simp only [hi, ↓reduceDIte]
          exact (x.2.1 i hi).symm
      right_inv := fun f => by
        funext j
        have hjS : j.1 ∈ S := (Finset.mem_filter.mp j.2).1
        simp only [hjS, ↓reduceDIte]
        congr 1
        exact Subtype.ext (exitOf_eq_self S hSnu j.2) }
  rw [LinearEquiv.finrank_eq e, Module.finrank_pi, Fintype.card_coe]

lemma gapFn_spec {n : ℕ} (hn : 3 ≤ n) (S : Finset (Fin n)) (i : Fin n)
    (hi : i ∈ exitsFn S) :
    1 ≤ gapFn S i ∧ gapFn S i < n ∧
      (∀ k, 1 ≤ k → k ≤ gapFn S i → moveFn i k ∉ S) ∧
      moveFn i (gapFn S i + 1) ∈ S := by
  classical
  rw [exitsFn, Finset.mem_filter] at hi
  let P : ℕ → Prop := fun k => ∀ j : Fin (k + 1), moveFn i (j.val + 1) ∉ S
  have hP_down : ∀ a b, a ≤ b → P b → P a := by
    intro a b hab hb j
    exact hb ⟨j.val, by omega⟩
  have hP0 : P 0 := by
    intro j
    have hj : j.val = 0 := by omega
    simpa [hj, moveFn_one] using hi.2
  have hnotPn : ¬ P (n - 1) := by
    intro hP
    have hmem := hP ⟨n - 1, by omega⟩
    have heq : n - 1 + 1 = n := by omega
    rw [heq, moveFn_n] at hmem
    exact hmem hi.1
  have hex : ∃ m, ¬ P m := ⟨n - 1, hnotPn⟩
  let g := Nat.find hex
  have hg_lt : g < n := by
    have hle : g ≤ n - 1 := Nat.find_min' hex hnotPn
    omega
  have hg_pos : 1 ≤ g := by
    by_contra h
    have h0 : g = 0 := by omega
    have hspec : ¬ P g := Nat.find_spec hex
    rw [h0] at hspec
    exact hspec hP0
  have hfilter : (Finset.range n).filter (fun k => P k) = Finset.range g := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, hPk⟩
      by_contra hge
      exact Nat.find_spec hex (hP_down g k (by omega) hPk)
    · intro hkg
      exact ⟨by omega, Classical.byContradiction (Nat.find_min hex hkg)⟩
  have hgap : gapFn S i = g := by
    unfold gapFn
    convert congrArg Finset.card hfilter using 1
    simp
  rw [hgap]
  have hnotS : ∀ k, 1 ≤ k → k ≤ g → moveFn i k ∉ S := by
    intro k hk1 hkg
    have hPg1 : P (g - 1) := Classical.byContradiction (Nat.find_min hex (by omega))
    have h := hPg1 ⟨k - 1, by omega⟩
    have heq : k - 1 + 1 = k := by omega
    rwa [heq] at h
  refine ⟨hg_pos, hg_lt, hnotS, ?_⟩
  by_contra hnot
  apply Nat.find_spec hex
  intro j
  by_cases hjl : j.val < g
  · exact hnotS (j.val + 1) (by omega) (by omega)
  · have hjeq : j.val = g := by omega
    simpa [hjeq] using hnot

lemma pathPt_injective {n : ℕ} (hn : 3 ≤ n) (S : Finset (Fin n)) (i : Fin n)
    (hi : i ∈ exitsFn S) : Function.Injective (pathPt S i) := by
  intro t₁ t₂ h
  have hgap := (gapFn_spec hn S i hi).2.1
  have heq := moveFn_inj_of_lt i (a := t₁.val + 2) (b := t₂.val + 2)
    (by omega) (by omega) h
  exact Fin.ext (by omega)

lemma pathSet_disjoint_S {n : ℕ} (hn : 3 ≤ n) (S : Finset (Fin n)) (i : Fin n)
    (hi : i ∈ exitsFn S) : Disjoint (pathSet S i) S := by
  rw [Finset.disjoint_left]
  intro v hv
  rw [pathSet, Finset.mem_image] at hv
  rcases hv with ⟨t, _, rfl⟩
  have hspec := gapFn_spec hn S i hi
  exact hspec.2.2.1 (t.val + 2) (by omega) (by omega)

private lemma vacant_run_unique_exit {n : ℕ} (hn : 3 ≤ n) (S : Finset (Fin n))
    {i i' : Fin n} (hi : i ∈ exitsFn S) (hi' : i' ∈ exitsFn S)
    {a b : ℕ} (ha1 : 1 ≤ a) (ha2 : a ≤ gapFn S i)
    (hb1 : 1 ≤ b) (hb2 : b ≤ gapFn S i')
    (heq : moveFn i a = moveFn i' b) : i = i' := by
  have hiS : i ∈ S := (Finset.mem_filter.mp hi).1
  have hi'S : i' ∈ S := (Finset.mem_filter.mp hi').1
  rcases le_total a b with hab | hba
  · have h1 : moveFn i a = moveFn (moveFn i' (b - a)) a := by
      rw [heq, moveFn_add, Nat.sub_add_cancel hab]
    have h2 : i = moveFn i' (b - a) := moveFn_cancel_right a h1
    by_cases h0 : b - a = 0
    · simpa [h0, moveFn_zero] using h2
    · exfalso
      have hnot := (gapFn_spec hn S i' hi').2.2.1 (b - a) (by omega) (by omega)
      rw [← h2] at hnot
      exact hnot hiS
  · have h1 : moveFn (moveFn i (a - b)) b = moveFn i' b := by
      rw [moveFn_add, Nat.sub_add_cancel hba, heq]
    have h2 : moveFn i (a - b) = i' := moveFn_cancel_right b h1
    by_cases h0 : a - b = 0
    · simpa [h0, moveFn_zero] using h2
    · exfalso
      have hnot := (gapFn_spec hn S i hi).2.2.1 (a - b) (by omega) (by omega)
      rw [h2] at hnot
      exact hnot hi'S

lemma pathSet_pairwiseDisjoint {n : ℕ} (hn : 3 ≤ n) (S : Finset (Fin n)) :
    (exitsFn S : Set (Fin n)).PairwiseDisjoint (pathSet S) := by
  intro i hi i' hi' hne
  change Disjoint (pathSet S i) (pathSet S i')
  rw [Finset.disjoint_left]
  intro v hv hv'
  rw [pathSet, Finset.mem_image] at hv hv'
  rcases hv with ⟨t₁, _, rfl⟩
  rcases hv' with ⟨t₂, _, hveq⟩
  exact hne (vacant_run_unique_exit hn S hi hi'
    (by omega) (by omega) (by omega) (by omega) hveq.symm)

lemma nextFn_pathPt {n : ℕ} (S : Finset (Fin n)) (i : Fin n)
    (t : Fin (gapFn S i - 2)) (ht : t.val + 1 < gapFn S i - 2) :
    nextFn (pathPt S i t) = pathPt S i ⟨t.val + 1, ht⟩ := by
  simp only [pathPt, nextFn_moveFn]

lemma pathSet_nextFn_mem {n : ℕ} (hn : 3 ≤ n) (S : Finset (Fin n)) (i : Fin n)
    (hi : i ∈ exitsFn S) (t : Fin (gapFn S i - 2))
    (hnext : nextFn (pathPt S i t) ∈ allPaths S) :
    t.val + 1 < gapFn S i - 2 := by
  by_contra h
  have h1 : nextFn (pathPt S i t) = moveFn i (gapFn S i) := by
    rw [pathPt, nextFn_moveFn]
    congr 1
    omega
  have h2 : nextFn (nextFn (pathPt S i t)) ∈ S := by
    rw [h1, nextFn_moveFn]
    exact (gapFn_spec hn S i hi).2.2.2
  rw [allPaths, Finset.mem_biUnion] at hnext
  rcases hnext with ⟨j, hj, hvj⟩
  rw [pathSet, Finset.mem_image] at hvj
  rcases hvj with ⟨u, _, hu⟩
  rw [← hu, pathPt, nextFn_moveFn] at h2
  have hnot := (gapFn_spec hn S j hj).2.2.1 (u.val + 2 + 1) (by omega) (by omega)
  exact hnot h2

lemma not_mem_S_union_allPaths_adj {n : ℕ} (hn : 3 ≤ n) (S : Finset (Fin n))
    (hSne : S.Nonempty) (hSnu : S ≠ Finset.univ)
    (v : Fin n) (hvS : v ∉ S) (hvP : v ∉ allPaths S) :
    nextFn v ∈ S ∨ (∃ u ∈ S, nextFn u = v) := by
  classical
  have _ := hSnu
  have hex : ∃ d, 1 ≤ d ∧ ∃ i ∈ S, moveFn i d = v := by
    rcases hSne with ⟨w, hw⟩
    rcases moveFn_surj w v with ⟨k, _, hkv⟩
    have hk : 1 ≤ k := by
      by_contra hk0
      have : k = 0 := by omega
      rw [this, moveFn_zero] at hkv
      exact hvS (hkv ▸ hw)
    exact ⟨k, hk, w, hw, hkv⟩
  let d := Nat.find hex
  have hd_spec : 1 ≤ d ∧ ∃ i ∈ S, moveFn i d = v := Nat.find_spec hex
  rcases hd_spec with ⟨hd1, i, hiS, hidv⟩
  have hi_exit : i ∈ exitsFn S := by
    rw [exitsFn, Finset.mem_filter]
    refine ⟨hiS, ?_⟩
    intro hni
    by_cases hd_eq1 : d = 1
    · rw [hd_eq1, moveFn_one] at hidv
      exact hvS (hidv ▸ hni)
    · have hlt : d - 1 < d := by omega
      refine Nat.find_min hex hlt ⟨by omega, nextFn i, hni, ?_⟩
      rw [← moveFn_one, moveFn_add, Nat.add_sub_of_le (by omega), ← hidv]
  have hspec := gapFn_spec hn S i hi_exit
  have hd_le : d ≤ gapFn S i := by
    by_contra hgt
    have huS : moveFn i (gapFn S i + 1) ∈ S := hspec.2.2.2
    by_cases hdeq : d = gapFn S i + 1
    · rw [← hdeq, hidv] at huS
      exact hvS huS
    · have hlt : d - (gapFn S i + 1) < d := by omega
      refine Nat.find_min hex hlt ⟨by omega, moveFn i (gapFn S i + 1), huS, ?_⟩
      rw [moveFn_add, Nat.add_sub_of_le (by omega), hidv]
  by_cases hd_eq1 : d = 1
  · right
    refine ⟨i, hiS, ?_⟩
    rwa [hd_eq1, moveFn_one] at hidv
  · by_cases hd_eqg : d = gapFn S i
    · left
      rw [← hidv, hd_eqg, nextFn_moveFn]
      exact hspec.2.2.2
    · exfalso
      apply hvP
      rw [allPaths, Finset.mem_biUnion]
      refine ⟨i, hi_exit, ?_⟩
      rw [pathSet, Finset.mem_image]
      refine ⟨⟨d - 2, by omega⟩, Finset.mem_univ _, ?_⟩
      simp only [pathPt]
      have : d - 2 + 2 = d := by omega
      rw [this, hidv]

def pathGood {l : ℕ} (Q : Submodule (ZMod 2) (Fin l → ZMod 2)) : Prop :=
  ∀ x ∈ Q, ∀ y ∈ Q, ∀ (t : Fin l) (ht : t.val + 1 < l),
    x t * y ⟨t.val + 1, ht⟩ = x ⟨t.val + 1, ht⟩ * y t

noncomputable def pathSupp {l : ℕ} (Q : Submodule (ZMod 2) (Fin l → ZMod 2)) : Finset (Fin l) :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  Finset.univ.filter (fun t : Fin l => ∃ x ∈ Q, x t ≠ 0)

def pathRuns {l : ℕ} (T : Finset (Fin l)) : Finset (Fin l) :=
  T.filter (fun t => ∀ ht : t.val + 1 < l, ⟨t.val + 1, ht⟩ ∉ T)

def blockSpace {l : ℕ} (T : Finset (Fin l)) : Submodule (ZMod 2) (Fin l → ZMod 2) where
  carrier := {x | (∀ t, t ∉ T → x t = 0) ∧
    (∀ (t : Fin l) (ht : t.val + 1 < l), t ∈ T → ⟨t.val + 1, ht⟩ ∈ T → x t = x ⟨t.val + 1, ht⟩)}
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩; add_mem' := fun hx hy => ⟨fun t ht => by simp [hx.1 t ht, hy.1 t ht],
    fun t ht h1 h2 => by simp [hx.2 t ht h1 h2, hy.2 t ht h1 h2]⟩
  smul_mem' := fun c x hx => ⟨fun t ht => by simp [hx.1 t ht],
    fun t ht h1 h2 => by simp [hx.2 t ht h1 h2]⟩

private lemma zmod2_eq_one_of_ne_zero {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact (ha rfl).elim
  · rfl

private lemma mem_pathSupp {l : ℕ} {Q : Submodule (ZMod 2) (Fin l → ZMod 2)} {t : Fin l} :
    t ∈ pathSupp Q ↔ ∃ x ∈ Q, x t ≠ 0 := by
  unfold pathSupp
  simp

private lemma mem_pathRuns {l : ℕ} {T : Finset (Fin l)} {t : Fin l} :
    t ∈ pathRuns T ↔ t ∈ T ∧ ∀ ht : t.val + 1 < l, ⟨t.val + 1, ht⟩ ∉ T := by
  unfold pathRuns
  simp

lemma pathGood_le_blockSpace {l : ℕ} (Q : Submodule (ZMod 2) (Fin l → ZMod 2)) (hQ : pathGood Q) :
    Q ≤ blockSpace (pathSupp Q) := by
  intro z hz
  refine ⟨?_, ?_⟩
  · intro t ht
    by_contra hzt
    exact ht (mem_pathSupp.mpr ⟨z, hz, hzt⟩)
  · intro t ht h1 h2
    obtain ⟨x, hxQ, hxt⟩ := mem_pathSupp.mp h1
    obtain ⟨y, hyQ, hyt⟩ := mem_pathSupp.mp h2
    have hxt1 : x t = 1 := zmod2_eq_one_of_ne_zero hxt
    have hyt1 : y ⟨t.val + 1, ht⟩ = 1 := zmod2_eq_one_of_ne_zero hyt
    have hxy := hQ x hxQ y hyQ t ht
    rw [hxt1, hyt1, one_mul] at hxy
    have hxnext_ne : x ⟨t.val + 1, ht⟩ ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hxy
      exact one_ne_zero hxy
    have hxnext1 : x ⟨t.val + 1, ht⟩ = 1 := zmod2_eq_one_of_ne_zero hxnext_ne
    have hxz := hQ x hxQ z hz t ht
    rw [hxt1, hxnext1, one_mul, one_mul] at hxz
    exact hxz.symm

lemma blockSpace_pathGood {l : ℕ} (T : Finset (Fin l)) : pathGood (blockSpace T) := by
  intro x hx y hy t ht
  by_cases h1 : t ∈ T
  · by_cases h2 : ⟨t.val + 1, ht⟩ ∈ T
    · rw [hx.2 t ht h1 h2, hy.2 t ht h1 h2, mul_comm]
    · simp [hx.1 _ h2, hy.1 _ h2]
  · simp [hx.1 _ h1, hy.1 _ h1]

lemma pathSupp_blockSpace {l : ℕ} (T : Finset (Fin l)) : pathSupp (blockSpace T) = T := by
  ext t
  rw [mem_pathSupp]
  constructor
  · rintro ⟨x, hx, hxt⟩
    by_contra ht
    exact hxt (hx.1 t ht)
  · intro ht
    refine ⟨fun s => if s ∈ T then 1 else 0, ⟨?_, ?_⟩, ?_⟩
    · intro s hs
      simp [hs]
    · intro s hs h1 h2
      simp [h1, h2]
    · simp [ht]

private def runExit {l : ℕ} (T : Finset (Fin l)) (t : Fin l) : Fin l :=
  if ht : t.val + 1 < l then
    if ⟨t.val + 1, ht⟩ ∈ T then runExit T ⟨t.val + 1, ht⟩ else t
  else t
termination_by l - t.val

private lemma runExit_mem_pathRuns {l : ℕ} (T : Finset (Fin l)) (t : Fin l) (ht : t ∈ T) :
    runExit T t ∈ pathRuns T := by
  unfold runExit
  split_ifs with hlt hnext
  · exact runExit_mem_pathRuns T ⟨t.val + 1, hlt⟩ hnext
  · exact mem_pathRuns.mpr ⟨ht, fun _ => hnext⟩
  · exact mem_pathRuns.mpr ⟨ht, fun h => (hlt h).elim⟩
termination_by l - t.val

private lemma runExit_of_mem_pathRuns {l : ℕ} (T : Finset (Fin l)) {t : Fin l}
    (ht : t ∈ pathRuns T) : runExit T t = t := by
  unfold runExit
  split_ifs with hlt hnext
  · exact ((mem_pathRuns.mp ht).2 hlt hnext).elim
  · rfl
  · rfl

private lemma runExit_step {l : ℕ} (T : Finset (Fin l)) {t : Fin l} (hlt : t.val + 1 < l)
    (hnext : ⟨t.val + 1, hlt⟩ ∈ T) : runExit T t = runExit T ⟨t.val + 1, hlt⟩ := by
  conv_lhs => unfold runExit
  simp [hlt, hnext]

private lemma eq_at_runExit {l : ℕ} {T : Finset (Fin l)} {x : Fin l → ZMod 2}
    (hx : x ∈ blockSpace T) (t : Fin l) (ht : t ∈ T) : x t = x (runExit T t) := by
  conv_rhs => unfold runExit
  split_ifs with hlt hnext
  · rw [hx.2 t hlt ht hnext]
    exact eq_at_runExit hx ⟨t.val + 1, hlt⟩ hnext
  · rfl
  · rfl
termination_by l - t.val

private def blockSpaceEquiv {l : ℕ} (T : Finset (Fin l)) :
    blockSpace T ≃ₗ[ZMod 2] (↥(pathRuns T) → ZMod 2) where
  toFun x r := x.1 r.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨fun t => if ht : t ∈ T then f ⟨runExit T t, runExit_mem_pathRuns T t ht⟩ else 0,
    ⟨fun t ht => by simp [ht],
     fun t hlt h1 h2 => by
      simp only [h1, h2, ↓reduceDIte]
      congr 1
      exact Subtype.ext (runExit_step T hlt h2)⟩⟩
  left_inv x := by
    ext t
    by_cases ht : t ∈ T
    · simp only [ht, ↓reduceDIte]
      exact (eq_at_runExit x.2 t ht).symm
    · simp only [ht, ↓reduceDIte]
      exact (x.2.1 t ht).symm
  right_inv f := by
    ext r
    have hrT : r.1 ∈ T := (mem_pathRuns.mp r.2).1
    simp only [hrT, ↓reduceDIte]
    congr 1
    exact Subtype.ext (runExit_of_mem_pathRuns T r.2)

lemma finrank_blockSpace {l : ℕ} (T : Finset (Fin l)) :
    Module.finrank (ZMod 2) (blockSpace T) = (pathRuns T).card := by
  rw [(blockSpaceEquiv T).finrank_eq, Module.finrank_pi, Fintype.card_coe]

lemma card_pathRuns_le {l : ℕ} (T : Finset (Fin l)) : (pathRuns T).card ≤ (l + 1) / 2 := by
  let S0 : Finset ℕ := (pathRuns T).image (fun t : Fin l => t.val)
  let S1 : Finset ℕ := (pathRuns T).image (fun t : Fin l => t.val + 1)
  have hdisj : Disjoint S0 S1 := by
    rw [Finset.disjoint_left]
    intro a ha0 ha1
    obtain ⟨t1, ht1, rfl⟩ := Finset.mem_image.mp ha0
    obtain ⟨t2, ht2, h2⟩ := Finset.mem_image.mp ha1
    have hlt : t2.val + 1 < l := h2.symm ▸ t1.isLt
    have heq : (⟨t2.val + 1, hlt⟩ : Fin l) = t1 := Fin.ext h2
    have hnot : (⟨t2.val + 1, hlt⟩ : Fin l) ∉ T := (mem_pathRuns.mp ht2).2 hlt
    rw [heq] at hnot
    exact hnot (mem_pathRuns.mp ht1).1
  have hsub : S0 ∪ S1 ⊆ Finset.range (l + 1) := by
    intro a ha
    rw [Finset.mem_range]
    rcases Finset.mem_union.mp ha with ha0 | ha1
    · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp ha0
      omega
    · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp ha1
      omega
  have hc0 : S0.card = (pathRuns T).card :=
    Finset.card_image_of_injective _ Fin.val_injective
  have hc1 : S1.card = (pathRuns T).card :=
    Finset.card_image_of_injective _ (fun a b h => Fin.val_injective (Nat.succ.inj h))
  have hle : (S0 ∪ S1).card ≤ (Finset.range (l + 1)).card := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hc0, hc1, Finset.card_range] at hle
  omega

lemma finrank_pathGood_le {l : ℕ} (Q : Submodule (ZMod 2) (Fin l → ZMod 2)) (hQ : pathGood Q) :
    Module.finrank (ZMod 2) Q ≤ (l + 1) / 2 := by
  calc Module.finrank (ZMod 2) Q
      ≤ Module.finrank (ZMod 2) (blockSpace (pathSupp Q)) :=
        Submodule.finrank_mono (pathGood_le_blockSpace Q hQ)
    _ = (pathRuns (pathSupp Q)).card := finrank_blockSpace (pathSupp Q)
    _ ≤ (l + 1) / 2 := card_pathRuns_le (pathSupp Q)

private def evenSet (l : ℕ) : Finset (Fin l) :=
  Finset.univ.filter (fun t : Fin l => t.val % 2 = 0)

private lemma pathRuns_evenSet (l : ℕ) : pathRuns (evenSet l) = evenSet l := by
  ext t
  rw [mem_pathRuns]
  simp only [evenSet, Finset.mem_filter, Finset.mem_univ, true_and, and_iff_left_iff_imp]
  intro ht hlt hnext
  omega

private lemma card_evenSet (l : ℕ) : (evenSet l).card = (l + 1) / 2 := by
  have hbij : (evenSet l).card = (Finset.univ : Finset (Fin ((l + 1) / 2))).card := by
    refine Finset.card_bij (fun t _ => ⟨t.val / 2, by omega⟩) ?_ ?_ ?_
    · intro _ _
      exact Finset.mem_univ _
    · intro a ha b hb hab
      simp only [evenSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      have hv : a.val / 2 = b.val / 2 := congrArg Fin.val hab
      exact Fin.ext (by omega)
    · intro i _
      refine ⟨⟨2 * i.val, by omega⟩, ?_, ?_⟩
      · simp [evenSet]
      · exact Fin.ext (by simp)
  simpa using hbij

lemma pathGood_max_exists (l : ℕ) :
    ∃ Q : Submodule (ZMod 2) (Fin l → ZMod 2),
      pathGood Q ∧ Module.finrank (ZMod 2) Q = (l + 1) / 2 := by
  refine ⟨blockSpace (evenSet l), blockSpace_pathGood (evenSet l), ?_⟩
  rw [finrank_blockSpace, pathRuns_evenSet, card_evenSet]

private def tailSet {n : ℕ} (T : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => i.succ ∈ T)

private lemma mem_tailSet {n : ℕ} {T : Finset (Fin (n + 1))} {i : Fin n} :
    i ∈ tailSet T ↔ i.succ ∈ T := by
  simp [tailSet]

private lemma succ_mem_pathRuns_iff {n : ℕ} (T : Finset (Fin (n + 1))) (i : Fin n) :
    i.succ ∈ pathRuns T ↔ i ∈ pathRuns (tailSet T) := by
  rw [mem_pathRuns, mem_pathRuns, mem_tailSet]
  constructor
  · rintro ⟨hi, hnext⟩
    refine ⟨hi, fun hlt hmem => ?_⟩
    have hlt' : i.succ.val + 1 < n + 1 := by simp; omega
    have hmem' : (⟨i.succ.val + 1, hlt'⟩ : Fin (n + 1)) ∈ T := by
      have heq : (⟨i.succ.val + 1, hlt'⟩ : Fin (n + 1)) = (⟨i.val + 1, hlt⟩ : Fin n).succ := by
        ext; simp
      rw [heq]
      exact mem_tailSet.mp hmem
    exact hnext hlt' hmem'
  · rintro ⟨hi, hnext⟩
    refine ⟨hi, fun hlt hmem => ?_⟩
    have hlt' : i.val + 1 < n := by simp at hlt; omega
    have heq : (⟨i.succ.val + 1, hlt⟩ : Fin (n + 1)) = (⟨i.val + 1, hlt'⟩ : Fin n).succ := by
      ext; simp
    rw [heq] at hmem
    exact hnext hlt' (mem_tailSet.mpr hmem)

private lemma card_pathRuns_succ {n : ℕ} (T : Finset (Fin (n + 1))) :
    (pathRuns T).card = (pathRuns (tailSet T)).card +
      if (0 : Fin (n + 1)) ∈ pathRuns T then 1 else 0 := by
  let S := (pathRuns (tailSet T)).map (Fin.succEmb n)
  have hS : S.card = (pathRuns (tailSet T)).card := Finset.card_map _
  have h0S : (0 : Fin (n + 1)) ∉ S := by
    simp [S, Fin.succ_ne_zero]
  by_cases h0 : (0 : Fin (n + 1)) ∈ pathRuns T
  · have heq : pathRuns T = insert 0 S := by
      ext x
      refine Fin.cases ?_ ?_ x
      · simp [h0]
      · intro i
        simp [S, succ_mem_pathRuns_iff]
    rw [heq, Finset.card_insert_of_notMem h0S, hS]
    simp [Nat.add_comm]
  · have heq : pathRuns T = S := by
      ext x
      refine Fin.cases ?_ ?_ x
      · simp [h0, h0S]
      · intro i
        simp [S, succ_mem_pathRuns_iff]
    rw [heq, hS]
    simp [h0S]

private lemma zero_mem_pathRuns_iff {m : ℕ} (T : Finset (Fin (m + 2))) :
    (0 : Fin (m + 2)) ∈ pathRuns T ↔
      (0 : Fin (m + 2)) ∈ T ∧ (0 : Fin (m + 1)).succ ∉ T := by
  rw [mem_pathRuns]
  constructor
  · rintro ⟨h0, hnext⟩
    refine ⟨h0, ?_⟩
    have hlt : (0 : Fin (m + 2)).val + 1 < m + 2 := by simp
    have heq : (⟨(0 : Fin (m + 2)).val + 1, hlt⟩ : Fin (m + 2)) = (0 : Fin (m + 1)).succ := by
      ext; simp
    rw [← heq]
    exact hnext hlt
  · rintro ⟨h0, h1⟩
    refine ⟨h0, fun hlt hmem => ?_⟩
    have heq : (⟨(0 : Fin (m + 2)).val + 1, hlt⟩ : Fin (m + 2)) = (0 : Fin (m + 1)).succ := by
      ext; simp
    rw [heq] at hmem
    exact h1 hmem

private lemma card_pathRuns_of_zero_notMem {n : ℕ} {T : Finset (Fin (n + 1))}
    (h0 : (0 : Fin (n + 1)) ∉ T) : (pathRuns T).card = (pathRuns (tailSet T)).card := by
  have h0' : (0 : Fin (n + 1)) ∉ pathRuns T := fun h => h0 (mem_pathRuns.mp h).1
  rw [card_pathRuns_succ]
  simp [h0']

private def maxRuns (l : ℕ) : Finset (Finset (Fin l)) :=
  Finset.univ.filter (fun T => (pathRuns T).card = (l + 1) / 2)

private lemma mem_maxRuns {l : ℕ} {T : Finset (Fin l)} :
    T ∈ maxRuns l ↔ (pathRuns T).card = (l + 1) / 2 := by
  simp [maxRuns]

private lemma evenSet_mem_maxRuns (l : ℕ) : evenSet l ∈ maxRuns l := by
  rw [mem_maxRuns, pathRuns_evenSet, card_evenSet]

private lemma card_filter_split {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] :
    (s.filter P).card + (s.filter (fun x => ¬ P x)).card = s.card := by
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  trans ∑ _x ∈ s, 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : P x <;> simp [h]
  · simp

private lemma maxRuns_odd (k : ℕ) : maxRuns (2 * k + 1) = {evenSet (2 * k + 1)} := by
  induction k with
  | zero =>
    ext T
    rw [mem_maxRuns, Finset.mem_singleton]
    constructor
    · intro hcard
      have hne : (pathRuns T).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨t, ht⟩ := hne
      have ht0 : t = 0 := Fin.ext (by omega)
      subst ht0
      ext x
      have hx0 : x = 0 := Fin.ext (by omega)
      subst hx0
      simp [(mem_pathRuns.mp ht).1, evenSet]
    · rintro rfl
      rw [pathRuns_evenSet, card_evenSet]
  | succ k ih =>
    ext T
    rw [Finset.mem_singleton]
    constructor
    · intro hT
      have hcard : (pathRuns T).card = k + 2 := by
        have h := mem_maxRuns.mp hT
        omega
      have hstep := card_pathRuns_succ T
      have hle : (pathRuns (tailSet T)).card ≤ k + 1 := by
        have h := card_pathRuns_le (tailSet T)
        omega
      have h0pr : (0 : Fin (2 * k + 3)) ∈ pathRuns T := by
        by_contra h0
        simp only [h0, ↓reduceIte] at hstep
        omega
      have ⟨h0T, h1T⟩ := (zero_mem_pathRuns_iff T).mp h0pr
      have htail_card : (pathRuns (tailSet T)).card = k + 1 := by
        simp only [h0pr, ↓reduceIte] at hstep
        omega
      have h0tail : (0 : Fin (2 * k + 2)) ∉ tailSet T := by
        rw [mem_tailSet]
        exact h1T
      have htail2_card : (pathRuns (tailSet (tailSet T))).card = k + 1 := by
        rw [← card_pathRuns_of_zero_notMem h0tail]
        exact htail_card
      have htail2_mem : tailSet (tailSet T) ∈ maxRuns (2 * k + 1) := by
        rw [mem_maxRuns]
        omega
      rw [ih, Finset.mem_singleton] at htail2_mem
      ext x
      refine Fin.cases ?_ ?_ x
      · simp [h0T, evenSet]
      · intro y
        refine Fin.cases ?_ ?_ y
        · simp only [evenSet, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro h
            exact (h1T h).elim
          · intro h
            simp only [Fin.val_succ, Fin.val_zero] at h
            omega
        · intro z
          have hz : z ∈ tailSet (tailSet T) ↔ z ∈ evenSet (2 * k + 1) := by
            rw [htail2_mem]
          simp only [tailSet, evenSet, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
          rw [hz]
          simp only [Fin.val_succ]
          omega
    · rintro rfl
      exact evenSet_mem_maxRuns (2 * k + 3)

private lemma card_maxRuns_even (k : ℕ) : (maxRuns (2 * k)).card = 2 * k + 1 := by
  induction k with
  | zero =>
    have h : maxRuns 0 = {∅} := by
      ext T
      rw [mem_maxRuns, Finset.mem_singleton]
      have hT : T = ∅ := Subsingleton.elim T ∅
      subst hT
      simp [pathRuns]
    rw [h, Finset.card_singleton]
  | succ k ih =>
    change (maxRuns (2 * k + 2)).card = 2 * k + 3
    let P : Finset (Fin (2 * k + 2)) → Prop :=
      fun T => (0 : Fin (2 * k + 2)) ∈ T ∧ (0 : Fin (2 * k + 1)).succ ∉ T
    have hsplit : ((maxRuns (2 * k + 2)).filter P).card +
        ((maxRuns (2 * k + 2)).filter (fun T => ¬ P T)).card =
        (maxRuns (2 * k + 2)).card :=
      card_filter_split (maxRuns (2 * k + 2)) P
    have hP : ((maxRuns (2 * k + 2)).filter P).card = (maxRuns (2 * k)).card := by
      refine Finset.card_bij (fun T _ => tailSet (tailSet T)) ?_ ?_ ?_
      · intro T hT
        rw [Finset.mem_filter, mem_maxRuns] at hT
        rcases hT with ⟨hcard, h0T, h1T⟩
        have h0pr : (0 : Fin (2 * k + 2)) ∈ pathRuns T :=
          (zero_mem_pathRuns_iff T).mpr ⟨h0T, h1T⟩
        have hstep := card_pathRuns_succ T
        simp only [h0pr, ↓reduceIte] at hstep
        have h0tail : (0 : Fin (2 * k + 1)) ∉ tailSet T := by
          rw [mem_tailSet]
          exact h1T
        have htail2 := card_pathRuns_of_zero_notMem h0tail
        rw [mem_maxRuns]
        omega
      · intro T1 hT1 T2 hT2 heq
        rw [Finset.mem_filter] at hT1 hT2
        ext x
        refine Fin.cases ?_ ?_ x
        · simp [hT1.2.1, hT2.2.1]
        · intro y
          refine Fin.cases ?_ ?_ y
          · simp only [hT1.2.2, hT2.2.2]
          · intro z
            have hz : z ∈ tailSet (tailSet T1) ↔ z ∈ tailSet (tailSet T2) := by
              rw [heq]
            simpa [tailSet] using hz
      · intro S hS
        let T : Finset (Fin (2 * k + 2)) :=
          insert 0 ((S.map (Fin.succEmb (2 * k))).map (Fin.succEmb (2 * k + 1)))
        have h0T : (0 : Fin (2 * k + 2)) ∈ T := Finset.mem_insert_self _ _
        have h1T : (0 : Fin (2 * k + 1)).succ ∉ T := by
          intro h
          simp only [T, Finset.mem_insert, Finset.mem_map] at h
          rcases h with h | ⟨_, ⟨x, _, rfl⟩, h⟩
          · exact Fin.succ_ne_zero _ h
          · exact Fin.succ_ne_zero _ (Fin.succ_injective _ h)
        have htail2 : tailSet (tailSet T) = S := by
          ext z
          simp [T, tailSet]
        have hTmem : T ∈ (maxRuns (2 * k + 2)).filter P := by
          rw [Finset.mem_filter, mem_maxRuns]
          refine ⟨?_, h0T, h1T⟩
          have h0pr : (0 : Fin (2 * k + 2)) ∈ pathRuns T :=
            (zero_mem_pathRuns_iff T).mpr ⟨h0T, h1T⟩
          have hstep := card_pathRuns_succ T
          simp only [h0pr, ↓reduceIte] at hstep
          have h0tail : (0 : Fin (2 * k + 1)) ∉ tailSet T := by
            rw [mem_tailSet]
            exact h1T
          rw [card_pathRuns_of_zero_notMem h0tail, htail2] at hstep
          have hScard := mem_maxRuns.mp hS
          omega
        exact ⟨T, hTmem, htail2⟩
    let T1 : Finset (Fin (2 * k + 2)) := (evenSet (2 * k + 1)).map (Fin.succEmb (2 * k + 1))
    let T2 : Finset (Fin (2 * k + 2)) := insert 0 T1
    have hnotP_eq : (maxRuns (2 * k + 2)).filter (fun T => ¬ P T) = {T1, T2} := by
      ext T
      rw [Finset.mem_filter, mem_maxRuns, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hcard, hnP⟩
        have h0pr : (0 : Fin (2 * k + 2)) ∉ pathRuns T := by
          intro h
          exact hnP ((zero_mem_pathRuns_iff T).mp h)
        have hstep := card_pathRuns_succ T
        simp only [h0pr, ↓reduceIte, Nat.add_zero] at hstep
        have htail_mem : tailSet T ∈ maxRuns (2 * k + 1) := by
          rw [mem_maxRuns]
          omega
        rw [maxRuns_odd k, Finset.mem_singleton] at htail_mem
        by_cases h0T : (0 : Fin (2 * k + 2)) ∈ T
        · right
          ext x
          refine Fin.cases ?_ ?_ x
          · simp [h0T, T2]
          · intro y
            have hy : y ∈ tailSet T ↔ y ∈ evenSet (2 * k + 1) := by rw [htail_mem]
            simpa [T2, T1, tailSet] using hy
        · left
          ext x
          refine Fin.cases ?_ ?_ x
          · simp [h0T, T1, Fin.succ_ne_zero]
          · intro y
            have hy : y ∈ tailSet T ↔ y ∈ evenSet (2 * k + 1) := by rw [htail_mem]
            simpa [T1, tailSet] using hy
      · intro h
        have htail_eq : tailSet T = evenSet (2 * k + 1) := by
          rcases h with rfl | rfl
          · ext y; simp [T1, tailSet]
          · ext y; simp [T2, T1, tailSet]
        have h1T : (0 : Fin (2 * k + 1)).succ ∈ T := by
          have h0e : (0 : Fin (2 * k + 1)) ∈ evenSet (2 * k + 1) := by simp [evenSet]
          rw [← htail_eq, mem_tailSet] at h0e
          exact h0e
        have hnP : ¬ P T := fun hP => hP.2 h1T
        have h0pr : (0 : Fin (2 * k + 2)) ∉ pathRuns T := fun h0 =>
          hnP ((zero_mem_pathRuns_iff T).mp h0)
        refine ⟨?_, hnP⟩
        rw [card_pathRuns_succ]
        simp only [h0pr, ↓reduceIte, Nat.add_zero, htail_eq, pathRuns_evenSet, card_evenSet]
        omega
    have hT12 : T1 ≠ T2 := by
      intro heq
      have h0T2 : (0 : Fin (2 * k + 2)) ∈ T2 := Finset.mem_insert_self _ _
      rw [← heq] at h0T2
      simp [T1, Fin.succ_ne_zero] at h0T2
    have hnotP : ((maxRuns (2 * k + 2)).filter (fun T => ¬ P T)).card = 2 := by
      rw [hnotP_eq, Finset.card_pair hT12]
    omega

private lemma card_maxRuns (l : ℕ) :
    (maxRuns l).card = if l % 2 = 0 then l + 1 else 1 := by
  by_cases h : l % 2 = 0
  · simp only [h, ↓reduceIte]
    have hl : l = 2 * (l / 2) := by omega
    conv_lhs => rw [hl]
    rw [card_maxRuns_even]
    omega
  · simp only [h, ↓reduceIte]
    have hl : l = 2 * (l / 2) + 1 := by omega
    conv_lhs => rw [hl]
    rw [maxRuns_odd, Finset.card_singleton]

lemma card_pathGood_max (l : ℕ) :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    letI : Fintype (Submodule (ZMod 2) (Fin l → ZMod 2)) := Fintype.ofFinite _
    ((Finset.univ : Finset (Submodule (ZMod 2) (Fin l → ZMod 2))).filter
      (fun Q => pathGood Q ∧ Module.finrank (ZMod 2) Q = (l + 1) / 2)).card =
      if l % 2 = 0 then l + 1 else 1 := by
  let _ : ∀ P : Prop, Decidable P := Classical.propDecidable
  let _ : Fintype (Submodule (ZMod 2) (Fin l → ZMod 2)) := Fintype.ofFinite _
  trans (maxRuns l).card
  · symm
    refine Finset.card_bij (fun T _ => blockSpace T) ?_ ?_ ?_
    · intro T hT
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, blockSpace_pathGood T, ?_⟩
      rw [finrank_blockSpace, mem_maxRuns.mp hT]
    · intro T1 _ T2 _ h
      have hs := congrArg pathSupp h
      rwa [pathSupp_blockSpace, pathSupp_blockSpace] at hs
    · intro Q hQ
      rw [Finset.mem_filter] at hQ
      rcases hQ with ⟨_, hgood, hfr⟩
      have hle : Q ≤ blockSpace (pathSupp Q) := pathGood_le_blockSpace Q hgood
      have hfr_le : Module.finrank (ZMod 2) Q ≤ Module.finrank (ZMod 2) (blockSpace (pathSupp Q)) :=
        Submodule.finrank_mono hle
      have hfr_bs : Module.finrank (ZMod 2) (blockSpace (pathSupp Q)) =
          (pathRuns (pathSupp Q)).card := finrank_blockSpace (pathSupp Q)
      have hruns_le : (pathRuns (pathSupp Q)).card ≤ (l + 1) / 2 := card_pathRuns_le (pathSupp Q)
      have hruns_ge : (l + 1) / 2 ≤ (pathRuns (pathSupp Q)).card := by
        rw [← hfr, ← hfr_bs]
        exact hfr_le
      have hruns_eq : (pathRuns (pathSupp Q)).card = (l + 1) / 2 :=
        le_antisymm hruns_le hruns_ge
      have hfr_eq : Module.finrank (ZMod 2) Q = Module.finrank (ZMod 2) (blockSpace (pathSupp Q)) := by
        rw [hfr, hfr_bs, hruns_eq]
      refine ⟨pathSupp Q, mem_maxRuns.mpr hruns_eq, ?_⟩
      exact (Submodule.eq_of_le_of_finrank_eq hle hfr_eq).symm
  · rw [card_maxRuns l]
    split_ifs <;> rfl

def syndromeMap {n m : ℕ} (h : Fin n → Fin m → ZMod 2) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) where
  toFun x b := ∑ i : Fin n, h i b * x i
  map_add' x y := by
    funext b
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext b
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

def goodSpace {n m : ℕ} (h : Fin n → Fin m → ZMod 2)
    (E : Submodule (ZMod 2) (Fin n → ZMod 2)) : Prop :=
  (∀ x ∈ E, ∀ b : Fin m, (∑ i : Fin n, h i b * x i) = 0) ∧
  (∀ x ∈ E, ∀ y ∈ E, ∀ i : Fin n, x i * y (nextFn i) = x (nextFn i) * y i)

noncomputable def suppFn {n : ℕ} (U : Submodule (ZMod 2) (Fin n → ZMod 2)) : Finset (Fin n) :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  Finset.univ.filter (fun i : Fin n => ∃ x ∈ U, x i ≠ 0)

private lemma mem_suppFn {n : ℕ} {U : Submodule (ZMod 2) (Fin n → ZMod 2)} {i : Fin n} :
    i ∈ suppFn U ↔ ∃ x ∈ U, x i ≠ 0 := by
  unfold suppFn
  simp

private def allowedSpace {n : ℕ} (S : Finset (Fin n)) : Submodule (ZMod 2) (Fin n → ZMod 2) where
  carrier := {x | (∀ v, v ∉ S → v ∉ allPaths S → x v = 0) ∧
    (∀ i ∈ S, nextFn i ∈ S → x i = x (nextFn i))}
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩; add_mem' := fun hx hy =>
    ⟨fun v hvS hvP => by simp [hx.1 v hvS hvP, hy.1 v hvS hvP],
     fun i hi hni => by simp [hx.2 i hi hni, hy.2 i hi hni]⟩
  smul_mem' := fun c x hx =>
    ⟨fun v hvS hvP => by simp [hx.1 v hvS hvP],
     fun i hi hni => by simp [hx.2 i hi hni]⟩

private def projOne {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin (gapFn S i - 2) → ZMod 2) where
  toFun x t := x (pathPt S i t)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def projAll {n : ℕ} (S : Finset (Fin n)) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] (∀ i : ↥(exitsFn S), Fin (gapFn S i.1 - 2) → ZMod 2) where
  toFun x i t := x (pathPt S i.1 t)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma host_le_allowedSpace {n m : ℕ} (hn : 3 ≤ n) (h : Fin n → Fin m → ZMod 2)
    {U E : Submodule (ZMod 2) (Fin n → ZMod 2)} (hUE : U ≤ E) (hE : goodSpace h E)
    (hSne : (suppFn U).Nonempty) (hSnu : suppFn U ≠ Finset.univ) :
    E ≤ allowedSpace (suppFn U) := by
  intro x hxE
  refine ⟨?_, ?_⟩
  · intro v hvS hvP
    rcases not_mem_S_union_allPaths_adj hn (suppFn U) hSne hSnu v hvS hvP with hnext | ⟨u, huS, huv⟩
    · obtain ⟨w, hwU, hwn⟩ := mem_suppFn.mp hnext
      have hwn1 : w (nextFn v) = 1 := zmod2_eq_one_of_ne_zero hwn
      have hwv0 : w v = 0 := by
        by_contra hne
        exact hvS (mem_suppFn.mpr ⟨w, hwU, hne⟩)
      have hiso := hE.2 w (hUE hwU) x hxE v
      rw [hwv0, hwn1, zero_mul, one_mul] at hiso
      exact hiso.symm
    · obtain ⟨w, hwU, hwu⟩ := mem_suppFn.mp huS
      have hwu1 : w u = 1 := zmod2_eq_one_of_ne_zero hwu
      have hwv0 : w v = 0 := by
        by_contra hne
        exact hvS (mem_suppFn.mpr ⟨w, hwU, hne⟩)
      have hiso := hE.2 w (hUE hwU) x hxE u
      rw [huv, hwu1, hwv0, one_mul, zero_mul] at hiso
      exact hiso
  · intro i hi hni
    obtain ⟨w, hwU, hwi⟩ := mem_suppFn.mp hi
    obtain ⟨y, hyU, hyni⟩ := mem_suppFn.mp hni
    have hwi1 : w i = 1 := zmod2_eq_one_of_ne_zero hwi
    have hyni1 : y (nextFn i) = 1 := zmod2_eq_one_of_ne_zero hyni
    have hwy := hE.2 w (hUE hwU) y (hUE hyU) i
    rw [hwi1, hyni1, one_mul] at hwy
    have hwni_ne : w (nextFn i) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hwy
      exact one_ne_zero hwy
    have hwni1 : w (nextFn i) = 1 := zmod2_eq_one_of_ne_zero hwni_ne
    have hwx := hE.2 w (hUE hwU) x hxE i
    rw [hwi1, hwni1, one_mul, one_mul] at hwx
    exact hwx.symm

private lemma host_projOne_pathGood {n m : ℕ} (h : Fin n → Fin m → ZMod 2)
    (S : Finset (Fin n)) {E : Submodule (ZMod 2) (Fin n → ZMod 2)} (hE : goodSpace h E)
    (i : Fin n) : pathGood (E.map (projOne S i)) := by
  rintro _ ⟨x, hxE, rfl⟩ _ ⟨y, hyE, rfl⟩ t ht
  simp only [projOne, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← nextFn_pathPt S i t ht]
  exact hE.2 x hxE y hyE (pathPt S i t)

private lemma ker_projAll_inf_allowed {n : ℕ} (hn : 3 ≤ n) (S : Finset (Fin n)) :
    allowedSpace S ⊓ LinearMap.ker (projAll S) = runConstSpace S := by
  ext x
  simp only [Submodule.mem_inf, LinearMap.mem_ker]
  constructor
  · rintro ⟨hxA, hxP⟩
    refine ⟨?_, hxA.2⟩
    intro v hvS
    by_cases hvP : v ∈ allPaths S
    · rw [allPaths, Finset.mem_biUnion] at hvP
      rcases hvP with ⟨i, hi, hvi⟩
      rw [pathSet, Finset.mem_image] at hvi
      rcases hvi with ⟨t, _, rfl⟩
      have h0 := congrFun (congrFun hxP ⟨i, hi⟩) t
      exact h0
    · exact hxA.1 v hvS hvP
  · intro hxR
    refine ⟨⟨fun v hvS _ => hxR.1 v hvS, hxR.2⟩, ?_⟩
    funext i t
    have hnotS : pathPt S i.1 t ∉ S :=
      Finset.disjoint_left.mp (pathSet_disjoint_S hn S i.1 i.2)
        (Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩)
    exact hxR.1 _ hnotS

private def piSubmoduleEquiv {ι : Type*} {R : Type*} [Semiring R] {M : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    (Q : ∀ i, Submodule R (M i)) :
    (Submodule.pi Set.univ Q) ≃ₗ[R] (∀ i, Q i) where
  toFun f i := ⟨f.1 i, f.2 i trivial⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun g := ⟨fun i => (g i).1, fun i _ => (g i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma finrank_pi_submodule {ι : Type*} [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod 2) (M i)] [∀ i, Module.Finite (ZMod 2) (M i)]
    (Q : ∀ i, Submodule (ZMod 2) (M i)) :
    Module.finrank (ZMod 2) (Submodule.pi Set.univ Q) = ∑ i : ι, Module.finrank (ZMod 2) (Q i) := by
  have _ : ∀ i, Module.Finite (ZMod 2) (Q i) := fun i => inferInstance
  rw [(piSubmoduleEquiv Q).finrank_eq, Module.finrank_pi_fintype]

private lemma finrank_K0 {n m : ℕ} (hn : 3 ≤ n) (h : Fin n → Fin m → ZMod 2)
    (S : Finset (Fin n)) (hSne : S.Nonempty) (hSnu : S ≠ Finset.univ)
    (hSurj : ∀ z : Fin m → ZMod 2, ∃ x ∈ runConstSpace S, syndromeMap h x = z) :
    Module.finrank (ZMod 2) ↥(runConstSpace S ⊓ LinearMap.ker (syndromeMap h)) =
      (exitsFn S).card - m ∧ m ≤ (exitsFn S).card := by
  let f : runConstSpace S →ₗ[ZMod 2] (Fin m → ZMod 2) :=
    (syndromeMap h).comp (runConstSpace S).subtype
  have hrange : LinearMap.range f = ⊤ := by
    rw [eq_top_iff]
    intro z _
    rcases hSurj z with ⟨x, hxR, hxz⟩
    exact ⟨⟨x, hxR⟩, hxz⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, finrank_top, Module.finrank_pi, Fintype.card_fin,
      finrank_runConstSpace hn S hSne hSnu] at hrk
  let e : LinearMap.ker f ≃ₗ[ZMod 2] ↥(runConstSpace S ⊓ LinearMap.ker (syndromeMap h)) :=
    { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [e.finrank_eq] at hrk
  omega

private def liftTuple {n m : ℕ} (h : Fin n → Fin m → ZMod 2) (S : Finset (Fin n))
    (Q : ∀ i : ↥(exitsFn S), Submodule (ZMod 2) (Fin (gapFn S i.1 - 2) → ZMod 2)) :
    Submodule (ZMod 2) (Fin n → ZMod 2) :=
  allowedSpace S ⊓ LinearMap.ker (syndromeMap h) ⊓ (Submodule.pi Set.univ Q).comap (projAll S)

private lemma path_not_adj_S_left {n : ℕ} (hn : 3 ≤ n) (S : Finset (Fin n))
    {v : Fin n} (hvS : v ∈ S) (hnextP : nextFn v ∈ allPaths S) : False := by
  rw [allPaths, Finset.mem_biUnion] at hnextP
  rcases hnextP with ⟨i, hi, hvi⟩
  rw [pathSet, Finset.mem_image] at hvi
  rcases hvi with ⟨t, _, htv⟩
  have hspec := gapFn_spec hn S i hi
  have heq : nextFn (moveFn i (t.val + 1)) = nextFn v := by
    rw [nextFn_moveFn, ← htv, pathPt]
  have hv_eq : moveFn i (t.val + 1) = v := nextFn_injective heq
  have hnotS := hspec.2.2.1 (t.val + 1) (by omega) (by omega)
  rw [hv_eq] at hnotS
  exact hnotS hvS

private lemma path_not_adj_S_right {n : ℕ} (hn : 3 ≤ n) (S : Finset (Fin n))
    {v : Fin n} (hvP : v ∈ allPaths S) (hnextS : nextFn v ∈ S) : False := by
  rw [allPaths, Finset.mem_biUnion] at hvP
  rcases hvP with ⟨i, hi, hvi⟩
  rw [pathSet, Finset.mem_image] at hvi
  rcases hvi with ⟨t, _, rfl⟩
  have hspec := gapFn_spec hn S i hi
  rw [pathPt, nextFn_moveFn] at hnextS
  exact hspec.2.2.1 (t.val + 2 + 1) (by omega) (by omega) hnextS

private lemma liftTuple_good {n m : ℕ} (hn : 3 ≤ n) (h : Fin n → Fin m → ZMod 2)
    (S : Finset (Fin n))
    (Q : ∀ i : ↥(exitsFn S), Submodule (ZMod 2) (Fin (gapFn S i.1 - 2) → ZMod 2))
    (hQ : ∀ i, pathGood (Q i)) :
    goodSpace h (liftTuple h S Q) := by
  refine ⟨?_, ?_⟩
  · intro x hx b
    exact congrFun hx.1.2 b
  · intro x hx y hy v
    by_cases hvS : v ∈ S
    · by_cases hnvS : nextFn v ∈ S
      · rw [hx.1.1.2 v hvS hnvS, hy.1.1.2 v hvS hnvS, mul_comm]
      · by_cases hnvP : nextFn v ∈ allPaths S
        · exact (path_not_adj_S_left hn S hvS hnvP).elim
        · simp [hx.1.1.1 (nextFn v) hnvS hnvP, hy.1.1.1 (nextFn v) hnvS hnvP]
    · by_cases hvP : v ∈ allPaths S
      · by_cases hnvS : nextFn v ∈ S
        · exact (path_not_adj_S_right hn S hvP hnvS).elim
        · by_cases hnvP : nextFn v ∈ allPaths S
          · rw [allPaths, Finset.mem_biUnion] at hvP
            rcases hvP with ⟨i, hi, hvi⟩
            rw [pathSet, Finset.mem_image] at hvi
            rcases hvi with ⟨t, _, rfl⟩
            have ht : t.val + 1 < gapFn S i - 2 := pathSet_nextFn_mem hn S i hi t hnvP
            rw [nextFn_pathPt S i t ht]
            have hxQ : projAll S x ⟨i, hi⟩ ∈ Q ⟨i, hi⟩ := hx.2 ⟨i, hi⟩ trivial
            have hyQ : projAll S y ⟨i, hi⟩ ∈ Q ⟨i, hi⟩ := hy.2 ⟨i, hi⟩ trivial
            exact hQ ⟨i, hi⟩ _ hxQ _ hyQ t ht
          · simp [hx.1.1.1 (nextFn v) hnvS hnvP, hy.1.1.1 (nextFn v) hnvS hnvP]
      · simp [hx.1.1.1 v hvS hvP, hy.1.1.1 v hvS hvP]

private lemma le_liftTuple_of_U {n m : ℕ} (hn : 3 ≤ n) (h : Fin n → Fin m → ZMod 2)
    {U : Submodule (ZMod 2) (Fin n → ZMod 2)} (hU : goodSpace h U)
    (hSne : (suppFn U).Nonempty) (hSnu : suppFn U ≠ Finset.univ)
    (Q : ∀ i : ↥(exitsFn (suppFn U)), Submodule (ZMod 2) (Fin (gapFn (suppFn U) i.1 - 2) → ZMod 2)) :
    U ≤ liftTuple h (suppFn U) Q := by
  intro u huU
  have huA : u ∈ allowedSpace (suppFn U) :=
    host_le_allowedSpace hn h (le_refl U) hU hSne hSnu huU
  have huK : u ∈ LinearMap.ker (syndromeMap h) := by
    rw [LinearMap.mem_ker]
    funext b
    exact hU.1 u huU b
  have huP : projAll (suppFn U) u = 0 := by
    funext i t
    have hnotS : pathPt (suppFn U) i.1 t ∉ suppFn U :=
      Finset.disjoint_left.mp (pathSet_disjoint_S hn (suppFn U) i.1 i.2)
        (Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩)
    by_contra hne
    exact hnotS (mem_suppFn.mpr ⟨u, huU, hne⟩)
  refine ⟨⟨huA, huK⟩, ?_⟩
  change projAll (suppFn U) u ∈ Submodule.pi Set.univ Q
  rw [huP]
  exact Submodule.zero_mem _

private lemma liftTuple_map_projAll {n m : ℕ} (hn : 3 ≤ n) (h : Fin n → Fin m → ZMod 2)
    (S : Finset (Fin n))
    (hSurj : ∀ z : Fin m → ZMod 2, ∃ x ∈ runConstSpace S, syndromeMap h x = z)
    (Q : ∀ i : ↥(exitsFn S), Submodule (ZMod 2) (Fin (gapFn S i.1 - 2) → ZMod 2)) :
    (liftTuple h S Q).map (projAll S) = Submodule.pi Set.univ Q := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  · intro q hq
    let xP : Fin n → ZMod 2 := fun v =>
      if hv : ∃ i : ↥(exitsFn S), ∃ t : Fin (gapFn S i.1 - 2), pathPt S i.1 t = v then
        q hv.choose hv.choose_spec.choose
      else 0
    have hxP_proj : projAll S xP = q := by
      funext i t
      have hex : ∃ i' : ↥(exitsFn S), ∃ t' : Fin (gapFn S i'.1 - 2),
          pathPt S i'.1 t' = pathPt S i.1 t := ⟨i, t, rfl⟩
      simp only [projAll, LinearMap.coe_mk, AddHom.coe_mk, xP, hex, ↓reduceDIte]
      have hpair : ∀ (j : ↥(exitsFn S)) (s : Fin (gapFn S j.1 - 2)),
          pathPt S j.1 s = pathPt S i.1 t → q j s = q i t := by
        intro j s hjs
        have hji : j = i := by
          apply Subtype.ext
          by_contra hne
          have hdisj := pathSet_pairwiseDisjoint hn S j.2 i.2 hne
          have hm1 : pathPt S j.1 s ∈ pathSet S j.1 :=
            Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
          have hm2 : pathPt S i.1 t ∈ pathSet S i.1 :=
            Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
          rw [hjs] at hm1
          exact Finset.disjoint_left.mp hdisj hm1 hm2
        subst hji
        have hst : s = t := pathPt_injective hn S j.1 j.2 hjs
        rw [hst]
      exact hpair hex.choose hex.choose_spec.choose hex.choose_spec.choose_spec
    have hxP_zero_S : ∀ v ∈ S, xP v = 0 := by
      intro v hvS
      have hnot : ¬ ∃ i : ↥(exitsFn S), ∃ t : Fin (gapFn S i.1 - 2), pathPt S i.1 t = v := by
        rintro ⟨i, t, rfl⟩
        exact Finset.disjoint_left.mp (pathSet_disjoint_S hn S i.1 i.2)
          (Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩) hvS
      simp only [xP, hnot, ↓reduceDIte]
    have hxP_allowed : xP ∈ allowedSpace S := by
      refine ⟨?_, ?_⟩
      · intro v _ hvP
        have hnot : ¬ ∃ i : ↥(exitsFn S), ∃ t : Fin (gapFn S i.1 - 2), pathPt S i.1 t = v := by
          rintro ⟨i, t, rfl⟩
          exact hvP (Finset.mem_biUnion.mpr ⟨i.1, i.2, Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩⟩)
        simp only [xP, hnot, ↓reduceDIte]
      · intro v hvS hnvS
        rw [hxP_zero_S v hvS, hxP_zero_S (nextFn v) hnvS]
    obtain ⟨xS, hxS_R, hxS_syn⟩ := hSurj (syndromeMap h xP)
    have hxS_allowed : xS ∈ allowedSpace S := ⟨fun v hvS _ => hxS_R.1 v hvS, hxS_R.2⟩
    have hxS_proj : projAll S xS = 0 := by
      funext i t
      have hnotS : pathPt S i.1 t ∉ S :=
        Finset.disjoint_left.mp (pathSet_disjoint_S hn S i.1 i.2)
          (Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩)
      exact hxS_R.1 _ hnotS
    refine ⟨xS + xP, ?_, ?_⟩
    · refine ⟨⟨(allowedSpace S).add_mem hxS_allowed hxP_allowed, ?_⟩, ?_⟩
      · change syndromeMap h (xS + xP) = 0
        rw [map_add, hxS_syn]
        funext b
        exact CharTwo.add_self_eq_zero _
      · change projAll S (xS + xP) ∈ Submodule.pi Set.univ Q
        rw [map_add, hxS_proj, zero_add, hxP_proj]
        exact hq
    · rw [map_add, hxS_proj, zero_add, hxP_proj]

private lemma finrank_liftTuple {n m : ℕ} (hn : 3 ≤ n) (h : Fin n → Fin m → ZMod 2)
    (S : Finset (Fin n)) (hSne : S.Nonempty) (hSnu : S ≠ Finset.univ)
    (hSurj : ∀ z : Fin m → ZMod 2, ∃ x ∈ runConstSpace S, syndromeMap h x = z)
    (Q : ∀ i : ↥(exitsFn S), Submodule (ZMod 2) (Fin (gapFn S i.1 - 2) → ZMod 2)) :
    Module.finrank (ZMod 2) (liftTuple h S Q) =
      (exitsFn S).card - m + ∑ i : ↥(exitsFn S), Module.finrank (ZMod 2) (Q i) := by
  let g : liftTuple h S Q →ₗ[ZMod 2] (∀ i : ↥(exitsFn S), Fin (gapFn S i.1 - 2) → ZMod 2) :=
    (projAll S).comp (liftTuple h S Q).subtype
  have hrk := LinearMap.finrank_range_add_finrank_ker g
  have hrange : LinearMap.range g = Submodule.pi Set.univ Q := by
    rw [LinearMap.range_comp, Submodule.range_subtype, liftTuple_map_projAll hn h S hSurj Q]
  have hker_eq : Module.finrank (ZMod 2) (LinearMap.ker g) =
      Module.finrank (ZMod 2) ↥(runConstSpace S ⊓ LinearMap.ker (syndromeMap h)) := by
    let e : LinearMap.ker g ≃ₗ[ZMod 2] ↥(runConstSpace S ⊓ LinearMap.ker (syndromeMap h)) :=
      { toFun := fun x =>
          ⟨x.1.1,
           ⟨by
              have hmem : x.1.1 ∈ allowedSpace S ⊓ LinearMap.ker (projAll S) := ⟨x.1.2.1.1, x.2⟩
              rwa [ker_projAll_inf_allowed hn S] at hmem,
            x.1.2.1.2⟩⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        invFun := fun y =>
          have hmem : y.1 ∈ allowedSpace S ⊓ LinearMap.ker (projAll S) := by
            rw [ker_projAll_inf_allowed hn S]
            exact y.2.1
          ⟨⟨y.1, ⟨⟨hmem.1, y.2.2⟩, by
              change projAll S y.1 ∈ Submodule.pi Set.univ Q
              rw [LinearMap.mem_ker.mp hmem.2]
              exact Submodule.zero_mem _⟩⟩, hmem.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact e.finrank_eq
  rw [hrange, finrank_pi_submodule, hker_eq, (finrank_K0 hn h S hSne hSnu hSurj).1] at hrk
  omega

private lemma liftTuple_map_projOne {n m : ℕ} (hn : 3 ≤ n) (h : Fin n → Fin m → ZMod 2)
    (S : Finset (Fin n))
    (hSurj : ∀ z : Fin m → ZMod 2, ∃ x ∈ runConstSpace S, syndromeMap h x = z)
    (Q : ∀ i : ↥(exitsFn S), Submodule (ZMod 2) (Fin (gapFn S i.1 - 2) → ZMod 2))
    (i : ↥(exitsFn S)) :
    (liftTuple h S Q).map (projOne S i.1) = Q i := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hx.2 i trivial
  · intro v hv
    let q : ∀ j : ↥(exitsFn S), Fin (gapFn S j.1 - 2) → ZMod 2 := fun j =>
      if hj : j = i then hj ▸ v else 0
    have hq : q ∈ Submodule.pi Set.univ Q := by
      intro j _
      by_cases hj : j = i
      · subst hj
        simpa [q] using hv
      · simp [q, hj]
    rw [← liftTuple_map_projAll hn h S hSurj Q] at hq
    rcases hq with ⟨x, hx, hxq⟩
    refine ⟨x, hx, ?_⟩
    have := congrFun hxq i
    simpa [q, projAll, projOne] using this

lemma main_cycle_host_count {n m : ℕ} (hn : 3 ≤ n) (h : Fin n → Fin m → ZMod 2)
    {U : Submodule (ZMod 2) (Fin n → ZMod 2)} (hU : goodSpace h U)
    (hSne : (suppFn U).Nonempty) (hSnu : suppFn U ≠ Finset.univ)
    (hSurj : ∀ z : Fin m → ZMod 2, ∃ x ∈ runConstSpace (suppFn U), syndromeMap h x = z)
    (hostsSet : Finset (Submodule (ZMod 2) (Fin n → ZMod 2)))
    (hhosts : ∀ E, E ∈ hostsSet ↔ goodSpace h E ∧ U ≤ E)
    [DecidablePred (fun E : Submodule (ZMod 2) (Fin n → ZMod 2) =>
      Module.finrank (ZMod 2) E = hostsSet.sup (fun E => Module.finrank (ZMod 2) E))] :
    hostsSet.sup (fun E => Module.finrank (ZMod 2) E) =
      (exitsFn (suppFn U)).card - m +
        ∑ i ∈ exitsFn (suppFn U), ((gapFn (suppFn U) i - 2) + 1) / 2 ∧
    (hostsSet.filter (fun E : Submodule (ZMod 2) (Fin n → ZMod 2) =>
      Module.finrank (ZMod 2) E = hostsSet.sup (fun E => Module.finrank (ZMod 2) E))).card =
      ∏ i ∈ exitsFn (suppFn U),
        (if (gapFn (suppFn U) i - 2) % 2 = 0 then (gapFn (suppFn U) i - 2) + 1 else 1) := by
  classical
  set S := suppFn U
  set D := (exitsFn S).card - m + ∑ i ∈ exitsFn S, ((gapFn S i - 2) + 1) / 2
  have hle_D : ∀ E ∈ hostsSet, Module.finrank (ZMod 2) E ≤ D := by
    intro E hE_mem
    obtain ⟨hEgood, hUE⟩ := (hhosts E).mp hE_mem
    let Q : ∀ i : ↥(exitsFn S), Submodule (ZMod 2) (Fin (gapFn S i.1 - 2) → ZMod 2) :=
      fun i => E.map (projOne S i.1)
    have hE_le : E ≤ liftTuple h S Q := by
      intro x hxE
      refine ⟨⟨host_le_allowedSpace hn h hUE hEgood hSne hSnu hxE, ?_⟩, ?_⟩
      · change syndromeMap h x = 0
        funext b
        exact hEgood.1 x hxE b
      · intro i _
        exact ⟨x, hxE, rfl⟩
    have hfr1 := Submodule.finrank_mono hE_le
    rw [finrank_liftTuple hn h S hSne hSnu hSurj Q] at hfr1
    have hsum_le : ∑ i : ↥(exitsFn S), Module.finrank (ZMod 2) (Q i) ≤
        ∑ i ∈ exitsFn S, ((gapFn S i - 2) + 1) / 2 := by
      rw [← Finset.sum_coe_sort (exitsFn S)]
      refine Finset.sum_le_sum fun i _ => ?_
      exact finrank_pathGood_le (Q i) (host_projOne_pathGood h S hEgood i.1)
    omega
  have hex_D : ∃ E ∈ hostsSet, Module.finrank (ZMod 2) E = D := by
    let Q : ∀ i : ↥(exitsFn S), Submodule (ZMod 2) (Fin (gapFn S i.1 - 2) → ZMod 2) :=
      fun i => (pathGood_max_exists (gapFn S i.1 - 2)).choose
    have hQgood : ∀ i, pathGood (Q i) := fun i =>
      (pathGood_max_exists (gapFn S i.1 - 2)).choose_spec.1
    have hQfr : ∀ i, Module.finrank (ZMod 2) (Q i) = ((gapFn S i.1 - 2) + 1) / 2 := fun i =>
      (pathGood_max_exists (gapFn S i.1 - 2)).choose_spec.2
    refine ⟨liftTuple h S Q, ?_, ?_⟩
    · exact (hhosts _).mpr ⟨liftTuple_good hn h S Q hQgood, le_liftTuple_of_U hn h hU hSne hSnu Q⟩
    · rw [finrank_liftTuple hn h S hSne hSnu hSurj Q]
      congr 1
      rw [← Finset.sum_coe_sort (exitsFn S)]
      exact Finset.sum_congr rfl fun i _ => hQfr i
  have htop : hostsSet.sup (fun E => Module.finrank (ZMod 2) E) = D := by
    apply le_antisymm
    · exact Finset.sup_le hle_D
    · rcases hex_D with ⟨E, hE, hEfr⟩
      rw [← hEfr]
      exact Finset.le_sup (f := fun E : Submodule (ZMod 2) (Fin n → ZMod 2) => Module.finrank (ZMod 2) E) hE
  refine ⟨htop, ?_⟩
  let _ : ∀ l : ℕ, Fintype (Submodule (ZMod 2) (Fin l → ZMod 2)) := fun _ => Fintype.ofFinite _
  let M : ∀ i : ↥(exitsFn S), Finset (Submodule (ZMod 2) (Fin (gapFn S i.1 - 2) → ZMod 2)) :=
    fun i => (Finset.univ : Finset (Submodule (ZMod 2) (Fin (gapFn S i.1 - 2) → ZMod 2))).filter
      (fun Q => pathGood Q ∧ Module.finrank (ZMod 2) Q = ((gapFn S i.1 - 2) + 1) / 2)
  have hbij : (hostsSet.filter (fun E : Submodule (ZMod 2) (Fin n → ZMod 2) =>
        Module.finrank (ZMod 2) E = hostsSet.sup (fun E => Module.finrank (ZMod 2) E))).card =
      (Fintype.piFinset M).card := by
    symm
    refine Finset.card_bij (fun Q _ => liftTuple h S Q) ?_ ?_ ?_
    · intro Q hQ
      rw [Fintype.mem_piFinset] at hQ
      have hQgood : ∀ i, pathGood (Q i) := fun i => (Finset.mem_filter.mp (hQ i)).2.1
      have hQfr : ∀ i, Module.finrank (ZMod 2) (Q i) = ((gapFn S i.1 - 2) + 1) / 2 :=
        fun i => (Finset.mem_filter.mp (hQ i)).2.2
      rw [Finset.mem_filter, htop]
      refine ⟨(hhosts _).mpr ⟨liftTuple_good hn h S Q hQgood, le_liftTuple_of_U hn h hU hSne hSnu Q⟩, ?_⟩
      rw [finrank_liftTuple hn h S hSne hSnu hSurj Q]
      congr 1
      rw [← Finset.sum_coe_sort (exitsFn S)]
      exact Finset.sum_congr rfl fun i _ => hQfr i
    · intro Q₁ _ Q₂ _ heq
      funext i
      have hm := congrArg (fun E => E.map (projOne S i.1)) heq
      rwa [liftTuple_map_projOne hn h S hSurj Q₁ i,
           liftTuple_map_projOne hn h S hSurj Q₂ i] at hm
    · intro E hE
      rw [Finset.mem_filter, htop] at hE
      rcases hE with ⟨hE_mem, hEfr⟩
      obtain ⟨hEgood, hUE⟩ := (hhosts E).mp hE_mem
      let Q : ∀ i : ↥(exitsFn S), Submodule (ZMod 2) (Fin (gapFn S i.1 - 2) → ZMod 2) :=
        fun i => E.map (projOne S i.1)
      have hE_le : E ≤ liftTuple h S Q := by
        intro x hxE
        refine ⟨⟨host_le_allowedSpace hn h hUE hEgood hSne hSnu hxE, ?_⟩, ?_⟩
        · change syndromeMap h x = 0
          funext b
          exact hEgood.1 x hxE b
        · intro i _
          exact ⟨x, hxE, rfl⟩
      have hQgood : ∀ i, pathGood (Q i) := fun i => host_projOne_pathGood h S hEgood i.1
      have hQle : ∀ i, Module.finrank (ZMod 2) (Q i) ≤ ((gapFn S i.1 - 2) + 1) / 2 :=
        fun i => finrank_pathGood_le (Q i) (hQgood i)
      have hfr_le : D ≤ (exitsFn S).card - m + ∑ i : ↥(exitsFn S), Module.finrank (ZMod 2) (Q i) := by
        rw [← hEfr, ← finrank_liftTuple hn h S hSne hSnu hSurj Q]
        exact Submodule.finrank_mono hE_le
      have hD : D = (exitsFn S).card - m + ∑ i : ↥(exitsFn S), ((gapFn S i.1 - 2) + 1) / 2 := by
        dsimp only [D]
        congr 1
        exact (Finset.sum_coe_sort (exitsFn S) (fun i => ((gapFn S i - 2) + 1) / 2)).symm
      have hsum_eq : ∑ i : ↥(exitsFn S), Module.finrank (ZMod 2) (Q i) =
          ∑ i : ↥(exitsFn S), ((gapFn S i.1 - 2) + 1) / 2 := by
        apply le_antisymm
        · exact Finset.sum_le_sum fun i _ => hQle i
        · omega
      have hQfr : ∀ i : ↥(exitsFn S), Module.finrank (ZMod 2) (Q i) = ((gapFn S i.1 - 2) + 1) / 2 := by
        intro i
        have := Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
          (f := fun j : ↥(exitsFn S) => Module.finrank (ZMod 2) (Q j))
          (g := fun j : ↥(exitsFn S) => ((gapFn S j.1 - 2) + 1) / 2)
          (fun j _ => hQle j)
        exact this.mp hsum_eq i (Finset.mem_univ i)
      have hQmem : Q ∈ Fintype.piFinset M := by
        rw [Fintype.mem_piFinset]
        intro i
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQgood i, hQfr i⟩
      have hfr_eq : Module.finrank (ZMod 2) E = Module.finrank (ZMod 2) (liftTuple h S Q) := by
        rw [hEfr, finrank_liftTuple hn h S hSne hSnu hSurj Q, hD]
        congr 1
        exact Finset.sum_congr rfl fun i _ => (hQfr i).symm
      exact ⟨Q, hQmem, (Submodule.eq_of_le_of_finrank_eq hE_le hfr_eq).symm⟩
  rw [hbij, Fintype.card_piFinset, ← Finset.prod_coe_sort (exitsFn S)]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hc := card_pathGood_max (gapFn S i.1 - 2)
  convert hc using 1
  · congr 1
    ext Q
    simp only [M, Finset.mem_filter, Finset.mem_univ, true_and]
  · split_ifs <;> rfl

end PEqualNP.Outside.L_lib_951

theorem PEqualNP.Outside.L_lib_951 : (∀ (n m : ℕ), 3 ≤ n → ∀ h : Fin n → Fin m → ZMod 2,
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let W := Fin n → F
  letI : Fintype (Submodule F W) := Fintype.ofFinite _
  let next := fun i : Fin n =>
    (⟨(i.val+1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
  let good := fun U : Submodule F W =>
    (∀ x ∈ U, ∀ b : Fin m, (∑ i, h i b * x i) = 0) ∧
    (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
  let supp := fun U : Submodule F W =>
    Finset.univ.filter (fun i : Fin n => ∃ x ∈ U, x i ≠ 0)
  let spaces := (Finset.univ : Finset (Submodule F W)).filter good
  let move := fun (i : Fin n) (v : ℕ) =>
    (⟨(i.val+v) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
  let exits := fun S : Finset (Fin n) => S.filter (fun i => next i ∉ S)
  let gap := fun (S : Finset (Fin n)) (i : Fin n) =>
    ((Finset.range n).filter (fun k => ∀ j : Fin (k+1), move i (j.val+1) ∉ S)).card
  let factor := fun g : ℕ => if (g-2) % 2 = 0 then (g-2)+1 else 1
  let hosts := fun U : Submodule F W => spaces.filter (fun E => U ≤ E)
  let topDim := fun U : Submodule F W => (hosts U).sup (fun E => Module.finrank F E)
  let countTop := fun U : Submodule F W =>
    ((hosts U).filter (fun E : Submodule F W => Module.finrank F E = topDim U)).card
  ∀ U ∈ spaces, let S := supp U
    S.Nonempty → S ≠ Finset.univ →
    (∀ z : Fin m → F, ∃ x : W, (∀ i, i ∉ S → x i = 0) ∧
      (∀ i ∈ S, next i ∈ S → x i = x (next i)) ∧
      (∀ b, (∑ i, h i b * x i) = z b)) →
    topDim U = (exits S).card - m + ∑ i ∈ exits S, ((gap S i - 2)+1)/2 ∧
      countTop U = ∏ i ∈ exits S, factor (gap S i)) := by
  intro n m hn h F W next good supp spaces move exits gap factor hosts topDim countTop U hU S hSne hSnu hSurj
  have hS_eq : S = PEqualNP.Outside.L_lib_951.suppFn U := by
    ext i
    simp only [S, supp, PEqualNP.Outside.L_lib_951.suppFn, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  have hUgood : PEqualNP.Outside.L_lib_951.goodSpace h U := by
    simp only [spaces, Finset.mem_filter, Finset.mem_univ, true_and] at hU
    exact hU
  have hSne' : (PEqualNP.Outside.L_lib_951.suppFn U).Nonempty := hS_eq ▸ hSne
  have hSnu' : PEqualNP.Outside.L_lib_951.suppFn U ≠ Finset.univ := hS_eq ▸ hSnu
  have hSurj' : ∀ z : Fin m → ZMod 2,
      ∃ x ∈ PEqualNP.Outside.L_lib_951.runConstSpace (PEqualNP.Outside.L_lib_951.suppFn U),
        PEqualNP.Outside.L_lib_951.syndromeMap h x = z := by
    intro z
    rcases hSurj z with ⟨x, hx1, hx2, hx3⟩
    refine ⟨x, ⟨?_, ?_⟩, funext hx3⟩
    · intro i hi
      exact hx1 i (hS_eq ▸ hi)
    · intro i hi hni
      exact hx2 i (hS_eq ▸ hi) (hS_eq ▸ hni)
  have hhosts : ∀ E, E ∈ hosts U ↔ PEqualNP.Outside.L_lib_951.goodSpace h E ∧ U ≤ E := by
    intro E
    simp only [hosts, spaces, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  have hmain := PEqualNP.Outside.L_lib_951.main_cycle_host_count hn h hUgood hSne' hSnu' hSurj'
    (hosts U) hhosts
  have hexits : exits S = PEqualNP.Outside.L_lib_951.exitsFn (PEqualNP.Outside.L_lib_951.suppFn U) := by
    rw [hS_eq]
    ext i
    simp only [exits, PEqualNP.Outside.L_lib_951.exitsFn, Finset.mem_filter]
    rfl
  have hgap : ∀ i, gap S i = PEqualNP.Outside.L_lib_951.gapFn (PEqualNP.Outside.L_lib_951.suppFn U) i := by
    intro i
    rw [hS_eq]
    dsimp only [gap, PEqualNP.Outside.L_lib_951.gapFn]
    congr 1
    ext k
    simp only [Finset.mem_filter]
    rfl
  have hfactor : ∀ g, factor g = if (g - 2) % 2 = 0 then (g - 2) + 1 else 1 := by
    intro g
    dsimp only [factor]
    split_ifs <;> rfl
  refine ⟨?_, ?_⟩
  · change (hosts U).sup (fun E => Module.finrank (ZMod 2) E) = _
    rw [hmain.1, hexits]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hgap i]
  · dsimp only [countTop]
    trans ((hosts U).filter (fun E : Submodule (ZMod 2) (Fin n → ZMod 2) =>
        Module.finrank (ZMod 2) E = (hosts U).sup (fun E => Module.finrank (ZMod 2) E))).card
    · congr 1
      ext E
      simp only [Finset.mem_filter]
      rfl
    · rw [hmain.2, hexits]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hgap i, hfactor]
