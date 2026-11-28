import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_952

private def nextC (n : ℕ) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

private def moveC (n : ℕ) (i : Fin n) (v : ℕ) : Fin n :=
  ⟨(i.val + v) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

private def prevC (n : ℕ) (i : Fin n) : Fin n :=
  ⟨(i.val + n - 1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

private def hMat (n : ℕ) (i : Fin n) (b : Fin 4) : ZMod 2 :=
  if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2)
  then (1 : ZMod 2) else 0

private def goodSub (n : ℕ) (U : Submodule (ZMod 2) (Fin n → ZMod 2)) : Prop :=
  (∀ x ∈ U, ∀ b : Fin 4, (∑ i : Fin n, hMat n i b * x i) = 0) ∧
  (∀ x ∈ U, ∀ y ∈ U, ∀ i : Fin n, x i * y (nextC n i) = x (nextC n i) * y i)

private noncomputable def suppSub (n : ℕ) (U : Submodule (ZMod 2) (Fin n → ZMod 2)) : Finset (Fin n) :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  Finset.univ.filter (fun i : Fin n => ∃ x ∈ U, x i ≠ 0)

private lemma mem_suppSub {n : ℕ} {U : Submodule (ZMod 2) (Fin n → ZMod 2)} {i : Fin n} :
    i ∈ suppSub n U ↔ ∃ x ∈ U, x i ≠ 0 := by
  dsimp only [suppSub]; simp

private def exitsS (n : ℕ) (S : Finset (Fin n)) : Finset (Fin n) :=
  S.filter (fun i => nextC n i ∉ S)

private def gapS (n : ℕ) (S : Finset (Fin n)) (i : Fin n) : ℕ :=
  ((Finset.range n).filter (fun k => ∀ j : Fin (k + 1), moveC n i (j.val + 1) ∉ S)).card

private def factorG (g : ℕ) : ℕ :=
  if (g - 2) % 2 = 0 then (g - 2) + 1 else 1

private lemma moveC_zero (n : ℕ) (i : Fin n) : moveC n i 0 = i := by
  ext; simp [moveC, Nat.mod_eq_of_lt i.isLt]

private lemma moveC_one (n : ℕ) (i : Fin n) : moveC n i 1 = nextC n i := rfl

private lemma moveC_add (n : ℕ) (i : Fin n) (a b : ℕ) :
    moveC n (moveC n i a) b = moveC n i (a + b) := by
  ext; simp only [moveC]; rw [Nat.mod_add_mod, Nat.add_assoc]

private lemma moveC_self (n : ℕ) (i : Fin n) : moveC n i n = i := by
  ext; simp [moveC, Nat.mod_eq_of_lt i.isLt]

private lemma nextC_prevC (n : ℕ) (i : Fin n) : nextC n (prevC n i) = i := by
  ext
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have h1 : (i.val + n - 1) % n + 1 ≡ i.val [MOD n] := by
    change ((i.val + n - 1) % n + 1) % n = i.val % n
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have hge : 1 ≤ i.val + n := by omega
    rw [Nat.sub_add_cancel hge, Nat.add_mod_right]
  simpa [nextC, prevC, Nat.ModEq, Nat.mod_eq_of_lt i.isLt] using h1

private lemma prevC_nextC (n : ℕ) (i : Fin n) : prevC n (nextC n i) = i := by
  ext
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  simp only [prevC, nextC]
  by_cases h : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt h, show i.val + 1 + n - 1 = i.val + n by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
  · have hi : i.val + 1 = n := by omega
    rw [hi, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (by omega)]
    omega

private lemma nextC_injective (n : ℕ) : Function.Injective (nextC n) := by
  intro a b h
  have := congrArg (prevC n) h
  rwa [prevC_nextC, prevC_nextC] at this

private lemma nextC_bijective (n : ℕ) : Function.Bijective (nextC n) :=
  Finite.injective_iff_bijective.mp (nextC_injective n)

private lemma moveC_injective_lt (n : ℕ) (i : Fin n) {a b : ℕ} (ha : a < n) (hb : b < n)
    (h : moveC n i a = moveC n i b) : a = b := by
  have hv : (i.val + a) % n = (i.val + b) % n := congrArg Fin.val h
  have hlt := i.isLt
  by_cases ha1 : i.val + a < n <;> by_cases hb1 : i.val + b < n
  · rw [Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt hb1] at hv; omega
  · have hb2 : i.val + b - n < n := by omega
    have hmb : (i.val + b) % n = i.val + b - n := by
      calc (i.val + b) % n = ((i.val + b - n) + n) % n := by congr 1; omega
        _ = (i.val + b - n) % n := Nat.add_mod_right _ _
        _ = i.val + b - n := Nat.mod_eq_of_lt hb2
    rw [Nat.mod_eq_of_lt ha1, hmb] at hv; omega
  · have ha2 : i.val + a - n < n := by omega
    have hma : (i.val + a) % n = i.val + a - n := by
      calc (i.val + a) % n = ((i.val + a - n) + n) % n := by congr 1; omega
        _ = (i.val + a - n) % n := Nat.add_mod_right _ _
        _ = i.val + a - n := Nat.mod_eq_of_lt ha2
    rw [Nat.mod_eq_of_lt hb1, hma] at hv; omega
  · have ha2 : i.val + a - n < n := by omega
    have hb2 : i.val + b - n < n := by omega
    have hma : (i.val + a) % n = i.val + a - n := by
      calc (i.val + a) % n = ((i.val + a - n) + n) % n := by congr 1; omega
        _ = (i.val + a - n) % n := Nat.add_mod_right _ _
        _ = i.val + a - n := Nat.mod_eq_of_lt ha2
    have hmb : (i.val + b) % n = i.val + b - n := by
      calc (i.val + b) % n = ((i.val + b - n) + n) % n := by congr 1; omega
        _ = (i.val + b - n) % n := Nat.add_mod_right _ _
        _ = i.val + b - n := Nat.mod_eq_of_lt hb2
    rw [hma, hmb] at hv; omega

private lemma moveC_mod_sub (n : ℕ) (a x : Fin n) :
    moveC n a ((x.val + n - a.val) % n) = x := by
  ext; simp only [moveC]
  have ha := a.isLt; have hx := x.isLt
  by_cases hle : a.val ≤ x.val
  · have hd : (x.val + n - a.val) % n = x.val - a.val := by
      calc (x.val + n - a.val) % n = ((x.val - a.val) + n) % n := by congr 1; omega
        _ = (x.val - a.val) % n := Nat.add_mod_right _ _
        _ = x.val - a.val := Nat.mod_eq_of_lt (by omega)
    rw [hd, show a.val + (x.val - a.val) = x.val by omega, Nat.mod_eq_of_lt hx]
  · have hd : (x.val + n - a.val) % n = x.val + n - a.val := Nat.mod_eq_of_lt (by omega)
    rw [hd, show a.val + (x.val + n - a.val) = x.val + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hx]

private lemma mod_sub_moveC (n : ℕ) (a : Fin n) {k : ℕ} (hk : k < n) :
    ((moveC n a k).val + n - a.val) % n = k := by
  simp only [moveC]
  have ha := a.isLt
  by_cases h1 : a.val + k < n
  · rw [Nat.mod_eq_of_lt h1, show a.val + k + n - a.val = k + n by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hk]
  · have hm : (a.val + k) % n = a.val + k - n := by
      calc (a.val + k) % n = ((a.val + k - n) + n) % n := by congr 1; omega
        _ = (a.val + k - n) % n := Nat.add_mod_right _ _
        _ = a.val + k - n := Nat.mod_eq_of_lt (by omega)
    rw [hm, show a.val + k - n + n - a.val = k by omega, Nat.mod_eq_of_lt hk]

private lemma goodSub_adj_eq (n : ℕ) (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hU : goodSub n U) {i : Fin n} (hi : i ∈ suppSub n U) (hni : nextC n i ∈ suppSub n U) :
    ∀ x ∈ U, x i = x (nextC n i) := by
  classical
  have h1 : ∃ x ∈ U, x i ≠ 0 := by simpa [suppSub] using hi
  have h2 : ∃ y ∈ U, y (nextC n i) ≠ 0 := by simpa [suppSub] using hni
  rcases h1 with ⟨x0, hx0, hxi⟩
  rcases h2 with ⟨y0, hy0, hyni⟩
  have hz2 : ∀ z : ZMod 2, z ≠ 0 → z = 1 := fun z hz => by fin_cases z <;> first | exact absurd rfl hz | rfl
  have hxi1 : x0 i = 1 := hz2 _ hxi
  have hyni1 : y0 (nextC n i) = 1 := hz2 _ hyni
  have hrel := hU.2 x0 hx0 y0 hy0 i
  rw [hxi1, hyni1, one_mul] at hrel
  have hxni1 : x0 (nextC n i) = 1 := by
    by_contra hne
    have h0 : x0 (nextC n i) = 0 := by
      have := hz2 (x0 (nextC n i))
      by_cases hz : x0 (nextC n i) = 0
      · exact hz
      · exact (hne (this hz)).elim
    rw [h0, zero_mul] at hrel
    exact one_ne_zero hrel
  intro x hx
  have hrx := hU.2 x0 hx0 x hx i
  rw [hxi1, hxni1, one_mul, one_mul] at hrx
  exact hrx.symm

private lemma goodSub_of_adj_eq (n : ℕ) (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hH : ∀ x ∈ U, ∀ b : Fin 4, (∑ i : Fin n, hMat n i b * x i) = 0)
    (hadj : ∀ i : Fin n, i ∈ suppSub n U → nextC n i ∈ suppSub n U → ∀ x ∈ U, x i = x (nextC n i)) :
    goodSub n U := by
  classical
  refine ⟨hH, fun x hx y hy i => ?_⟩
  by_cases h1 : i ∈ suppSub n U
  · by_cases h2 : nextC n i ∈ suppSub n U
    · rw [hadj i h1 h2 x hx, hadj i h1 h2 y hy]
    · have hxn : x (nextC n i) = 0 := by
        by_contra hne; exact h2 (by simpa [suppSub] using ⟨x, hx, hne⟩)
      have hyn : y (nextC n i) = 0 := by
        by_contra hne; exact h2 (by simpa [suppSub] using ⟨y, hy, hne⟩)
      rw [hxn, hyn, mul_zero, zero_mul]
  · have hxi : x i = 0 := by
      by_contra hne; exact h1 (by simpa [suppSub] using ⟨x, hx, hne⟩)
    have hyi : y i = 0 := by
      by_contra hne; exact h1 (by simpa [suppSub] using ⟨y, hy, hne⟩)
    rw [hxi, hyi, zero_mul, mul_zero]

private lemma suppSub_ne_univ_of_finrank (n : ℕ) (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hU : goodSub n U) (hd : 2 ≤ Module.finrank (ZMod 2) U) : suppSub n U ≠ Finset.univ := by
  intro huniv
  have hn : 0 < n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    haveI : Fintype U := Fintype.ofFinite U
    have hcard : Fintype.card U = 1 := by
      have hle := Fintype.card_le_of_injective (Subtype.val : U → Fin 0 → ZMod 2) Subtype.val_injective
      have hc0 : Fintype.card (Fin 0 → ZMod 2) = 1 := by simp
      have hpos : 0 < Fintype.card U := Fintype.card_pos
      omega
    have hfr : Module.finrank (ZMod 2) U = 0 := by
      have := Module.card_eq_pow_finrank (K := ZMod 2) (V := U)
      rw [hcard, ZMod.card] at this
      by_contra hne
      have : 2 ≤ 2 ^ Module.finrank (ZMod 2) U := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ Module.finrank (ZMod 2) U := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    omega
  have hconst : ∀ x ∈ U, ∀ i : Fin n, x i = x ⟨0, hn⟩ := by
    intro x hx i
    have hstep : ∀ k : ℕ, x (moveC n ⟨0, hn⟩ k) = x ⟨0, hn⟩ := by
      intro k
      induction k with
      | zero => rw [moveC_zero]
      | succ k ih =>
        have hadj := goodSub_adj_eq n U hU (i := moveC n ⟨0, hn⟩ k)
          (by rw [huniv]; exact Finset.mem_univ _) (by rw [huniv]; exact Finset.mem_univ _) x hx
        rw [← moveC_one, moveC_add] at hadj
        rw [← hadj, ih]
    have hi_eq : moveC n ⟨0, hn⟩ i.val = i := by ext; simp [moveC, Nat.mod_eq_of_lt i.isLt]
    rw [← hi_eq, hstep i.val]
  let ev0 : U →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun x => x.1 ⟨0, hn⟩
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have hinj : Function.Injective ev0 := by
    intro x y hxy
    apply Subtype.ext; funext i
    rw [hconst x.1 x.2 i, hconst y.1 y.2 i]; exact hxy
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_self] at hle
  omega

private lemma suppSub_nonempty_of_finrank (n : ℕ) (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hd : 1 ≤ Module.finrank (ZMod 2) U) : (suppSub n U).Nonempty := by
  classical
  have hne : U ≠ ⊥ := by
    intro hb; rw [hb, finrank_bot] at hd; omega
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hne with ⟨x, hxU, hx0⟩
  have hex : ∃ i : Fin n, x i ≠ 0 := by
    by_contra hall; push_neg at hall; exact hx0 (funext hall)
  rcases hex with ⟨i, hi⟩
  exact ⟨i, by simpa [suppSub] using ⟨x, hxU, hi⟩⟩

private lemma exists_not_mem_moveC (n : ℕ) (S : Finset (Fin n)) (hne : S ≠ Finset.univ) (i : Fin n) :
    ∃ k < n, moveC n i (k + 1) ∉ S := by
  have hcompl : ∃ j : Fin n, j ∉ S := by
    by_contra hall; push_neg at hall; exact hne (Finset.eq_univ_iff_forall.mpr hall)
  rcases hcompl with ⟨j, hj⟩
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  let d := (j.val + n - i.val - 1) % n
  by_cases hij : i = j
  · refine ⟨n - 1, by omega, ?_⟩
    have hm : moveC n i (n - 1 + 1) = j := by
      rw [Nat.sub_add_cancel hn, moveC_self, hij]
    rwa [hm]
  · have hstep : ∃ m < n, moveC n i m = j ∧ 0 < m := by
      by_cases hlt : i.val < j.val
      · refine ⟨j.val - i.val, by omega, ?_, by omega⟩
        ext; simp [moveC, Nat.add_sub_cancel' (le_of_lt hlt), Nat.mod_eq_of_lt j.isLt]
      · have hgt : j.val < i.val := lt_of_le_of_ne (not_lt.mp hlt) (fun he => hij (Fin.ext he.symm))
        refine ⟨j.val + n - i.val, by omega, ?_, by omega⟩
        ext; simp only [moveC]
        rw [show i.val + (j.val + n - i.val) = j.val + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
    rcases hstep with ⟨m, hm, hmeq, hm0⟩
    refine ⟨m - 1, by omega, ?_⟩
    rw [Nat.sub_add_cancel hm0, hmeq]; exact hj

private noncomputable def runDist (n : ℕ) (S : Finset (Fin n)) (hne : S ≠ Finset.univ) (i : Fin n) : ℕ :=
  Nat.find (exists_not_mem_moveC n S hne i)

private noncomputable def runExit (n : ℕ) (S : Finset (Fin n)) (hne : S ≠ Finset.univ) (i : Fin n) : Fin n :=
  moveC n i (runDist n S hne i)

private lemma runDist_lt (n : ℕ) (S : Finset (Fin n)) (hne : S ≠ Finset.univ) (i : Fin n) :
    runDist n S hne i < n :=
  (Nat.find_spec (exists_not_mem_moveC n S hne i)).1

private lemma runExit_next_not_mem (n : ℕ) (S : Finset (Fin n)) (hne : S ≠ Finset.univ) (i : Fin n) :
    nextC n (runExit n S hne i) ∉ S := by
  have hspec := (Nat.find_spec (exists_not_mem_moveC n S hne i)).2
  simpa [runExit, runDist, ← moveC_one, moveC_add] using hspec

private lemma runDist_mem_prefix (n : ℕ) (S : Finset (Fin n)) (hne : S ≠ Finset.univ) (i : Fin n)
    (hi : i ∈ S) : ∀ m ≤ runDist n S hne i, moveC n i m ∈ S := by
  intro m hm
  cases m with
  | zero => rwa [moveC_zero]
  | succ k =>
    by_contra hnot
    have hklt : k < runDist n S hne i := by omega
    have hlt_n : k < n := lt_trans hklt (runDist_lt n S hne i)
    exact Nat.find_min (exists_not_mem_moveC n S hne i) hklt ⟨hlt_n, hnot⟩

private lemma runExit_mem_exits (n : ℕ) (S : Finset (Fin n)) (hne : S ≠ Finset.univ) {i : Fin n}
    (hi : i ∈ S) : runExit n S hne i ∈ exitsS n S :=
  Finset.mem_filter.mpr ⟨runDist_mem_prefix n S hne i hi _ le_rfl, runExit_next_not_mem n S hne i⟩

private lemma runExit_of_exit (n : ℕ) (S : Finset (Fin n)) (hne : S ≠ Finset.univ) {a : Fin n}
    (ha : a ∈ exitsS n S) : runExit n S hne a = a := by
  have h0 : runDist n S hne a = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply Nat.find_le
    refine ⟨Nat.lt_of_le_of_lt (Nat.zero_le _) a.isLt, ?_⟩
    simpa [moveC_one] using (Finset.mem_filter.mp ha).2
  simp [runExit, h0, moveC_zero]

private lemma runExit_next_eq (n : ℕ) (S : Finset (Fin n)) (hne : S ≠ Finset.univ) {i : Fin n}
    (hni : nextC n i ∈ S) : runExit n S hne (nextC n i) = runExit n S hne i := by
  have hpos : 0 < runDist n S hne i := by
    by_contra h0
    have h0' : runDist n S hne i = 0 := by omega
    have hspec := runExit_next_not_mem n S hne i
    simp [runExit, h0', moveC_zero] at hspec
    exact hspec hni
  have hdist : runDist n S hne (nextC n i) = runDist n S hne i - 1 := by
    apply le_antisymm
    · apply Nat.find_le
      refine ⟨by have := runDist_lt n S hne i; omega, ?_⟩
      have hspec := (Nat.find_spec (exists_not_mem_moveC n S hne i)).2
      rw [← moveC_one, moveC_add, show 1 + (runDist n S hne i - 1 + 1) = runDist n S hne i + 1 by omega]
      exact hspec
    · by_contra hlt
      push_neg at hlt
      have hspec := Nat.find_spec (exists_not_mem_moveC n S hne (nextC n i))
      have hlt_i : runDist n S hne (nextC n i) + 1 < runDist n S hne i := by omega
      have hlt_n : runDist n S hne (nextC n i) + 1 < n := lt_trans hlt_i (runDist_lt n S hne i)
      refine Nat.find_min (exists_not_mem_moveC n S hne i) hlt_i ⟨hlt_n, ?_⟩
      have h2 := hspec.2
      rw [← moveC_one, moveC_add] at h2
      rwa [show runDist n S hne (nextC n i) + 1 + 1 = 1 + (runDist n S hne (nextC n i) + 1) by omega]
  rw [runExit, runExit, hdist, ← moveC_one, moveC_add, show 1 + (runDist n S hne i - 1) = runDist n S hne i by omega]

private lemma const_on_run_eq_runExit (n : ℕ) (S : Finset (Fin n)) (hne : S ≠ Finset.univ)
    (x : Fin n → ZMod 2) (hadj : ∀ i ∈ S, nextC n i ∈ S → x i = x (nextC n i))
    {i : Fin n} (hi : i ∈ S) : x i = x (runExit n S hne i) := by
  have hstep : ∀ k ≤ runDist n S hne i, x (moveC n i k) = x i := by
    intro k hk
    induction k with
    | zero => rw [moveC_zero]
    | succ k ih =>
      have hm1 : moveC n i k ∈ S := runDist_mem_prefix n S hne i hi k (by omega)
      have hm2 : nextC n (moveC n i k) ∈ S := by
        rw [← moveC_one, moveC_add]; exact runDist_mem_prefix n S hne i hi (k + 1) hk
      have heq := hadj _ hm1 hm2
      rw [← moveC_one, moveC_add] at heq
      rw [← heq, ih (by omega)]
  exact (hstep (runDist n S hne i) le_rfl).symm

private noncomputable def embedRuns (n : ℕ) (S : Finset (Fin n)) (hne : S ≠ Finset.univ) :
    (exitsS n S → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
  { toFun := fun c i => if h : i ∈ S then c ⟨runExit n S hne i, runExit_mem_exits n S hne h⟩ else 0
    map_add' := fun c1 c2 => by funext i; simp only [Pi.add_apply]; split_ifs <;> simp
    map_smul' := fun r c => by funext i; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }

private lemma embedRuns_injective (n : ℕ) (S : Finset (Fin n)) (hne : S ≠ Finset.univ) :
    Function.Injective (embedRuns n S hne) := by
  intro c1 c2 heq
  funext ⟨a, ha⟩
  have h1 := congrFun heq a
  have haS : a ∈ S := (Finset.mem_filter.mp ha).1
  dsimp only [embedRuns, LinearMap.coe_mk, AddHom.coe_mk] at h1
  rw [dif_pos haS, dif_pos haS] at h1
  have hre : (⟨runExit n S hne a, runExit_mem_exits n S hne haS⟩ : exitsS n S) = ⟨a, ha⟩ :=
    Subtype.ext (runExit_of_exit n S hne ha)
  rwa [hre] at h1

private lemma mem_range_embedRuns_iff (n : ℕ) (S : Finset (Fin n)) (hne : S ≠ Finset.univ)
    (x : Fin n → ZMod 2) :
    x ∈ LinearMap.range (embedRuns n S hne) ↔
      (∀ i, i ∉ S → x i = 0) ∧ (∀ i ∈ S, nextC n i ∈ S → x i = x (nextC n i)) := by
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨fun i hi => by dsimp only [embedRuns, LinearMap.coe_mk, AddHom.coe_mk]; rw [dif_neg hi],
      fun i hi hni => ?_⟩
    dsimp only [embedRuns, LinearMap.coe_mk, AddHom.coe_mk]
    rw [dif_pos hi, dif_pos hni]
    congr 1; exact Subtype.ext (runExit_next_eq n S hne hni).symm
  · rintro ⟨hsupp, hadj⟩
    refine ⟨fun a => x a.1, ?_⟩
    funext i
    dsimp only [embedRuns, LinearMap.coe_mk, AddHom.coe_mk]
    by_cases hi : i ∈ S
    · rw [dif_pos hi]; exact (const_on_run_eq_runExit n S hne x hadj hi).symm
    · rw [dif_neg hi]; exact (hsupp i hi).symm

private def parityMap (n : ℕ) : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
  { toFun := fun x b => ∑ i : Fin n, hMat n i b * x i
    map_add' := fun x y => by funext b; simp [mul_add, Finset.sum_add_distrib]
    map_smul' := fun c x => by
      funext b; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring }

private noncomputable def runSig (n : ℕ) (S : Finset (Fin n)) (hne : S ≠ Finset.univ)
    (a : exitsS n S) (b : Fin 4) : ZMod 2 :=
  parityMap n (embedRuns n S hne (Pi.single a 1)) b

private lemma parityMap_embedRuns (n : ℕ) (S : Finset (Fin n)) (hne : S ≠ Finset.univ)
    (c : exitsS n S → ZMod 2) (b : Fin 4) :
    parityMap n (embedRuns n S hne c) b = ∑ a : exitsS n S, runSig n S hne a b * c a := by
  have hc : c = ∑ a : exitsS n S, c a • Pi.single a (1 : ZMod 2) := by
    funext a; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hc]
  rw [map_sum, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]; rfl

private lemma gapS_iff (n : ℕ) (S : Finset (Fin n)) {i : Fin n} (hi : i ∈ S) (g : ℕ) :
    gapS n S i = g ↔ g < n ∧ (∀ v < g, moveC n i (v + 1) ∉ S) ∧ moveC n i (g + 1) ∈ S := by
  have hex : ∃ k < n, moveC n i (k + 1) ∈ S := ⟨n - 1, by have := i.isLt; omega, by
    rw [Nat.sub_add_cancel (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt), moveC_self]; exact hi⟩
  let g0 := Nat.find hex
  have hg0_lt : g0 < n := (Nat.find_spec hex).1
  have hg0_mem : moveC n i (g0 + 1) ∈ S := (Nat.find_spec hex).2
  have hg0_not : ∀ v < g0, moveC n i (v + 1) ∉ S := fun v hv => fun hm =>
    Nat.find_min hex hv ⟨lt_trans hv hg0_lt, hm⟩
  have hfilt : (Finset.range n).filter (fun k => ∀ j : Fin (k + 1), moveC n i (j.val + 1) ∉ S) =
      Finset.range g0 := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, hk⟩
      by_contra hge; push_neg at hge
      exact hk ⟨g0, by omega⟩ hg0_mem
    · intro hk
      exact ⟨lt_trans hk hg0_lt, fun j => hg0_not j.val (by omega)⟩
  have hcard : gapS n S i = g0 := by
    dsimp only [gapS]; rw [hfilt, Finset.card_range]
  rw [hcard]
  constructor
  · rintro rfl; exact ⟨hg0_lt, hg0_not, hg0_mem⟩
  · rintro ⟨hg_lt, hg_not, hg_mem⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hg_not g0 hlt hg0_mem
    · exact hg0_not g hgt hg_mem

private lemma gapS_pos_of_exit (n : ℕ) (S : Finset (Fin n)) {a : Fin n} (ha : a ∈ exitsS n S) :
    1 ≤ gapS n S a := by
  have haS := (Finset.mem_filter.mp ha).1
  have hna := (Finset.mem_filter.mp ha).2
  have hspec := (gapS_iff n S haS (gapS n S a)).mp rfl
  by_contra h0
  have hg0 : gapS n S a = 0 := by omega
  have hm := hspec.2.2
  rw [hg0, zero_add, moveC_one] at hm
  exact hna hm

private def gapInt (n : ℕ) (S : Finset (Fin n)) (a : Fin n) : Finset (Fin n) :=
  (Finset.range (gapS n S a - 2)).image (fun k => moveC n a (k + 2))

private lemma gapInt_disjoint_S (n : ℕ) (S : Finset (Fin n)) {a : Fin n} (ha : a ∈ exitsS n S) :
    Disjoint (gapInt n S a) S := by
  rw [Finset.disjoint_left]
  intro x hx hxS
  rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
  have hkl : k < gapS n S a - 2 := Finset.mem_range.mp hk
  have hspec := (gapS_iff n S (Finset.mem_filter.mp ha).1 (gapS n S a)).mp rfl
  exact hspec.2.1 (k + 1) (by omega) hxS

private lemma gapInt_pairwise_disjoint (n : ℕ) (S : Finset (Fin n)) {a b : Fin n}
    (ha : a ∈ exitsS n S) (hb : b ∈ exitsS n S) (hab : a ≠ b) :
    Disjoint (gapInt n S a) (gapInt n S b) := by
  rw [Finset.disjoint_left]
  intro x hxa hxb
  rcases Finset.mem_image.mp hxa with ⟨ka, hka, rfl⟩
  rcases Finset.mem_image.mp hxb with ⟨kb, hkb, heq⟩
  have hka_lt : ka < gapS n S a - 2 := Finset.mem_range.mp hka
  have hkb_lt : kb < gapS n S b - 2 := Finset.mem_range.mp hkb
  have haS := (Finset.mem_filter.mp ha).1
  have hbS := (Finset.mem_filter.mp hb).1
  have hsa := (gapS_iff n S haS (gapS n S a)).mp rfl
  have hsb := (gapS_iff n S hbS (gapS n S b)).mp rfl
  by_cases hle : ka ≤ kb
  · have hmove : moveC n b (kb - ka) = a := by
      have h1 : moveC n (moveC n b (kb - ka)) (ka + 2) = moveC n a (ka + 2) := by
        rw [moveC_add, show kb - ka + (ka + 2) = kb + 2 by omega]; exact heq
      have h2 := congrArg (fun z => moveC n z (n - (ka + 2) % n)) h1
      have hlt : ka + 2 < n := by omega
      have hsub : moveC n (moveC n (moveC n b (kb - ka)) (ka + 2)) (n - (ka + 2)) =
          moveC n b (kb - ka) := by
        rw [moveC_add, Nat.add_sub_cancel' (le_of_lt hlt), moveC_self]
      have hsub2 : moveC n (moveC n a (ka + 2)) (n - (ka + 2)) = a := by
        rw [moveC_add, Nat.add_sub_cancel' (le_of_lt hlt), moveC_self]
      rw [Nat.mod_eq_of_lt hlt, hsub, hsub2] at h2; exact h2
    by_cases h0 : kb - ka = 0
    · rw [h0, moveC_zero] at hmove; exact hab hmove.symm
    · have hnot := hsb.2.1 (kb - ka - 1) (by omega)
      rw [show kb - ka - 1 + 1 = kb - ka by omega, hmove] at hnot
      exact hnot haS
  · have hlt' : kb < ka := not_le.mp hle
    have hmove : moveC n a (ka - kb) = b := by
      have h1 : moveC n (moveC n a (ka - kb)) (kb + 2) = moveC n b (kb + 2) := by
        rw [moveC_add, show ka - kb + (kb + 2) = ka + 2 by omega]; exact heq.symm
      have hlt : kb + 2 < n := by omega
      have h2 := congrArg (fun z => moveC n z (n - (kb + 2))) h1
      rw [moveC_add n (moveC n a (ka - kb)), moveC_add n b, Nat.add_sub_cancel' (le_of_lt hlt), moveC_self, moveC_self] at h2
      exact h2
    have hnot := hsa.2.1 (ka - kb - 1) (by omega)
    rw [show ka - kb - 1 + 1 = ka - kb by omega, hmove] at hnot
    exact hnot hbS

private lemma mem_gapInt_of_not_mem_and_not_adj (n : ℕ) (S : Finset (Fin n)) (hne_e : S.Nonempty)
    (hne_u : S ≠ Finset.univ) {x : Fin n} (hx : x ∉ S) (hprev : prevC n x ∉ S) (hnext : nextC n x ∉ S) :
    ∃ a ∈ exitsS n S, x ∈ gapInt n S a := by
  have hex : ∃ k < n, moveC n x (n - 1 - k) ∈ S := by
    rcases hne_e with ⟨y, hy⟩
    have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) x.isLt
    let d := (x.val + n - y.val) % n
    have hd_pos : 0 < d := by
      by_contra h0
      have hd0 : d = 0 := by omega
      have hxy : x = y := by
        ext; dsimp only [d] at hd0
        have hlt := x.isLt; have hlt2 := y.isLt
        by_cases h1 : y.val ≤ x.val
        · have : (x.val + n - y.val) % n = x.val - y.val := by
            rw [show x.val + n - y.val = (x.val - y.val) + n by omega, Nat.add_mod_right,
              Nat.mod_eq_of_lt (by omega)]
          omega
        · have : (x.val + n - y.val) % n = x.val + n - y.val := Nat.mod_eq_of_lt (by omega)
          omega
      exact hx (hxy ▸ hy)
    have hd_lt : d < n := Nat.mod_lt _ hn
    refine ⟨d - 1, by omega, ?_⟩
    have hm : moveC n x (n - 1 - (d - 1)) = y := by
      ext; simp only [moveC]
      have hsub : n - 1 - (d - 1) = n - d := by omega
      rw [hsub]
      have hlt := x.isLt; have hlt2 := y.isLt
      by_cases h1 : y.val ≤ x.val
      · have hd_eq : d = x.val - y.val := by
          dsimp only [d]
          rw [show x.val + n - y.val = (x.val - y.val) + n by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]
        rw [hd_eq, show x.val + (n - (x.val - y.val)) = y.val + n by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt hlt2]
      · have hd_eq : d = x.val + n - y.val := by
          dsimp only [d]; exact Nat.mod_eq_of_lt (by omega)
        rw [hd_eq, show x.val + (n - (x.val + n - y.val)) = y.val by omega, Nat.mod_eq_of_lt hlt2]
    rwa [hm]
  let k0 := Nat.find hex
  have hk0_lt : k0 < n := (Nat.find_spec hex).1
  have hk0_mem : moveC n x (n - 1 - k0) ∈ S := (Nat.find_spec hex).2
  let a := moveC n x (n - 1 - k0)
  have hdist : moveC n a (k0 + 1) = x := by
    dsimp only [a]; rw [moveC_add, show n - 1 - k0 + (k0 + 1) = n by omega, moveC_self]
  have hnot_between : ∀ j < k0 + 1, moveC n a (j + 1) ∉ S := by
    intro j hj
    by_cases hjk : j = k0
    · rw [hjk, hdist]; exact hx
    · intro hm
      have hlt' : k0 - 1 - j < k0 := by omega
      have hlt_n : k0 - 1 - j < n := lt_trans hlt' hk0_lt
      refine Nat.find_min hex hlt' ⟨hlt_n, ?_⟩
      have heq : moveC n x (n - 1 - (k0 - 1 - j)) = moveC n a (j + 1) := by
        dsimp only [a]; rw [moveC_add]
        congr 1; omega
      rwa [heq]
  have ha_exit : a ∈ exitsS n S := by
    refine Finset.mem_filter.mpr ⟨hk0_mem, ?_⟩
    rw [← moveC_one]; exact hnot_between 0 (by omega)
  have hk0_ge1 : 1 ≤ k0 := by
    by_contra h0
    have hk0' : k0 = 0 := by omega
    have ha_prev : a = prevC n x := by
      apply nextC_injective n
      rw [hk0', zero_add] at hdist
      rw [nextC_prevC, ← moveC_one, hdist]
    exact hprev (ha_prev ▸ hk0_mem)
  have hgap_ge : k0 + 2 ≤ gapS n S a := by
    have hspec := (gapS_iff n S hk0_mem (gapS n S a)).mp rfl
    by_contra hlt; push_neg at hlt
    have hmem_g := hspec.2.2
    by_cases h1 : gapS n S a ≤ k0
    · exact hnot_between (gapS n S a) (by omega) hmem_g
    · have hge : gapS n S a = k0 + 1 := by omega
      rw [hge, show k0 + 1 + 1 = (k0 + 1) + 1 by omega, ← moveC_add, hdist, moveC_one] at hmem_g
      exact hnext hmem_g
  refine ⟨a, ha_exit, Finset.mem_image.mpr ⟨k0 - 1, Finset.mem_range.mpr (by omega), ?_⟩⟩
  rw [show k0 - 1 + 2 = k0 + 1 by omega]; exact hdist

private def runsL (L : ℕ) (A : Finset (Fin L)) : ℕ :=
  (A.filter (fun i : Fin L => ∀ h : i.val + 1 < L, (⟨i.val + 1, h⟩ : Fin L) ∉ A)).card

private lemma runsL_le (L : ℕ) (A : Finset (Fin L)) : runsL L A ≤ (L + 1) / 2 := by
  let E := A.filter (fun i : Fin L => ∀ h : i.val + 1 < L, (⟨i.val + 1, h⟩ : Fin L) ∉ A)
  let E0 : Finset (Fin (L + 1)) := E.image (fun i => ⟨i.val, by omega⟩)
  let E1 : Finset (Fin (L + 1)) := E.image (fun i => ⟨i.val + 1, by omega⟩)
  have hdisj : Disjoint E0 E1 := by
    rw [Finset.disjoint_left]
    intro x hx0 hx1
    rcases Finset.mem_image.mp hx0 with ⟨i, hi, rfl⟩
    rcases Finset.mem_image.mp hx1 with ⟨j, hj, heq⟩
    have hv : j.val + 1 = i.val := congrArg Fin.val heq
    have hj_spec := (Finset.mem_filter.mp hj).2
    have hiA := (Finset.mem_filter.mp hi).1
    have hjl : j.val + 1 < L := by omega
    have : (⟨j.val + 1, hjl⟩ : Fin L) = i := Fin.ext hv
    exact hj_spec hjl (this ▸ hiA)
  have hc0 : E0.card = E.card := Finset.card_image_of_injective _ fun a b h => by
    have hv := congrArg Fin.val h; dsimp only at hv; exact Fin.ext hv
  have hc1 : E1.card = E.card := Finset.card_image_of_injective _ fun a b h => by
    have hv := congrArg Fin.val h; dsimp only at hv; exact Fin.ext (by omega)
  have hle : (E0 ∪ E1).card ≤ L + 1 := by
    have := Finset.card_le_univ (E0 ∪ E1); simpa using this
  rw [Finset.card_union_of_disjoint hdisj, hc0, hc1] at hle
  change E.card ≤ (L + 1) / 2; omega

set_option maxHeartbeats 800000 in
private lemma card_max_runsL : ∀ L : ℕ,
    ((Finset.univ : Finset (Finset (Fin L))).filter (fun A => runsL L A = (L + 1) / 2)).card =
      if L % 2 = 0 then L + 1 else 1 := by
  intro L
  induction L using Nat.strong_induction_on with
  | ind L ih =>
    match L with
    | 0 => decide
    | 1 => decide
    | L + 2 =>
      let All := (Finset.univ : Finset (Finset (Fin (L + 2)))).filter (fun A => runsL (L + 2) A = (L + 3) / 2)
      let i0 : Fin (L + 2) := ⟨0, by omega⟩
      let i1 : Fin (L + 2) := ⟨1, by omega⟩
      let P0 := All.filter (fun A => i0 ∉ A)
      let P10 := All.filter (fun A => i0 ∈ A ∧ i1 ∉ A)
      let P11 := All.filter (fun A => i0 ∈ A ∧ i1 ∈ A)
      have hpart : All.card = P0.card + P10.card + P11.card := by
        have hu : All = (P0 ∪ P10) ∪ P11 := by
          ext A; simp only [Finset.mem_union, Finset.mem_filter, P0, P10, P11]
          by_cases h0 : i0 ∈ A <;> by_cases h1 : i1 ∈ A <;> tauto
        have hd1 : Disjoint P0 P10 := by rw [Finset.disjoint_left]; intro A h1 h2; exact (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2.1
        have hd2 : Disjoint (P0 ∪ P10) P11 := by
          rw [Finset.disjoint_left]; intro A h1 h2
          rcases Finset.mem_union.mp h1 with ha | hb
          · exact (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp h2).2.1
          · exact (Finset.mem_filter.mp hb).2.2 (Finset.mem_filter.mp h2).2.2
        rw [hu, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
      have hshift1_runs : ∀ A : Finset (Fin (L + 2)), (i0 ∉ A ∨ i1 ∈ A) →
          runsL (L + 2) A = runsL (L + 1) (Finset.univ.filter (fun j : Fin (L + 1) => (⟨j.val + 1, by omega⟩ : Fin (L + 2)) ∈ A)) := by
        intro A hor
        let B := Finset.univ.filter (fun j : Fin (L + 1) => (⟨j.val + 1, by omega⟩ : Fin (L + 2)) ∈ A)
        dsimp only [runsL]
        refine Finset.card_bij (fun (i : Fin (L + 2)) (hi) =>
            (⟨i.val - 1, by
              have hne0 : i ≠ i0 := by
                intro heq; subst heq
                rcases hor with h0 | h1
                · exact h0 (Finset.mem_filter.mp hi).1
                · exact (Finset.mem_filter.mp hi).2 (by dsimp only [i0]; omega) h1
              have : 0 < i.val := by
                by_contra hle; exact hne0 (Fin.ext (by dsimp only [i0]; omega))
              have := i.isLt; omega⟩ : Fin (L + 1))) ?_ ?_ ?_
        · intro i hi
          have hiA := (Finset.mem_filter.mp hi).1
          have hiE := (Finset.mem_filter.mp hi).2
          have hne0 : i ≠ i0 := by
            intro heq; subst heq
            rcases hor with h0 | h1
            · exact h0 hiA
            · exact hiE (by dsimp only [i0]; omega) h1
          have hpos : 0 < i.val := by by_contra hle; exact hne0 (Fin.ext (by dsimp only [i0]; omega))
          have hi_lt := i.isLt
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, fun hlt hm => ?_⟩
          · have hfe : (⟨i.val - 1 + 1, by omega⟩ : Fin (L + 2)) = i := Fin.ext (by dsimp only; omega)
            rwa [hfe]
          · have hmA := (Finset.mem_filter.mp hm).2
            dsimp only at hlt
            have hlt2 : i.val + 1 < L + 2 := by omega
            have hfe : (⟨i.val + 1, hlt2⟩ : Fin (L + 2)) = ⟨i.val - 1 + 1 + 1, by omega⟩ := Fin.ext (by dsimp only; omega)
            exact hiE hlt2 (hfe ▸ hmA)
        · intro a ha b hb heq
          have ha_pos : 0 < a.val := by
            by_contra hle
            have ha0 : a = i0 := Fin.ext (by dsimp only [i0]; omega)
            subst ha0
            rcases hor with h0 | h1
            · exact h0 (Finset.mem_filter.mp ha).1
            · exact (Finset.mem_filter.mp ha).2 (by dsimp only [i0]; omega) h1
          have hb_pos : 0 < b.val := by
            by_contra hle
            have hb0 : b = i0 := Fin.ext (by dsimp only [i0]; omega)
            subst hb0
            rcases hor with h0 | h1
            · exact h0 (Finset.mem_filter.mp hb).1
            · exact (Finset.mem_filter.mp hb).2 (by dsimp only [i0]; omega) h1
          have hv := congrArg Fin.val heq; dsimp only at hv
          exact Fin.ext (by omega)
        · intro j hj
          have hjB := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
          have hjE := (Finset.mem_filter.mp hj).2
          have hj_lt := j.isLt
          refine ⟨⟨j.val + 1, by omega⟩, Finset.mem_filter.mpr ⟨hjB, fun hlt hm => ?_⟩, Fin.ext (by simp)⟩
          exact hjE (by dsimp only at hlt; omega) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩)
      have hP10_card : P10.card = ((Finset.univ : Finset (Finset (Fin L))).filter (fun B => runsL L B = (L + 1) / 2)).card := by
        refine Finset.card_bij (fun A _ => Finset.univ.filter (fun j : Fin L => (⟨j.val + 2, by omega⟩ : Fin (L + 2)) ∈ A)) ?_ ?_ ?_
        · intro A hA
          have hAll := (Finset.mem_filter.mp hA).1
          have h01 := (Finset.mem_filter.mp hA).2
          have hruns := (Finset.mem_filter.mp hAll).2
          let B := Finset.univ.filter (fun j : Fin L => (⟨j.val + 2, by omega⟩ : Fin (L + 2)) ∈ A)
          have hr : runsL (L + 2) A = runsL L B + 1 := by
            dsimp only [runsL]
            have hi0_in : i0 ∈ A.filter (fun i : Fin (L + 2) => ∀ h : i.val + 1 < L + 2, (⟨i.val + 1, h⟩ : Fin (L + 2)) ∉ A) :=
              Finset.mem_filter.mpr ⟨h01.1, fun _ hm => h01.2 hm⟩
            rw [← Finset.card_erase_add_one hi0_in]
            congr 1
            refine Finset.card_bij (fun i hi =>
                (⟨i.val - 2, by
                  have hne0 : i ≠ i0 := (Finset.mem_erase.mp hi).1
                  have hne1 : i ≠ i1 := fun h => h01.2 (h ▸ (Finset.mem_filter.mp (Finset.mem_erase.mp hi).2).1)
                  have : 2 ≤ i.val := by
                    by_contra hlt
                    rcases show i.val = 0 ∨ i.val = 1 by omega with h | h
                    · exact hne0 (Fin.ext h)
                    · exact hne1 (Fin.ext h)
                  omega⟩ : Fin L)) ?_ ?_ ?_
            · intro i hi
              have hne0 : i ≠ i0 := (Finset.mem_erase.mp hi).1
              have hiF := (Finset.mem_erase.mp hi).2
              have hiA := (Finset.mem_filter.mp hiF).1
              have hiE := (Finset.mem_filter.mp hiF).2
              have hne1 : i ≠ i1 := fun h => h01.2 (h ▸ hiA)
              have hge2 : 2 ≤ i.val := by
                by_contra hlt
                rcases show i.val = 0 ∨ i.val = 1 by omega with h | h
                · exact hne0 (Fin.ext h)
                · exact hne1 (Fin.ext h)
              have hi_lt := i.isLt
              refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, fun hlt hm => ?_⟩
              · have hfe : (⟨i.val - 2 + 2, by omega⟩ : Fin (L + 2)) = i := Fin.ext (by dsimp only; omega)
                rwa [hfe]
              · have hmA := (Finset.mem_filter.mp hm).2
                dsimp only at hlt
                have hlt2 : i.val + 1 < L + 2 := by omega
                have hfe : (⟨i.val + 1, hlt2⟩ : Fin (L + 2)) = ⟨i.val - 2 + 1 + 2, by omega⟩ := Fin.ext (by dsimp only; omega)
                exact hiE hlt2 (hfe ▸ hmA)
            · intro a ha b hb heq
              have hge_a : 2 ≤ a.val := by
                have hne0 := (Finset.mem_erase.mp ha).1
                have hne1 : a ≠ i1 := fun h => h01.2 (h ▸ (Finset.mem_filter.mp (Finset.mem_erase.mp ha).2).1)
                by_contra hlt; rcases show a.val = 0 ∨ a.val = 1 by omega with h | h
                · exact hne0 (Fin.ext h)
                · exact hne1 (Fin.ext h)
              have hge_b : 2 ≤ b.val := by
                have hne0 := (Finset.mem_erase.mp hb).1
                have hne1 : b ≠ i1 := fun h => h01.2 (h ▸ (Finset.mem_filter.mp (Finset.mem_erase.mp hb).2).1)
                by_contra hlt; rcases show b.val = 0 ∨ b.val = 1 by omega with h | h
                · exact hne0 (Fin.ext h)
                · exact hne1 (Fin.ext h)
              have hv := congrArg Fin.val heq; dsimp only at hv
              exact Fin.ext (by omega)
            · intro j hj
              have hj_lt := j.isLt
              have hjB := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
              have hjE := (Finset.mem_filter.mp hj).2
              refine ⟨⟨j.val + 2, by omega⟩, Finset.mem_erase.mpr ⟨fun h => by have := congrArg Fin.val h; simp [i0] at this,
                Finset.mem_filter.mpr ⟨hjB, fun hlt hm => hjE (by dsimp only at hlt; omega) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
                  have hfe : (⟨j.val + 1 + 2, by omega⟩ : Fin (L + 2)) = ⟨j.val + 2 + 1, hlt⟩ := Fin.ext rfl
                  rwa [hfe]⟩)⟩⟩,
                Fin.ext (by simp)⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          change runsL L B = (L + 1) / 2; omega
        · intro A1 hA1 A2 hA2 heq
          have h1 := (Finset.mem_filter.mp hA1).2
          have h2 := (Finset.mem_filter.mp hA2).2
          ext i
          by_cases h0 : i.val = 0
          · have : i = i0 := Fin.ext h0; subst this; simp [h1.1, h2.1]
          · by_cases h1' : i.val = 1
            · have : i = i1 := Fin.ext h1'; subst this; simp [h1.2, h2.2]
            · have hge : 2 ≤ i.val := by omega
              let j : Fin L := ⟨i.val - 2, by omega⟩
              have hi_lt := i.isLt
              have hj := Finset.ext_iff.mp heq j
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, j] at hj
              have hi_eq : (⟨i.val - 2 + 2, by omega⟩ : Fin (L + 2)) = i := Fin.ext (by dsimp only; omega)
              rwa [hi_eq] at hj
        · intro B hB
          let A : Finset (Fin (L + 2)) := insert i0 (B.image (fun j => ⟨j.val + 2, by omega⟩))
          have hi0A : i0 ∈ A := Finset.mem_insert_self _ _
          have hi1A : i1 ∉ A := by
            simp only [A, Finset.mem_insert, Finset.mem_image, i0, i1]
            rintro (h | ⟨j, _, h⟩)
            · have := congrArg Fin.val h; simp at this
            · have := congrArg Fin.val h; dsimp only at this; omega
          have hB_eq : Finset.univ.filter (fun j : Fin L => (⟨j.val + 2, by omega⟩ : Fin (L + 2)) ∈ A) = B := by
            ext j; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_image, i0]
            constructor
            · rintro (h | ⟨j', hj', heq⟩)
              · have := congrArg Fin.val h; dsimp only at this; omega
              · have : j' = j := Fin.ext (by have := congrArg Fin.val heq; dsimp only at this; omega)
                rwa [← this]
            · intro hj; right; exact ⟨j, hj, rfl⟩
          have hrunsA : runsL (L + 2) A = (L + 3) / 2 := by
            have hB_runs := (Finset.mem_filter.mp hB).2
            have hr : runsL (L + 2) A = runsL L B + 1 := by
              dsimp only [runsL]
              have hi0_in : i0 ∈ A.filter (fun i : Fin (L + 2) => ∀ h : i.val + 1 < L + 2, (⟨i.val + 1, h⟩ : Fin (L + 2)) ∉ A) :=
                Finset.mem_filter.mpr ⟨hi0A, fun _ hm => hi1A hm⟩
              rw [← Finset.card_erase_add_one hi0_in]
              congr 1
              refine Finset.card_bij (fun i hi =>
                  (⟨i.val - 2, by
                    have hne0 := (Finset.mem_erase.mp hi).1
                    have hne1 : i ≠ i1 := fun h => hi1A (h ▸ (Finset.mem_filter.mp (Finset.mem_erase.mp hi).2).1)
                    have : 2 ≤ i.val := by
                      by_contra hlt; rcases show i.val = 0 ∨ i.val = 1 by omega with h | h
                      · exact hne0 (Fin.ext h)
                      · exact hne1 (Fin.ext h)
                    omega⟩ : Fin L)) ?_ ?_ ?_
              · intro i hi
                have hne0 := (Finset.mem_erase.mp hi).1
                have hiF := (Finset.mem_erase.mp hi).2
                have hiA := (Finset.mem_filter.mp hiF).1
                have hiE := (Finset.mem_filter.mp hiF).2
                have hne1 : i ≠ i1 := fun h => hi1A (h ▸ hiA)
                have hge2 : 2 ≤ i.val := by
                  by_contra hlt; rcases show i.val = 0 ∨ i.val = 1 by omega with h | h
                  · exact hne0 (Fin.ext h)
                  · exact hne1 (Fin.ext h)
                have hi_lt := i.isLt
                have hjB : (⟨i.val - 2, by omega⟩ : Fin L) ∈ B := by
                  rw [← hB_eq]; refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                  have hi_eq : (⟨i.val - 2 + 2, by omega⟩ : Fin (L + 2)) = i := Fin.ext (by dsimp only; omega)
                  rwa [hi_eq]
                refine Finset.mem_filter.mpr ⟨hjB, fun hlt hm => ?_⟩
                dsimp only at hlt
                have hmA : (⟨i.val + 1, by omega⟩ : Fin (L + 2)) ∈ A := by
                  have h1 : (⟨i.val + 1, by omega⟩ : Fin (L + 2)) ∈ B.image (fun j : Fin L => (⟨j.val + 2, by omega⟩ : Fin (L + 2))) :=
                    Finset.mem_image.mpr ⟨(⟨i.val - 2 + 1, hlt⟩ : Fin L), hm, Fin.ext (by dsimp only; omega)⟩
                  exact Finset.mem_insert_of_mem h1
                exact hiE (by omega) hmA
              · intro a ha b hb heq
                have hge_a : 2 ≤ a.val := by
                  have hne0 := (Finset.mem_erase.mp ha).1
                  have hne1 : a ≠ i1 := fun h => hi1A (h ▸ (Finset.mem_filter.mp (Finset.mem_erase.mp ha).2).1)
                  by_contra hlt; rcases show a.val = 0 ∨ a.val = 1 by omega with h | h
                  · exact hne0 (Fin.ext h)
                  · exact hne1 (Fin.ext h)
                have hge_b : 2 ≤ b.val := by
                  have hne0 := (Finset.mem_erase.mp hb).1
                  have hne1 : b ≠ i1 := fun h => hi1A (h ▸ (Finset.mem_filter.mp (Finset.mem_erase.mp hb).2).1)
                  by_contra hlt; rcases show b.val = 0 ∨ b.val = 1 by omega with h | h
                  · exact hne0 (Fin.ext h)
                  · exact hne1 (Fin.ext h)
                have hv := congrArg Fin.val heq; dsimp only at hv; exact Fin.ext (by omega)
              · intro j hj
                have hjB := (Finset.mem_filter.mp hj).1
                have hjE := (Finset.mem_filter.mp hj).2
                have hjA : (⟨j.val + 2, by omega⟩ : Fin (L + 2)) ∈ A :=
                  Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, hjB, rfl⟩)
                have hj_lt := j.isLt
                refine ⟨⟨j.val + 2, by omega⟩, Finset.mem_erase.mpr ⟨fun h => by have := congrArg Fin.val h; simp [i0] at this,
                  Finset.mem_filter.mpr ⟨hjA, fun hlt hm => ?_⟩⟩, Fin.ext (by simp)⟩
                dsimp only at hlt
                have hj1B : (⟨j.val + 1, by omega⟩ : Fin L) ∈ B := by
                  rw [← hB_eq]; refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                  have hfe : (⟨j.val + 1 + 2, by omega⟩ : Fin (L + 2)) = ⟨j.val + 2 + 1, hlt⟩ := Fin.ext rfl
                  rwa [hfe]
                exact hjE (by omega) hj1B
            omega
          exact ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrunsA⟩, hi0A, hi1A⟩, hB_eq⟩
      have hP10_val : P10.card = if L % 2 = 0 then L + 1 else 1 := by
        rw [hP10_card, ih L (by omega)]
      by_cases heven : L % 2 = 0
      · have hP0_card : P0.card = 1 := by
          have hbij : P0.card = ((Finset.univ : Finset (Finset (Fin (L + 1)))).filter (fun B => runsL (L + 1) B = (L + 2) / 2)).card := by
            refine Finset.card_bij (fun A _ => Finset.univ.filter (fun j : Fin (L + 1) => (⟨j.val + 1, by omega⟩ : Fin (L + 2)) ∈ A)) ?_ ?_ ?_
            · intro A hA
              have hruns := (Finset.mem_filter.mp (Finset.mem_filter.mp hA).1).2
              have h0 := (Finset.mem_filter.mp hA).2
              rw [hshift1_runs A (Or.inl h0)] at hruns
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
            · intro A1 hA1 A2 hA2 heq
              have h1 := (Finset.mem_filter.mp hA1).2; have h2 := (Finset.mem_filter.mp hA2).2
              ext i; by_cases h0 : i.val = 0
              · have : i = i0 := Fin.ext h0; subst this; simp [h1, h2]
              · have hi_lt := i.isLt
                let j : Fin (L + 1) := ⟨i.val - 1, by omega⟩
                have hj := Finset.ext_iff.mp heq j
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, j] at hj
                have hi_eq : (⟨i.val - 1 + 1, by omega⟩ : Fin (L + 2)) = i := Fin.ext (by dsimp only; omega)
                rwa [hi_eq] at hj
            · intro B hB
              let A : Finset (Fin (L + 2)) := B.image (fun j => ⟨j.val + 1, by omega⟩)
              have h0 : i0 ∉ A := by
                simp only [A, Finset.mem_image, i0]; rintro ⟨j, _, h⟩; have := congrArg Fin.val h; dsimp only at this; omega
              have hB_eq : Finset.univ.filter (fun j : Fin (L + 1) => (⟨j.val + 1, by omega⟩ : Fin (L + 2)) ∈ A) = B := by
                ext j; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
                constructor
                · rintro ⟨j', hj', heq⟩; have : j' = j := Fin.ext (by have := congrArg Fin.val heq; dsimp only at this; omega); rwa [← this]
                · intro hj; exact ⟨j, hj, rfl⟩
              have hrunsA : runsL (L + 2) A = (L + 3) / 2 := by
                rw [hshift1_runs A (Or.inl h0), hB_eq, (Finset.mem_filter.mp hB).2]; omega
              exact ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrunsA⟩, h0⟩, hB_eq⟩
          rw [hbij, ih (L + 1) (by omega), if_neg (by omega)]
        have hP11_card : P11.card = 1 := by
          have hB_odd_card : ((Finset.univ : Finset (Finset (Fin (L + 1)))).filter (fun B => runsL (L + 1) B = (L + 2) / 2)).card = 1 := by
            rw [ih (L + 1) (by omega), if_neg (by omega)]
          have hB_has0 : ∀ B : Finset (Fin (L + 1)), runsL (L + 1) B = (L + 2) / 2 → (⟨0, by omega⟩ : Fin (L + 1)) ∈ B := by
            intro B hB
            by_contra hnot0
            let B' : Finset (Fin L) := Finset.univ.filter (fun j : Fin L => (⟨j.val + 1, by omega⟩ : Fin (L + 1)) ∈ B)
            have hle : runsL (L + 1) B ≤ runsL L B' := by
              dsimp only [runsL]
              have hLpos : 0 < L := by
                by_contra h0; have hL0 : L = 0 := by omega
                subst hL0
                have hBe : B = ∅ := by
                  ext x; fin_cases x; exact iff_of_false hnot0 (Finset.notMem_empty _)
                have hr0 : runsL (0 + 1) B = 0 := by rw [hBe]; dsimp only [runsL]; rw [Finset.filter_empty, Finset.card_empty]
                omega
              refine Finset.card_le_card_of_injOn (fun i : Fin (L + 1) => (⟨if i.val = 0 then 0 else i.val - 1, by have := i.isLt; split_ifs <;> omega⟩ : Fin L)) ?_ ?_
              · intro i hi
                have hiB := (Finset.mem_filter.mp hi).1
                have hiE := (Finset.mem_filter.mp hi).2
                have hi_lt := i.isLt
                have hpos : 0 < i.val := by
                  by_contra hle
                  have h0 : (⟨0, by omega⟩ : Fin (L + 1)) = i := Fin.ext (by dsimp only; omega)
                  exact hnot0 (h0 ▸ hiB)
                have hif : (if i.val = 0 then 0 else i.val - 1) = i.val - 1 := if_neg (by omega)
                refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, fun hlt hm => ?_⟩)
                · have hfe : (⟨(if i.val = 0 then 0 else i.val - 1) + 1, by split_ifs <;> omega⟩ : Fin (L + 1)) = i :=
                    Fin.ext (by dsimp only; rw [hif]; omega)
                  rwa [hfe]
                · have hmB := (Finset.mem_filter.mp hm).2
                  dsimp only at hlt
                  rw [hif] at hlt
                  have hlt2 : i.val + 1 < L + 1 := by omega
                  have hfe : (⟨i.val + 1, hlt2⟩ : Fin (L + 1)) = ⟨(if i.val = 0 then 0 else i.val - 1) + 1 + 1, by omega⟩ :=
                    Fin.ext (by dsimp only; rw [hif]; omega)
                  exact hiE hlt2 (hfe ▸ hmB)
              · intro a ha b hb heq
                have hap : 0 < a.val := by
                  by_contra hle; have h0 : (⟨0, by omega⟩ : Fin (L + 1)) = a := Fin.ext (by dsimp only; omega)
                  exact hnot0 (h0 ▸ (Finset.mem_filter.mp ha).1)
                have hbp : 0 < b.val := by
                  by_contra hle; have h0 : (⟨0, by omega⟩ : Fin (L + 1)) = b := Fin.ext (by dsimp only; omega)
                  exact hnot0 (h0 ▸ (Finset.mem_filter.mp hb).1)
                have hv := congrArg Fin.val heq; dsimp only at hv
                rw [if_neg (by omega), if_neg (by omega)] at hv
                exact Fin.ext (by omega)
            have hle2 := runsL_le L B'
            omega
          have hbij : P11.card = ((Finset.univ : Finset (Finset (Fin (L + 1)))).filter (fun B => runsL (L + 1) B = (L + 2) / 2)).card := by
            refine Finset.card_bij (fun A _ => Finset.univ.filter (fun j : Fin (L + 1) => (⟨j.val + 1, by omega⟩ : Fin (L + 2)) ∈ A)) ?_ ?_ ?_
            · intro A hA
              have hruns := (Finset.mem_filter.mp (Finset.mem_filter.mp hA).1).2
              have h01 := (Finset.mem_filter.mp hA).2
              rw [hshift1_runs A (Or.inr h01.2)] at hruns
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
            · intro A1 hA1 A2 hA2 heq
              have h1 := (Finset.mem_filter.mp hA1).2; have h2 := (Finset.mem_filter.mp hA2).2
              ext i; by_cases h0 : i.val = 0
              · have : i = i0 := Fin.ext h0; subst this; simp [h1.1, h2.1]
              · have hi_lt := i.isLt
                let j : Fin (L + 1) := ⟨i.val - 1, by omega⟩
                have hj := Finset.ext_iff.mp heq j
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, j] at hj
                have hi_eq : (⟨i.val - 1 + 1, by omega⟩ : Fin (L + 2)) = i := Fin.ext (by dsimp only; omega)
                rwa [hi_eq] at hj
            · intro B hB
              have hB0 : (⟨0, by omega⟩ : Fin (L + 1)) ∈ B := hB_has0 B (Finset.mem_filter.mp hB).2
              let A : Finset (Fin (L + 2)) := insert i0 (B.image (fun j => ⟨j.val + 1, by omega⟩))
              have h0 : i0 ∈ A := Finset.mem_insert_self _ _
              have h1 : i1 ∈ A := Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨⟨0, by omega⟩, hB0, Fin.ext (by simp [i1])⟩)
              have hB_eq : Finset.univ.filter (fun j : Fin (L + 1) => (⟨j.val + 1, by omega⟩ : Fin (L + 2)) ∈ A) = B := by
                ext j; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_image, i0]
                constructor
                · rintro (h | ⟨j', hj', heq⟩)
                  · have := congrArg Fin.val h; dsimp only at this; omega
                  · have : j' = j := Fin.ext (by have := congrArg Fin.val heq; dsimp only at this; omega); rwa [← this]
                · intro hj; right; exact ⟨j, hj, rfl⟩
              have hrunsA : runsL (L + 2) A = (L + 3) / 2 := by
                rw [hshift1_runs A (Or.inr h1), hB_eq, (Finset.mem_filter.mp hB).2]; omega
              exact ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrunsA⟩, h0, h1⟩, hB_eq⟩
          rw [hbij, hB_odd_card]
        rw [if_pos (by omega)]
        rw [if_pos heven] at hP10_val
        change All.card = L + 2 + 1
        omega
      · have hP0_empty : P0 = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro A hA
          have hruns := (Finset.mem_filter.mp (Finset.mem_filter.mp hA).1).2
          have h0 := (Finset.mem_filter.mp hA).2
          rw [hshift1_runs A (Or.inl h0)] at hruns
          have hle := runsL_le (L + 1) (Finset.univ.filter (fun j : Fin (L + 1) => (⟨j.val + 1, by omega⟩ : Fin (L + 2)) ∈ A))
          omega
        have hP11_empty : P11 = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro A hA
          have hruns := (Finset.mem_filter.mp (Finset.mem_filter.mp hA).1).2
          have h01 := (Finset.mem_filter.mp hA).2
          rw [hshift1_runs A (Or.inr h01.2)] at hruns
          have hle := runsL_le (L + 1) (Finset.univ.filter (fun j : Fin (L + 1) => (⟨j.val + 1, by omega⟩ : Fin (L + 2)) ∈ A))
          omega
        rw [hP0_empty, hP11_empty, Finset.card_empty] at hpart
        rw [if_neg (by omega)]
        rw [if_neg heven] at hP10_val
        change All.card = 1
        omega

set_option maxHeartbeats 800000 in
private lemma countTop_eq_prod_factor (n : ℕ) (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hU : goodSub n U) (hd : 2 ≤ Module.finrank (ZMod 2) U)
    (hsurj : Function.Surjective ((parityMap n).comp (embedRuns n (suppSub n U) (suppSub_ne_univ_of_finrank n U hU hd)))) :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    letI : Fintype (Submodule (ZMod 2) (Fin n → ZMod 2)) := Fintype.ofFinite _
    let spaces := (Finset.univ : Finset (Submodule (ZMod 2) (Fin n → ZMod 2))).filter (goodSub n)
    let hosts := spaces.filter (fun E => U ≤ E)
    let topDim := hosts.sup (fun E : Submodule (ZMod 2) (Fin n → ZMod 2) => Module.finrank (ZMod 2) E)
    ((hosts.filter (fun E : Submodule (ZMod 2) (Fin n → ZMod 2) => Module.finrank (ZMod 2) E = topDim)).card) =
      ∏ a ∈ exitsS n (suppSub n U), factorG (gapS n (suppSub n U) a) := by
  classical
  intro spaces hosts topDim
  let S := suppSub n U
  have hS_ne_u : S ≠ Finset.univ := suppSub_ne_univ_of_finrank n U hU hd
  have hS_ne_e : S.Nonempty := suppSub_nonempty_of_finrank n U (by omega)
  let m := (exitsS n S).card
  let targetDim := m + (∑ a ∈ exitsS n S, (gapS n S a - 1) / 2) - 4
  have hrank4 : ∀ (S' : Finset (Fin n)) (hS'u : S' ≠ Finset.univ), S ⊆ S' →
      (∀ i ∈ S, nextC n i ∈ S' → nextC n i ∈ S) →
      (∀ i ∈ S', nextC n i ∈ S → i ∈ S) →
      Function.Surjective ((parityMap n).comp (embedRuns n S' hS'u)) ∧
      Module.finrank (ZMod 2) (LinearMap.ker ((parityMap n).comp (embedRuns n S' hS'u))) =
        (exitsS n S').card - 4 ∧
      4 ≤ (exitsS n S').card := by
    intro S' hS'u hsub hnoR hnoL
    have hex_sub : exitsS n S ⊆ exitsS n S' := by
      intro a ha
      have haS := (Finset.mem_filter.mp ha).1
      have hna := (Finset.mem_filter.mp ha).2
      exact Finset.mem_filter.mpr ⟨hsub haS, fun hm => hna (hnoR a haS hm)⟩
    have hV_sub : LinearMap.range (embedRuns n S hS_ne_u) ≤ LinearMap.range (embedRuns n S' hS'u) := by
      intro x hx
      rw [mem_range_embedRuns_iff] at hx ⊢
      refine ⟨fun i hi => hx.1 i (fun hm => hi (hsub hm)), fun i hi hni => ?_⟩
      by_cases hiS : i ∈ S
      · exact hx.2 i hiS (hnoR i hiS hni)
      · have hniS : nextC n i ∉ S := fun hm => hiS (hnoL i hi hm)
        rw [hx.1 i hiS, hx.1 (nextC n i) hniS]
    have hsurj' : Function.Surjective ((parityMap n).comp (embedRuns n S' hS'u)) := by
      intro y
      rcases hsurj y with ⟨c, hc⟩
      have hm : embedRuns n S hS_ne_u c ∈ LinearMap.range (embedRuns n S' hS'u) := hV_sub ⟨c, rfl⟩
      rcases hm with ⟨c', hc'⟩
      exact ⟨c', by dsimp only [LinearMap.comp_apply] at hc ⊢; rw [hc', hc]⟩
    have hrn := LinearMap.finrank_range_add_finrank_ker ((parityMap n).comp (embedRuns n S' hS'u))
    have hrange : LinearMap.range ((parityMap n).comp (embedRuns n S' hS'u)) = ⊤ :=
      LinearMap.range_eq_top.mpr hsurj'
    rw [hrange, finrank_top, Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hrn
    exact ⟨hsurj', by omega, by omega⟩
  have hhost_struct : ∀ E ∈ hosts,
      let S' := suppSub n E
      S ⊆ S' ∧ S' ≠ Finset.univ ∧
      (∀ i ∈ S, nextC n i ∈ S' → nextC n i ∈ S) ∧
      (∀ i ∈ S', nextC n i ∈ S → i ∈ S) := by
    intro E hE
    have hE_good : goodSub n E := (Finset.mem_filter.mp (Finset.mem_filter.mp hE).1).2
    have hUE : U ≤ E := (Finset.mem_filter.mp hE).2
    have hsub : S ⊆ suppSub n E := fun i hi => by
      rcases mem_suppSub.mp hi with ⟨x, hxU, hxi⟩
      exact mem_suppSub.mpr ⟨x, hUE hxU, hxi⟩
    have hdimE : 2 ≤ Module.finrank (ZMod 2) E := le_trans hd (Submodule.finrank_mono hUE)
    have hne : suppSub n E ≠ Finset.univ := suppSub_ne_univ_of_finrank n E hE_good hdimE
    refine ⟨hsub, hne, fun i hi hni => ?_, fun i hi hni => ?_⟩
    · by_contra hnot
      have heq := goodSub_adj_eq n E hE_good (hsub hi) hni
      rcases mem_suppSub.mp hi with ⟨x, hxU, hxi⟩
      have hxni : x (nextC n i) = 0 := by
        by_contra hnz; exact hnot (mem_suppSub.mpr ⟨x, hxU, hnz⟩)
      exact hxi ((heq x (hUE hxU)).trans hxni)
    · by_contra hnot
      have heq := goodSub_adj_eq n E hE_good hi (hsub hni)
      rcases mem_suppSub.mp hni with ⟨x, hxU, hxni⟩
      have hxi : x i = 0 := by
        by_contra hnz; exact hnot (mem_suppSub.mpr ⟨x, hxU, hnz⟩)
      exact hxni ((heq x (hUE hxU)).symm.trans hxi)
  let projInt : (a : exitsS n S) → Finset (Fin n) → Finset (Fin (gapS n S a.1 - 2)) :=
    fun a S' => Finset.univ.filter (fun k : Fin (gapS n S a.1 - 2) => moveC n a.1 (k.val + 2) ∈ S')
  have hexits_decomp : ∀ (S' : Finset (Fin n)), S ⊆ S' →
      (∀ i ∈ S, nextC n i ∈ S' → nextC n i ∈ S) →
      (∀ i ∈ S', nextC n i ∈ S → i ∈ S) →
      (exitsS n S').card = m + ∑ a : exitsS n S, runsL (gapS n S a.1 - 2) (projInt a S') := by
    intro S' hsub hnoR hnoL
    have hex_S : exitsS n S ⊆ exitsS n S' := fun a ha =>
      Finset.mem_filter.mpr ⟨hsub (Finset.mem_filter.mp ha).1, fun hm => (Finset.mem_filter.mp ha).2 (hnoR a (Finset.mem_filter.mp ha).1 hm)⟩
    have hdisj_S : ∀ a : exitsS n S, Disjoint (exitsS n S) ((exitsS n S') ∩ gapInt n S a.1) := fun a =>
      Disjoint.mono (Finset.filter_subset _ _) Finset.inter_subset_right (gapInt_disjoint_S n S a.2).symm
    have hcover : exitsS n S' = exitsS n S ∪ (Finset.univ : Finset (exitsS n S)).biUnion (fun a => (exitsS n S') ∩ gapInt n S a.1) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_inter]
      constructor
      · intro hx
        by_cases hxS : x ∈ S
        · left; exact Finset.mem_filter.mpr ⟨hxS, fun hm => (Finset.mem_filter.mp hx).2 (hsub hm)⟩
        · right
          have hxS' := (Finset.mem_filter.mp hx).1
          have hpx : prevC n x ∉ S := fun hm => hxS (by rw [← nextC_prevC n x]; exact hnoR (prevC n x) hm (by rwa [nextC_prevC]))
          have hnx : nextC n x ∉ S := fun hm => hxS (hnoL x hxS' hm)
          rcases mem_gapInt_of_not_mem_and_not_adj n S hS_ne_e hS_ne_u hxS hpx hnx with ⟨a, ha, hxa⟩
          exact ⟨⟨a, ha⟩, hx, hxa⟩
      · rintro (hx | ⟨a, hx, _⟩)
        · exact hex_S hx
        · exact hx
    have hdisj_all : Disjoint (exitsS n S) ((Finset.univ : Finset (exitsS n S)).biUnion (fun a => (exitsS n S') ∩ gapInt n S a.1)) := by
      rw [Finset.disjoint_biUnion_right]; intro a _; exact hdisj_S a
    have hpw : Set.PairwiseDisjoint ((Finset.univ : Finset (exitsS n S)) : Set (exitsS n S))
        (fun a => (exitsS n S') ∩ gapInt n S a.1) := by
      intro a _ b _ hab
      dsimp only [Function.onFun]
      exact Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right
        (gapInt_pairwise_disjoint n S a.2 b.2 (fun h => hab (Subtype.ext h)))
    rw [hcover, Finset.card_union_of_disjoint hdisj_all, Finset.card_biUnion hpw]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    have haS := (Finset.mem_filter.mp a.2).1
    have hspec := (gapS_iff n S haS (gapS n S a.1)).mp rfl
    dsimp only [runsL, projInt]
    refine Finset.card_bij (fun (x : Fin n) hx =>
        (⟨Classical.choose (Finset.mem_image.mp (Finset.mem_inter.mp hx).2),
          Finset.mem_range.mp (Classical.choose_spec (Finset.mem_image.mp (Finset.mem_inter.mp hx).2)).1⟩ : Fin (gapS n S a.1 - 2))) ?_ ?_ ?_
    · intro x hx
      let k := Classical.choose (Finset.mem_image.mp (Finset.mem_inter.mp hx).2)
      have hk_spec := Classical.choose_spec (Finset.mem_image.mp (Finset.mem_inter.mp hx).2)
      have hk_lt : k < gapS n S a.1 - 2 := Finset.mem_range.mp hk_spec.1
      have hxk : moveC n a.1 (k + 2) = x := hk_spec.2
      have hxE := (Finset.mem_inter.mp hx).1
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxk.symm ▸ (Finset.mem_filter.mp hxE).1⟩, fun hlt hm => ?_⟩
      have hmS' := (Finset.mem_filter.mp hm).2
      have hnx : nextC n x = moveC n a.1 (k + 1 + 2) := by
        rw [← hxk, ← moveC_one, moveC_add]
      exact (Finset.mem_filter.mp hxE).2 (hnx.symm ▸ hmS')
    · intro x1 hx1 x2 hx2 heq
      have h1 := Classical.choose_spec (Finset.mem_image.mp (Finset.mem_inter.mp hx1).2)
      have h2 := Classical.choose_spec (Finset.mem_image.mp (Finset.mem_inter.mp hx2).2)
      have hk_eq : Classical.choose (Finset.mem_image.mp (Finset.mem_inter.mp hx1).2) =
          Classical.choose (Finset.mem_image.mp (Finset.mem_inter.mp hx2).2) := congrArg Fin.val heq
      rw [← h1.2, ← h2.2, hk_eq]
    · intro k hk
      have hkS' := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
      have hkE := (Finset.mem_filter.mp hk).2
      let x := moveC n a.1 (k.val + 2)
      have hx_int : x ∈ gapInt n S a.1 := Finset.mem_image.mpr ⟨k.val, Finset.mem_range.mpr k.isLt, rfl⟩
      have hnx_not : nextC n x ∉ S' := by
        by_cases hlt : k.val + 1 < gapS n S a.1 - 2
        · intro hm
          have : moveC n a.1 (k.val + 1 + 2) ∈ S' := by
            convert hm using 1; dsimp only [x]; rw [← moveC_one, moveC_add]
          exact hkE hlt (Finset.mem_filter.mpr ⟨Finset.mem_univ _, this⟩)
        · intro hm
          have hk_last : k.val + 3 = gapS n S a.1 := by omega
          have hnx_eq : nextC n x = moveC n a.1 (gapS n S a.1) := by
            dsimp only [x]; rw [← moveC_one, moveC_add, hk_last]
          have hlast_next : nextC n (moveC n a.1 (gapS n S a.1)) ∈ S := by
            rw [← moveC_one, moveC_add]; exact hspec.2.2
          have hmS := hnoL _ (hnx_eq ▸ hm) hlast_next
          exact hspec.2.1 (gapS n S a.1 - 1) (by omega) (by rw [Nat.sub_add_cancel (by omega)]; exact hmS)
      have hx_mem : x ∈ (exitsS n S') ∩ gapInt n S a.1 :=
        Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨hkS', hnx_not⟩, hx_int⟩
      refine ⟨x, hx_mem, ?_⟩
      apply Fin.ext; dsimp only
      have hch := Classical.choose_spec (Finset.mem_image.mp (Finset.mem_inter.mp hx_mem).2)
      have hch_lt : Classical.choose (Finset.mem_image.mp (Finset.mem_inter.mp hx_mem).2) + 2 < n := by
        have := Finset.mem_range.mp hch.1; omega
      have hk_lt2 : k.val + 2 < n := by omega
      have := moveC_injective_lt n a.1 hch_lt hk_lt2 hch.2
      omega
  let buildS' : (∀ a : exitsS n S, Finset (Fin (gapS n S a.1 - 2))) → Finset (Fin n) :=
    fun cfg => S ∪ (Finset.univ : Finset (exitsS n S)).biUnion
      (fun a => (cfg a).image (fun k => moveC n a.1 (k.val + 2)))
  have hbuild_props : ∀ cfg : (∀ a : exitsS n S, Finset (Fin (gapS n S a.1 - 2))),
      let S' := buildS' cfg
      S ⊆ S' ∧ S' ≠ Finset.univ ∧
      (∀ i ∈ S, nextC n i ∈ S' → nextC n i ∈ S) ∧
      (∀ i ∈ S', nextC n i ∈ S → i ∈ S) ∧
      (∀ a : exitsS n S, projInt a S' = cfg a) := by
    intro cfg
    let S' := buildS' cfg
    have hsub : S ⊆ S' := Finset.subset_union_left
    have hsub_int : ∀ a : exitsS n S, (cfg a).image (fun k => moveC n a.1 (k.val + 2)) ⊆ gapInt n S a.1 := by
      intro a x hx
      rcases Finset.mem_image.mp hx with ⟨k, _, rfl⟩
      exact Finset.mem_image.mpr ⟨k.val, Finset.mem_range.mpr k.isLt, rfl⟩
    have hno_boundary : ∀ a : exitsS n S, nextC n a.1 ∉ S' := by
      intro a hm
      rcases Finset.mem_union.mp hm with hS | hbi
      · exact (Finset.mem_filter.mp a.2).2 hS
      · rcases Finset.mem_biUnion.mp hbi with ⟨b, _, hxb⟩
        have hxint := hsub_int b hxb
        rcases Finset.mem_image.mp hxint with ⟨k, hk, heq⟩
        have hkl : k < gapS n S b.1 - 2 := Finset.mem_range.mp hk
        have hbS := (Finset.mem_filter.mp b.2).1
        have hsb := (gapS_iff n S hbS (gapS n S b.1)).mp rfl
        have hba : moveC n b.1 (k + 1) = a.1 := by
          apply nextC_injective n
          rw [← moveC_one, moveC_add, show k + 1 + 1 = k + 2 by omega]; exact heq
        exact hsb.2.1 k (by omega) (hba.symm ▸ (Finset.mem_filter.mp a.2).1)
    have hne_u : S' ≠ Finset.univ := by
      rcases hS_ne_e with ⟨x0, hx0⟩
      have hex0 : runExit n S hS_ne_u x0 ∈ exitsS n S := runExit_mem_exits n S hS_ne_u hx0
      intro hu
      exact hno_boundary ⟨runExit n S hS_ne_u x0, hex0⟩ (hu.symm ▸ Finset.mem_univ _)
    have hnoR : ∀ i ∈ S, nextC n i ∈ S' → nextC n i ∈ S := by
      intro i hi hni
      by_contra hnot
      exact hno_boundary ⟨i, Finset.mem_filter.mpr ⟨hi, hnot⟩⟩ hni
    have hnoL : ∀ i ∈ S', nextC n i ∈ S → i ∈ S := by
      intro i hi hni
      by_contra hnot
      rcases Finset.mem_union.mp hi with hS | hbi
      · exact hnot hS
      · rcases Finset.mem_biUnion.mp hbi with ⟨b, _, hxb⟩
        have hxint := hsub_int b hxb
        rcases Finset.mem_image.mp hxint with ⟨k, hk, heq⟩
        have hkl : k < gapS n S b.1 - 2 := Finset.mem_range.mp hk
        have hbS := (Finset.mem_filter.mp b.2).1
        have hsb := (gapS_iff n S hbS (gapS n S b.1)).mp rfl
        have hni_eq : nextC n i = moveC n b.1 (k + 3) := by
          rw [← heq, ← moveC_one, moveC_add]
        exact hsb.2.1 (k + 2) (by omega) (hni_eq ▸ hni)
    have hproj : ∀ a : exitsS n S, projInt a S' = cfg a := by
      intro a
      ext k
      simp only [projInt, Finset.mem_filter, Finset.mem_univ, true_and, S', buildS', Finset.mem_union, Finset.mem_biUnion]
      have hx_int : moveC n a.1 (k.val + 2) ∈ gapInt n S a.1 :=
        Finset.mem_image.mpr ⟨k.val, Finset.mem_range.mpr k.isLt, rfl⟩
      constructor
      · rintro (hS | ⟨b, hxb⟩)
        · exact (Finset.disjoint_left.mp (gapInt_disjoint_S n S a.2) hx_int hS).elim
        · have hba : b = a := by
            by_contra hne
            exact Finset.disjoint_left.mp (gapInt_pairwise_disjoint n S a.2 b.2 (fun h => hne (Subtype.ext h.symm)))
              hx_int (hsub_int b hxb)
          rcases Finset.mem_image.mp (hba ▸ hxb) with ⟨k', hk', heq⟩
          have haS := (Finset.mem_filter.mp a.2).1
          have hsa := (gapS_iff n S haS (gapS n S a.1)).mp rfl
          have : k'.val + 2 = k.val + 2 := moveC_injective_lt n a.1 (by have := k'.isLt; omega) (by have := k.isLt; omega) heq
          have : k' = k := Fin.ext (by omega)
          rwa [← this]
      · intro hk; right; exact ⟨a, Finset.mem_image.mpr ⟨k, hk, rfl⟩⟩
    exact ⟨hsub, hne_u, hnoR, hnoL, hproj⟩
  have hbuild_E : ∀ cfg : (∀ a : exitsS n S, Finset (Fin (gapS n S a.1 - 2))),
      let S' := buildS' cfg
      let hS'u := (hbuild_props cfg).2.1
      let E := (LinearMap.ker ((parityMap n).comp (embedRuns n S' hS'u))).map (embedRuns n S' hS'u)
      E ∈ hosts ∧ suppSub n E = S' ∧
      Module.finrank (ZMod 2) E = m + (∑ a : exitsS n S, runsL (gapS n S a.1 - 2) (cfg a)) - 4 := by
    intro cfg
    let S' := buildS' cfg
    have hp := hbuild_props cfg
    let hS'u := hp.2.1
    let E := (LinearMap.ker ((parityMap n).comp (embedRuns n S' hS'u))).map (embedRuns n S' hS'u)
    have hE_good : goodSub n E := by
      refine ⟨fun x hx b => ?_, fun x hx y hy i => ?_⟩
      · rcases Submodule.mem_map.mp hx with ⟨c, hc, rfl⟩
        exact congrFun (LinearMap.mem_ker.mp hc) b
      · rcases Submodule.mem_map.mp hx with ⟨cx, _, rfl⟩
        rcases Submodule.mem_map.mp hy with ⟨cy, _, rfl⟩
        have hx' := (mem_range_embedRuns_iff n S' hS'u _).mp ⟨cx, rfl⟩
        have hy' := (mem_range_embedRuns_iff n S' hS'u _).mp ⟨cy, rfl⟩
        by_cases h1 : i ∈ S'
        · by_cases h2 : nextC n i ∈ S'
          · rw [hx'.2 i h1 h2, hy'.2 i h1 h2]
          · rw [hx'.1 _ h2, hy'.1 _ h2, mul_zero, zero_mul]
        · rw [hx'.1 _ h1, hy'.1 _ h1, zero_mul, mul_zero]
    have hUE : U ≤ E := by
      intro x hxU
      have hxS : x ∈ LinearMap.range (embedRuns n S hS_ne_u) := by
        rw [mem_range_embedRuns_iff]
        refine ⟨fun i hi => by by_contra hnz; exact hi (mem_suppSub.mpr ⟨x, hxU, hnz⟩),
          fun i hi hni => goodSub_adj_eq n U hU hi hni x hxU⟩
      have hxS' : x ∈ LinearMap.range (embedRuns n S' hS'u) := by
        rw [mem_range_embedRuns_iff] at hxS ⊢
        refine ⟨fun i hi => hxS.1 i (fun hm => hi (hp.1 hm)), fun i hi hni => ?_⟩
        by_cases hiS : i ∈ S
        · exact hxS.2 i hiS (hp.2.2.1 i hiS hni)
        · have hniS : nextC n i ∉ S := fun hm => hiS (hp.2.2.2.1 i hi hm)
          rw [hxS.1 i hiS, hxS.1 (nextC n i) hniS]
      rcases hxS' with ⟨c, hc⟩
      refine Submodule.mem_map.mpr ⟨c, ?_, hc⟩
      rw [LinearMap.mem_ker]; funext b
      dsimp only [LinearMap.comp_apply]; rw [hc]; exact hU.1 x hxU b
    have hsuppE : suppSub n E = S' := by
      ext i
      constructor
      · intro hi
        rcases mem_suppSub.mp hi with ⟨x, hxE, hxi⟩
        rcases Submodule.mem_map.mp hxE with ⟨c, _, rfl⟩
        by_contra hnot
        exact hxi (((mem_range_embedRuns_iff n S' hS'u _).mp ⟨c, rfl⟩).1 i hnot)
      · intro hi
        by_cases hiS : i ∈ S
        · rcases mem_suppSub.mp hiS with ⟨x, hxU, hxi⟩
          exact mem_suppSub.mpr ⟨x, hUE hxU, hxi⟩
        · let a0 : exitsS n S' := ⟨runExit n S' hS'u i, runExit_mem_exits n S' hS'u hi⟩
          let x1 := embedRuns n S' hS'u (Pi.single a0 1)
          rcases hsurj (parityMap n x1) with ⟨cS, hcS⟩
          let yS := embedRuns n S hS_ne_u cS
          have hyS_range : yS ∈ LinearMap.range (embedRuns n S' hS'u) := by
            have hyS' := (mem_range_embedRuns_iff n S hS_ne_u yS).mp ⟨cS, rfl⟩
            rw [mem_range_embedRuns_iff]
            refine ⟨fun j hj => hyS'.1 j (fun hm => hj (hp.1 hm)), fun j hj hnj => ?_⟩
            by_cases hjS : j ∈ S
            · exact hyS'.2 j hjS (hp.2.2.1 j hjS hnj)
            · have hnjS : nextC n j ∉ S := fun hm => hjS (hp.2.2.2.1 j hj hm)
              rw [hyS'.1 j hjS, hyS'.1 (nextC n j) hnjS]
          rcases hyS_range with ⟨cS', hcS'⟩
          have hx1_mem : x1 + yS ∈ E := by
            refine Submodule.mem_map.mpr ⟨Pi.single a0 1 + cS', ?_, by rw [map_add, hcS']⟩
            rw [LinearMap.mem_ker, LinearMap.comp_apply, map_add, map_add, hcS']
            dsimp only [LinearMap.comp_apply] at hcS
            have hz2 : ∀ z : ZMod 2, z + z = 0 := by decide
            funext b; simp only [Pi.add_apply, Pi.zero_apply]
            have hcb := congrFun hcS b
            rw [hcb]; exact hz2 _
          have hyS_i : yS i = 0 := ((mem_range_embedRuns_iff n S hS_ne_u yS).mp ⟨cS, rfl⟩).1 i hiS
          have hx1_i : x1 i = 1 := by
            dsimp only [x1, embedRuns, LinearMap.coe_mk, AddHom.coe_mk]
            rw [dif_pos hi, Pi.single_eq_same]
          refine mem_suppSub.mpr ⟨x1 + yS, hx1_mem, ?_⟩
          simp only [Pi.add_apply, hx1_i, hyS_i, add_zero]
          exact one_ne_zero
    have hfr : Module.finrank (ZMod 2) E = m + (∑ a : exitsS n S, runsL (gapS n S a.1 - 2) (cfg a)) - 4 := by
      have hinj := embedRuns_injective n S' hS'u
      have heq1 : Module.finrank (ZMod 2) E = Module.finrank (ZMod 2) (LinearMap.ker ((parityMap n).comp (embedRuns n S' hS'u))) :=
        (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (embedRuns n S' hS'u) hinj _)).symm
      have hr4 := (hrank4 S' hS'u hp.1 hp.2.2.1 hp.2.2.2.1).2.1
      have hex := hexits_decomp S' hp.1 hp.2.2.1 hp.2.2.2.1
      have hsum_proj : ∑ a : exitsS n S, runsL (gapS n S a.1 - 2) (projInt a S') =
          ∑ a : exitsS n S, runsL (gapS n S a.1 - 2) (cfg a) :=
        Finset.sum_congr rfl fun a _ => by rw [hp.2.2.2.2 a]
      rw [heq1, hr4, hex, hsum_proj]
    refine ⟨?_, hsuppE, hfr⟩
    dsimp only [hosts, spaces]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hE_good, hUE⟩
  have htop_le : ∀ E ∈ hosts, Module.finrank (ZMod 2) E ≤ targetDim := by
    intro E hE
    have hst := hhost_struct E hE
    let S' := suppSub n E
    have hE_good := (Finset.mem_filter.mp (Finset.mem_filter.mp hE).1).2
    have hE_le : E ≤ (LinearMap.ker ((parityMap n).comp (embedRuns n S' hst.2.1))).map (embedRuns n S' hst.2.1) := by
      intro x hxE
      have hx_rng : x ∈ LinearMap.range (embedRuns n S' hst.2.1) := by
        rw [mem_range_embedRuns_iff]
        refine ⟨fun i hi => by by_contra hnz; exact hi (mem_suppSub.mpr ⟨x, hxE, hnz⟩),
          fun i hi hni => goodSub_adj_eq n E hE_good hi hni x hxE⟩
      rcases hx_rng with ⟨c, hc⟩
      refine Submodule.mem_map.mpr ⟨c, ?_, hc⟩
      rw [LinearMap.mem_ker]; funext b
      dsimp only [LinearMap.comp_apply]; rw [hc]; exact hE_good.1 x hxE b
    have hle1 := Submodule.finrank_mono hE_le
    have hmeq : Module.finrank (ZMod 2) ((LinearMap.ker ((parityMap n).comp (embedRuns n S' hst.2.1))).map (embedRuns n S' hst.2.1)) =
        Module.finrank (ZMod 2) (LinearMap.ker ((parityMap n).comp (embedRuns n S' hst.2.1))) :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (embedRuns n S' hst.2.1) (embedRuns_injective n S' hst.2.1) _)).symm
    rw [hmeq,
      (hrank4 S' hst.2.1 hst.1 hst.2.2.1 hst.2.2.2).2.1,
      hexits_decomp S' hst.1 hst.2.2.1 hst.2.2.2] at hle1
    have hsum_le : ∑ a : exitsS n S, runsL (gapS n S a.1 - 2) (projInt a S') ≤
        ∑ a ∈ exitsS n S, (gapS n S a - 1) / 2 := by
      rw [← Finset.sum_coe_sort (exitsS n S)]
      refine Finset.sum_le_sum fun a _ => ?_
      have h1 := runsL_le (gapS n S a.1 - 2) (projInt a S')
      have hgp := gapS_pos_of_exit n S a.2
      have h2 : (gapS n S a.1 - 2 + 1) / 2 = (gapS n S a.1 - 1) / 2 := by
        by_cases hg1 : gapS n S a.1 = 1
        · rw [hg1]
        · congr 1; omega
      omega
    dsimp only [targetDim]; omega
  have hex_max_cfg : ∃ cfg : (∀ a : exitsS n S, Finset (Fin (gapS n S a.1 - 2))),
      ∀ a : exitsS n S, runsL (gapS n S a.1 - 2) (cfg a) = (gapS n S a.1 - 1) / 2 := by
    have h1 : ∀ a : exitsS n S, ∃ A : Finset (Fin (gapS n S a.1 - 2)),
        runsL (gapS n S a.1 - 2) A = (gapS n S a.1 - 1) / 2 := by
      intro a
      have hc := card_max_runsL (gapS n S a.1 - 2)
      have hpos : 0 < ((Finset.univ : Finset (Finset (Fin (gapS n S a.1 - 2)))).filter
          (fun A => runsL (gapS n S a.1 - 2) A = (gapS n S a.1 - 2 + 1) / 2)).card := by
        rw [hc]; split_ifs <;> omega
      rcases Finset.card_pos.mp hpos with ⟨A, hA⟩
      have hgp := gapS_pos_of_exit n S a.2
      have h2 : (gapS n S a.1 - 2 + 1) / 2 = (gapS n S a.1 - 1) / 2 := by
        by_cases hg1 : gapS n S a.1 = 1
        · rw [hg1]
        · congr 1; omega
      exact ⟨A, (Finset.mem_filter.mp hA).2.trans h2⟩
    exact ⟨fun a => Classical.choose (h1 a), fun a => Classical.choose_spec (h1 a)⟩
  have htop_eq : topDim = targetDim := by
    apply le_antisymm
    · exact Finset.sup_le fun E hE => htop_le E hE
    · rcases hex_max_cfg with ⟨cfg, hcfg⟩
      have hb := hbuild_E cfg
      have hle := Finset.le_sup (f := fun E : Submodule (ZMod 2) (Fin n → ZMod 2) => Module.finrank (ZMod 2) E) hb.1
      have hsum : ∑ a : exitsS n S, runsL (gapS n S a.1 - 2) (cfg a) =
          ∑ a ∈ exitsS n S, (gapS n S a - 1) / 2 := by
        rw [← Finset.sum_coe_sort (exitsS n S)]
        exact Finset.sum_congr rfl fun a _ => hcfg a
      rw [hb.2.2, hsum] at hle; exact hle
  let maxCfgs : Finset (∀ a : exitsS n S, Finset (Fin (gapS n S a.1 - 2))) :=
    Fintype.piFinset fun a =>
      (Finset.univ : Finset (Finset (Fin (gapS n S a.1 - 2)))).filter
        (fun A => runsL (gapS n S a.1 - 2) A = (gapS n S a.1 - 1) / 2)
  have hcard_cfgs : maxCfgs.card = ∏ a ∈ exitsS n S, factorG (gapS n S a) := by
    rw [Fintype.card_piFinset, ← Finset.prod_coe_sort (exitsS n S)]
    refine Finset.prod_congr rfl fun a _ => ?_
    have hgp := gapS_pos_of_exit n S a.2
    have h2 : (gapS n S a.1 - 2 + 1) / 2 = (gapS n S a.1 - 1) / 2 := by
      by_cases hg1 : gapS n S a.1 = 1
      · rw [hg1]
      · congr 1; omega
    have hc := card_max_runsL (gapS n S a.1 - 2)
    rw [h2] at hc; exact hc
  rw [← hcard_cfgs]
  refine Finset.card_bij (fun (E : Submodule (ZMod 2) (Fin n → ZMod 2)) _ => fun a => projInt a (suppSub n E)) ?_ ?_ ?_
  · intro E hE
    have hE' : E ∈ hosts ∧ Module.finrank (ZMod 2) E = topDim := by simpa using hE
    have hEh := hE'.1
    have hEdim := hE'.2
    rw [htop_eq] at hEdim
    have hst := hhost_struct E hEh
    let S' := suppSub n E
    have hE_good := (Finset.mem_filter.mp (Finset.mem_filter.mp hEh).1).2
    have hE_le : E ≤ (LinearMap.ker ((parityMap n).comp (embedRuns n S' hst.2.1))).map (embedRuns n S' hst.2.1) := by
      intro x hxE
      have hx_rng : x ∈ LinearMap.range (embedRuns n S' hst.2.1) := by
        rw [mem_range_embedRuns_iff]
        refine ⟨fun i hi => by by_contra hnz; exact hi (mem_suppSub.mpr ⟨x, hxE, hnz⟩),
          fun i hi hni => goodSub_adj_eq n E hE_good hi hni x hxE⟩
      rcases hx_rng with ⟨c, hc⟩
      refine Submodule.mem_map.mpr ⟨c, ?_, hc⟩
      rw [LinearMap.mem_ker]; funext b
      dsimp only [LinearMap.comp_apply]; rw [hc]; exact hE_good.1 x hxE b
    have hle1 := Submodule.finrank_mono hE_le
    have hr4 := hrank4 S' hst.2.1 hst.1 hst.2.2.1 hst.2.2.2
    have hmeq : Module.finrank (ZMod 2) ((LinearMap.ker ((parityMap n).comp (embedRuns n S' hst.2.1))).map (embedRuns n S' hst.2.1)) =
        Module.finrank (ZMod 2) (LinearMap.ker ((parityMap n).comp (embedRuns n S' hst.2.1))) :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (embedRuns n S' hst.2.1) (embedRuns_injective n S' hst.2.1) _)).symm
    rw [hmeq, hr4.2.1, hexits_decomp S' hst.1 hst.2.2.1 hst.2.2.2] at hle1
    have hge4 : 4 ≤ m + ∑ a : exitsS n S, runsL (gapS n S a.1 - 2) (projInt a S') := by
      rw [← hexits_decomp S' hst.1 hst.2.2.1 hst.2.2.2]; exact hr4.2.2
    have hle_each : ∀ a : exitsS n S, runsL (gapS n S a.1 - 2) (projInt a S') ≤ (gapS n S a.1 - 1) / 2 := by
      intro a
      have h1 := runsL_le (gapS n S a.1 - 2) (projInt a S')
      have hgp := gapS_pos_of_exit n S a.2
      have h2 : (gapS n S a.1 - 2 + 1) / 2 = (gapS n S a.1 - 1) / 2 := by
        by_cases hg1 : gapS n S a.1 = 1
        · rw [hg1]
        · congr 1; omega
      omega
    have hsum_eq : ∑ a : exitsS n S, runsL (gapS n S a.1 - 2) (projInt a S') =
        ∑ a : exitsS n S, (gapS n S a.1 - 1) / 2 := by
      apply le_antisymm
      · exact Finset.sum_le_sum fun a _ => hle_each a
      · have hsum_coe : ∑ a : exitsS n S, (gapS n S a.1 - 1) / 2 = ∑ a ∈ exitsS n S, (gapS n S a - 1) / 2 :=
          Finset.sum_coe_sort (exitsS n S) (fun a => (gapS n S a - 1) / 2)
        dsimp only [targetDim] at hEdim
        omega
    rw [Fintype.mem_piFinset]
    intro a
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    by_contra hne
    have hlt : runsL (gapS n S a.1 - 2) (projInt a S') < (gapS n S a.1 - 1) / 2 :=
      lt_of_le_of_ne (hle_each a) hne
    have hsum_lt := Finset.sum_lt_sum (fun b _ => hle_each b) ⟨a, Finset.mem_univ _, hlt⟩
    omega
  · intro E1 hE1 E2 hE2 hproj_eq
    have hsupp_eq : suppSub n E1 = suppSub n E2 := by
      have hst1 := hhost_struct E1 (show E1 ∈ hosts ∧ Module.finrank (ZMod 2) E1 = topDim by simpa using hE1).1
      have hst2 := hhost_struct E2 (show E2 ∈ hosts ∧ Module.finrank (ZMod 2) E2 = topDim by simpa using hE2).1
      ext x
      by_cases hxS : x ∈ S
      · simp [hst1.1 hxS, hst2.1 hxS]
      · constructor
        · intro hx1
          have hpx : prevC n x ∉ S := fun hm => hxS (by rw [← nextC_prevC n x]; exact hst1.2.2.1 (prevC n x) hm (by rwa [nextC_prevC]))
          have hnx : nextC n x ∉ S := fun hm => hxS (hst1.2.2.2 x hx1 hm)
          rcases mem_gapInt_of_not_mem_and_not_adj n S hS_ne_e hS_ne_u hxS hpx hnx with ⟨a, ha, hxa⟩
          rcases Finset.mem_image.mp hxa with ⟨k, hk, rfl⟩
          let k' : Fin (gapS n S a - 2) := ⟨k, Finset.mem_range.mp hk⟩
          have h1 : k' ∈ projInt ⟨a, ha⟩ (suppSub n E1) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx1⟩
          have h2 : k' ∈ projInt ⟨a, ha⟩ (suppSub n E2) := by rw [← congrFun hproj_eq ⟨a, ha⟩]; exact h1
          exact (Finset.mem_filter.mp h2).2
        · intro hx2
          have hpx : prevC n x ∉ S := fun hm => hxS (by rw [← nextC_prevC n x]; exact hst2.2.2.1 (prevC n x) hm (by rwa [nextC_prevC]))
          have hnx : nextC n x ∉ S := fun hm => hxS (hst2.2.2.2 x hx2 hm)
          rcases mem_gapInt_of_not_mem_and_not_adj n S hS_ne_e hS_ne_u hxS hpx hnx with ⟨a, ha, hxa⟩
          rcases Finset.mem_image.mp hxa with ⟨k, hk, rfl⟩
          let k' : Fin (gapS n S a - 2) := ⟨k, Finset.mem_range.mp hk⟩
          have h2 : k' ∈ projInt ⟨a, ha⟩ (suppSub n E2) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx2⟩
          have h1 : k' ∈ projInt ⟨a, ha⟩ (suppSub n E1) := by rw [congrFun hproj_eq ⟨a, ha⟩]; exact h2
          exact (Finset.mem_filter.mp h1).2
    have hE_eq_max : ∀ (E : Submodule (ZMod 2) (Fin n → ZMod 2))
        (hEh : E ∈ hosts) (hEdim : Module.finrank (ZMod 2) E = topDim),
        let hst := hhost_struct E hEh
        E = (LinearMap.ker ((parityMap n).comp (embedRuns n (suppSub n E) hst.2.1))).map
          (embedRuns n (suppSub n E) hst.2.1) := by
      intro E hEh hEdim
      have hst := hhost_struct E hEh
      have hE_good := (Finset.mem_filter.mp (Finset.mem_filter.mp hEh).1).2
      let M := (LinearMap.ker ((parityMap n).comp (embedRuns n (suppSub n E) hst.2.1))).map
        (embedRuns n (suppSub n E) hst.2.1)
      have hle : E ≤ M := by
        intro x hxE
        have hx_rng : x ∈ LinearMap.range (embedRuns n (suppSub n E) hst.2.1) := by
          rw [mem_range_embedRuns_iff]
          refine ⟨fun i hi => by by_contra hnz; exact hi (mem_suppSub.mpr ⟨x, hxE, hnz⟩),
            fun i hi hni => goodSub_adj_eq n E hE_good hi hni x hxE⟩
        rcases hx_rng with ⟨c, hc⟩
        refine Submodule.mem_map.mpr ⟨c, ?_, hc⟩
        rw [LinearMap.mem_ker]; funext b
        dsimp only [LinearMap.comp_apply]; rw [hc]; exact hE_good.1 x hxE b
      have hM_host : M ∈ hosts := by
        dsimp only [hosts, spaces]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, (show goodSub n E ∧ U ≤ E by simpa [hosts, spaces] using hEh).2.trans hle⟩
        refine ⟨fun x hx b => ?_, fun x hx y hy i => ?_⟩
        · rcases Submodule.mem_map.mp hx with ⟨c, hc, rfl⟩; exact congrFun (LinearMap.mem_ker.mp hc) b
        · rcases Submodule.mem_map.mp hx with ⟨cx, _, rfl⟩
          rcases Submodule.mem_map.mp hy with ⟨cy, _, rfl⟩
          have hx' := (mem_range_embedRuns_iff n (suppSub n E) hst.2.1 _).mp ⟨cx, rfl⟩
          have hy' := (mem_range_embedRuns_iff n (suppSub n E) hst.2.1 _).mp ⟨cy, rfl⟩
          by_cases h1 : i ∈ suppSub n E
          · by_cases h2 : nextC n i ∈ suppSub n E
            · rw [hx'.2 i h1 h2, hy'.2 i h1 h2]
            · rw [hx'.1 _ h2, hy'.1 _ h2, mul_zero, zero_mul]
          · rw [hx'.1 _ h1, hy'.1 _ h1, zero_mul, mul_zero]
      have hdim_eq : Module.finrank (ZMod 2) E = Module.finrank (ZMod 2) M := by
        apply le_antisymm (Submodule.finrank_mono hle)
        rw [hEdim]
        exact Finset.le_sup (f := fun X : Submodule (ZMod 2) (Fin n → ZMod 2) => Module.finrank (ZMod 2) X) hM_host
      exact Submodule.eq_of_le_of_finrank_eq hle hdim_eq
    have hE1' : E1 ∈ hosts ∧ Module.finrank (ZMod 2) E1 = topDim := by simpa using hE1
    have hE2' : E2 ∈ hosts ∧ Module.finrank (ZMod 2) E2 = topDim := by simpa using hE2
    have h1 := hE_eq_max E1 hE1'.1 hE1'.2
    have h2 := hE_eq_max E2 hE2'.1 hE2'.2
    rw [h1, h2]
    generalize_proofs hne1 hne2
    revert hne1 hne2
    rw [hsupp_eq]
    intros
    rfl
  · intro cfg hcfg
    have hmem := Fintype.mem_piFinset.mp hcfg
    have hb := hbuild_E cfg
    have hp := hbuild_props cfg
    have hsum : ∑ a : exitsS n S, runsL (gapS n S a.1 - 2) (cfg a) =
        ∑ a ∈ exitsS n S, (gapS n S a - 1) / 2 := by
      rw [← Finset.sum_coe_sort (exitsS n S)]
      exact Finset.sum_congr rfl fun a _ => (Finset.mem_filter.mp (hmem a)).2
    refine ⟨_, by simp only [Finset.mem_filter]; exact ⟨hb.1, by rw [hb.2.2, hsum, htop_eq]⟩, ?_⟩
    funext a; rw [hb.2.1, hp.2.2.2.2 a]


private noncomputable def badRuns (n : ℕ) (S : Finset (Fin n)) (hne : S ≠ Finset.univ)
    (α : Fin 4 → ZMod 2) : ℕ :=
  ((Finset.univ : Finset (exitsS n S)).filter (fun a => (∑ b : Fin 4, α b * runSig n S hne a b) ≠ 0)).card

private lemma surj_of_badRuns_pos (n : ℕ) (S : Finset (Fin n)) (hne : S ≠ Finset.univ)
    (hbad : ∀ α : Fin 4 → ZMod 2, α ≠ 0 → 1 ≤ badRuns n S hne α) :
    Function.Surjective ((parityMap n).comp (embedRuns n S hne)) := by
  classical
  let f := (parityMap n).comp (embedRuns n S hne)
  rw [← LinearMap.range_eq_top]
  by_contra hne_top
  have hlt : Module.finrank (ZMod 2) (LinearMap.range f) < Module.finrank (ZMod 2) (Fin 4 → ZMod 2) :=
    Submodule.finrank_lt hne_top
  let R := LinearMap.range f
  have hq_pos : 0 < Module.finrank (ZMod 2) ((Fin 4 → ZMod 2) ⧸ R) := by
    have hadd := Submodule.finrank_quotient_add_finrank R
    have hlt' : Module.finrank (ZMod 2) R < Module.finrank (ZMod 2) (Fin 4 → ZMod 2) := hlt
    omega
  have hq_ne : Nontrivial ((Fin 4 → ZMod 2) ⧸ R) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have : Module.finrank (ZMod 2) ((Fin 4 → ZMod 2) ⧸ R) = 0 := Module.finrank_zero_of_subsingleton
    omega
  rcases exists_ne (0 : (Fin 4 → ZMod 2) ⧸ R) with ⟨q0, hq0⟩
  have hex_dual : ∃ φ : ((Fin 4 → ZMod 2) ⧸ R) →ₗ[ZMod 2] ZMod 2, φ q0 ≠ 0 := by
    let b := Module.Basis.ofVectorSpace (ZMod 2) ((Fin 4 → ZMod 2) ⧸ R)
    by_contra hall; push_neg at hall
    have hrepr : b.repr q0 = 0 := by
      ext i
      exact hall ((Finsupp.lapply i).comp b.repr.toLinearMap)
    exact hq0 (b.repr.injective (by rwa [map_zero]))
  rcases hex_dual with ⟨φ, hφ⟩
  let ψ : (Fin 4 → ZMod 2) →ₗ[ZMod 2] ZMod 2 := φ.comp (Submodule.mkQ R)
  let α : Fin 4 → ZMod 2 := fun b => ψ (Pi.single b 1)
  have hψ_eq : ∀ y : Fin 4 → ZMod 2, ψ y = ∑ b : Fin 4, α b * y b := by
    intro y
    have hy : y = ∑ b : Fin 4, y b • Pi.single b (1 : ZMod 2) := by
      funext b; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hy]
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => by rw [map_smul, smul_eq_mul, mul_comm]
  have hα_nz : α ≠ 0 := by
    intro h0
    rcases Submodule.Quotient.mk_surjective R q0 with ⟨y0, rfl⟩
    have : ψ y0 = 0 := by rw [hψ_eq, h0]; simp
    exact hφ this
  have hpos := hbad α hα_nz
  rcases Finset.card_pos.mp hpos with ⟨a, ha⟩
  have hnz : (∑ b : Fin 4, α b * runSig n S hne a b) ≠ 0 := (Finset.mem_filter.mp ha).2
  have hmem : (fun b => runSig n S hne a b) ∈ R := ⟨Pi.single a 1, rfl⟩
  have hzero : ψ (fun b => runSig n S hne a b) = 0 := by
    dsimp only [ψ, LinearMap.comp_apply]
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero R).mpr hmem, map_zero]
  rw [hψ_eq] at hzero
  exact hnz hzero

private lemma mixed_of_badRuns_pos (n : ℕ) (S : Finset (Fin n)) (hne : S ≠ Finset.univ)
    (hbad : ∀ α : Fin 4 → ZMod 2, α ≠ 0 → 1 ≤ badRuns n S hne α) :
    ∀ b : Fin 2, ∃ i ∈ S, i.val % 2 = b.val := by
  intro b
  fin_cases b
  · let α : Fin 4 → ZMod 2 := fun k => if k = 0 then 1 else 0
    have hα : α ≠ 0 := fun h => by have := congrFun h 0; simp [α] at this
    rcases Finset.card_pos.mp (hbad α hα) with ⟨a, ha⟩
    have hnz : (∑ k : Fin 4, α k * runSig n S hne a k) ≠ 0 := (Finset.mem_filter.mp ha).2
    have hsig : runSig n S hne a 0 ≠ 0 := by
      simpa [α, Finset.sum_ite_eq'] using hnz
    dsimp only [runSig, parityMap, LinearMap.coe_mk, AddHom.coe_mk] at hsig
    by_contra hall; push_neg at hall
    apply hsig
    refine Finset.sum_eq_zero fun i _ => ?_
    dsimp only [embedRuns, LinearMap.coe_mk, AddHom.coe_mk]
    by_cases hi : i ∈ S
    · have hodd := hall i hi
      have hh0 : hMat n i 0 = 0 := by dsimp only [hMat]; rw [if_neg]; intro hc; exact hodd hc.1
      rw [hh0, zero_mul]
    · rw [dif_neg hi, mul_zero]
  · let α : Fin 4 → ZMod 2 := fun k => if k = 2 then 1 else 0
    have hα : α ≠ 0 := fun h => by have := congrFun h 2; simp [α] at this
    rcases Finset.card_pos.mp (hbad α hα) with ⟨a, ha⟩
    have hnz : (∑ k : Fin 4, α k * runSig n S hne a k) ≠ 0 := (Finset.mem_filter.mp ha).2
    have hsig : runSig n S hne a 2 ≠ 0 := by
      simpa [α, Finset.sum_ite_eq'] using hnz
    dsimp only [runSig, parityMap, LinearMap.coe_mk, AddHom.coe_mk] at hsig
    by_contra hall; push_neg at hall
    apply hsig
    refine Finset.sum_eq_zero fun i _ => ?_
    dsimp only [embedRuns, LinearMap.coe_mk, AddHom.coe_mk]
    by_cases hi : i ∈ S
    · have hev := hall i hi
      have hh2 : hMat n i 2 = 0 := by dsimp only [hMat]; rw [if_neg]; intro hc; exact hev hc.1
      rw [hh2, zero_mul]
    · rw [dif_neg hi, mul_zero]

private lemma finite_gl (d : ℕ) : Finite ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)) :=
  Finite.of_injective (fun g => (g : (Fin d → ZMod 2) → (Fin d → ZMod 2)))
    (fun _ _ h => LinearEquiv.ext (congrFun h))

private noncomputable def glCard (d : ℕ) : ℕ :=
  letI : Finite ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)) := finite_gl d
  letI : Fintype ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)) := Fintype.ofFinite _
  Fintype.card ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2))

private lemma glCard_pos (d : ℕ) : 0 < glCard d := by
  letI : Finite ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)) := finite_gl d
  letI : Fintype ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)) := Fintype.ofFinite _
  haveI : Nonempty ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)) := ⟨LinearEquiv.refl (ZMod 2) _⟩
  exact Fintype.card_pos

private noncomputable def phiSet (n d : ℕ) (S : Finset (Fin n)) (hne : S ≠ Finset.univ) :
    Finset (exitsS n S → (Fin d → ZMod 2)) :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  Finset.univ.filter fun φ =>
    (∀ a, φ a ≠ 0) ∧
    (∀ b : Fin 4, (∑ a : exitsS n S, runSig n S hne a b • φ a) = 0) ∧
    Submodule.span (ZMod 2) (Set.range φ) = ⊤

private lemma mem_phiSet {n d : ℕ} {S : Finset (Fin n)} {hne : S ≠ Finset.univ}
    {φ : exitsS n S → (Fin d → ZMod 2)} :
    φ ∈ phiSet n d S hne ↔
      (∀ a, φ a ≠ 0) ∧
      (∀ b : Fin 4, (∑ a : exitsS n S, runSig n S hne a b • φ a) = 0) ∧
      Submodule.span (ZMod 2) (Set.range φ) = ⊤ := by
  dsimp only [phiSet]; simp

private noncomputable def phiSet0 (n d : ℕ) (S : Finset (Fin n)) (hne : S ≠ Finset.univ) :
    Finset (exitsS n S → (Fin d → ZMod 2)) :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  Finset.univ.filter fun φ =>
    (∀ a, φ a ≠ 0) ∧
    (∀ b : Fin 4, (∑ a : exitsS n S, runSig n S hne a b • φ a) = 0)

private lemma mem_phiSet0 {n d : ℕ} {S : Finset (Fin n)} {hne : S ≠ Finset.univ}
    {φ : exitsS n S → (Fin d → ZMod 2)} :
    φ ∈ phiSet0 n d S hne ↔
      (∀ a, φ a ≠ 0) ∧
      (∀ b : Fin 4, (∑ a : exitsS n S, runSig n S hne a b • φ a) = 0) := by
  dsimp only [phiSet0]; simp

set_option maxHeartbeats 800000 in
private lemma card_spaces_supp_mul_gl (n d : ℕ) (S : Finset (Fin n)) (hne : S ≠ Finset.univ) :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    letI : Fintype (Submodule (ZMod 2) (Fin n → ZMod 2)) := Fintype.ofFinite _
    let fiber := (Finset.univ : Finset (Submodule (ZMod 2) (Fin n → ZMod 2))).filter
      (fun U => goodSub n U ∧ Module.finrank (ZMod 2) U = d ∧ suppSub n U = S)
    fiber.card * glCard d = (phiSet n d S hne).card := by
  classical
  intro fiber
  let toSub : (exitsS n S → (Fin d → ZMod 2)) → Submodule (ZMod 2) (Fin n → ZMod 2) := fun φ =>
    LinearMap.range ((embedRuns n S hne).comp
      ({ toFun := fun v a => ∑ j : Fin d, v j * φ a j
         map_add' := fun v1 v2 => by funext a; simp [add_mul, Finset.sum_add_distrib]
         map_smul' := fun r v => by
           funext a; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
           refine Finset.sum_congr rfl fun j _ => by ring } : (Fin d → ZMod 2) →ₗ[ZMod 2] (exitsS n S → ZMod 2)))
  have hmap_mem : ∀ φ ∈ phiSet n d S hne, toSub φ ∈ fiber := by
    intro φ hφ
    rcases mem_phiSet.mp hφ with ⟨hφ_nz, hφ_par, hφ_span⟩
    let Lφ : (Fin d → ZMod 2) →ₗ[ZMod 2] (exitsS n S → ZMod 2) :=
      { toFun := fun v a => ∑ j : Fin d, v j * φ a j
        map_add' := fun v1 v2 => by funext a; simp [add_mul, Finset.sum_add_distrib]
        map_smul' := fun r v => by
          funext a; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring }
    have hLφ_inj : Function.Injective Lφ := by
      rw [injective_iff_map_eq_zero]
      intro v hv
      have hdot : ∀ w ∈ Submodule.span (ZMod 2) (Set.range φ), (∑ j : Fin d, v j * w j) = 0 := by
        intro w hw
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
        · rintro _ ⟨a, rfl⟩; exact congrFun hv a
        · simp
        · intro x y _ _ hx hy; simp [mul_add, Finset.sum_add_distrib, hx, hy]
        · intro r x _ hx
          simp only [Pi.smul_apply, smul_eq_mul]
          calc ∑ j : Fin d, v j * (r * x j) = r * ∑ j : Fin d, v j * x j := by
                rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
            _ = 0 := by rw [hx, mul_zero]
      funext j0
      have hmem : (Pi.single j0 (1 : ZMod 2) : Fin d → ZMod 2) ∈ Submodule.span (ZMod 2) (Set.range φ) := by
        rw [hφ_span]; trivial
      have h0 := hdot _ hmem
      simpa [Pi.single_apply] using h0
    have hcomp_inj : Function.Injective ((embedRuns n S hne).comp Lφ) :=
      (embedRuns_injective n S hne).comp hLφ_inj
    have hgood : goodSub n (toSub φ) := by
      refine ⟨fun x hx b => ?_, fun x hx y hy i => ?_⟩
      · rcases hx with ⟨v, rfl⟩
        change parityMap n (embedRuns n S hne (Lφ v)) b = 0
        rw [parityMap_embedRuns]
        calc ∑ a : exitsS n S, runSig n S hne a b * (∑ j : Fin d, v j * φ a j)
            = ∑ j : Fin d, v j * (∑ a : exitsS n S, runSig n S hne a b * φ a j) := by
                simp_rw [Finset.mul_sum]
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => by ring
          _ = ∑ j : Fin d, v j * 0 := by
                refine Finset.sum_congr rfl fun j _ => ?_
                have hj := congrFun (hφ_par b) j
                simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj
                rw [hj]
          _ = 0 := by simp
      · rcases hx with ⟨vx, rfl⟩
        rcases hy with ⟨vy, rfl⟩
        have hx' := (mem_range_embedRuns_iff n S hne _).mp ⟨Lφ vx, rfl⟩
        have hy' := (mem_range_embedRuns_iff n S hne _).mp ⟨Lφ vy, rfl⟩
        change embedRuns n S hne (Lφ vx) i * embedRuns n S hne (Lφ vy) (nextC n i) =
          embedRuns n S hne (Lφ vx) (nextC n i) * embedRuns n S hne (Lφ vy) i
        by_cases h1 : i ∈ S
        · by_cases h2 : nextC n i ∈ S
          · rw [hx'.2 i h1 h2, hy'.2 i h1 h2]
          · rw [hx'.1 _ h2, hy'.1 _ h2, mul_zero, zero_mul]
        · rw [hx'.1 _ h1, hy'.1 _ h1, zero_mul, mul_zero]
    have hdim : Module.finrank (ZMod 2) (toSub φ) = d := by
      dsimp only [toSub]
      rw [LinearMap.finrank_range_of_inj hcomp_inj, Module.finrank_fin_fun]
    have hsupp : suppSub n (toSub φ) = S := by
      ext i
      constructor
      · intro hi
        rcases mem_suppSub.mp hi with ⟨x, ⟨v, rfl⟩, hxi⟩
        by_contra hnot
        exact hxi (((mem_range_embedRuns_iff n S hne _).mp ⟨Lφ v, rfl⟩).1 i hnot)
      · intro hi
        let a : exitsS n S := ⟨runExit n S hne i, runExit_mem_exits n S hne hi⟩
        have hnz : ∃ j : Fin d, φ a j ≠ 0 := by
          by_contra hall; push_neg at hall; exact hφ_nz a (funext hall)
        rcases hnz with ⟨j0, hj0⟩
        refine mem_suppSub.mpr ⟨((embedRuns n S hne).comp Lφ) (Pi.single j0 1), ⟨Pi.single j0 1, rfl⟩, ?_⟩
        dsimp only [LinearMap.comp_apply, embedRuns, LinearMap.coe_mk, AddHom.coe_mk, Lφ]
        rw [dif_pos hi]
        simpa [Pi.single_apply] using hj0
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hgood, hdim, hsupp⟩
  have hfiber_card : ∀ U ∈ fiber, ((phiSet n d S hne).filter (fun φ => toSub φ = U)).card = glCard d := by
    intro U hU
    have hU' : goodSub n U ∧ Module.finrank (ZMod 2) U = d ∧ suppSub n U = S := by
      simpa [fiber] using hU
    rcases hU' with ⟨hU_good, hU_dim, hU_supp⟩
    haveI : Finite ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)) := finite_gl d
    haveI : Fintype ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)) := Fintype.ofFinite _
    let e0 : (Fin d → ZMod 2) ≃ₗ[ZMod 2] U :=
      LinearEquiv.ofFinrankEq (Fin d → ZMod 2) U (by rw [Module.finrank_fin_fun, hU_dim])
    let mkPhi : ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)) → (exitsS n S → (Fin d → ZMod 2)) :=
      fun g a j => (e0 (g (Pi.single j 1))).1 a.1
    have hmk_eq_eval : ∀ (g : (Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)) (v : Fin d → ZMod 2) (i : Fin n),
        embedRuns n S hne (fun a => ∑ j : Fin d, v j * mkPhi g a j) i = (e0 (g v)).1 i := by
      intro g v i
      have hv : v = ∑ j : Fin d, v j • Pi.single j (1 : ZMod 2) := by
        funext j; simp [Finset.sum_apply, Pi.single_apply]
      have hgv : (e0 (g v)).1 = ∑ j : Fin d, v j • (e0 (g (Pi.single j 1))).1 := by
        change (Submodule.subtype U) (e0 (g v)) = ∑ j : Fin d, v j • (Submodule.subtype U) (e0 (g (Pi.single j 1)))
        conv_lhs => rw [hv]
        rw [map_sum, map_sum, map_sum]
        refine Finset.sum_congr rfl fun j _ => by rw [map_smul, map_smul, map_smul]
      have hU_mem : (e0 (g v)).1 ∈ LinearMap.range (embedRuns n S hne) := by
        rw [mem_range_embedRuns_iff]
        refine ⟨fun k hk => by by_contra hnz; exact hk (hU_supp ▸ mem_suppSub.mpr ⟨_, (e0 (g v)).2, hnz⟩),
          fun k hk hnk => goodSub_adj_eq n U hU_good (hU_supp.symm ▸ hk) (hU_supp.symm ▸ hnk) _ (e0 (g v)).2⟩
      have heval_eq : ∀ a : exitsS n S, (∑ j : Fin d, v j * mkPhi g a j) = (e0 (g v)).1 a.1 := fun a => by
        rw [hgv, Finset.sum_apply]
        refine Finset.sum_congr rfl fun j _ => by simp [mkPhi]
      dsimp only [embedRuns, LinearMap.coe_mk, AddHom.coe_mk]
      by_cases hi : i ∈ S
      · rw [dif_pos hi, heval_eq]
        exact (const_on_run_eq_runExit n S hne (e0 (g v)).1 ((mem_range_embedRuns_iff n S hne _).mp hU_mem).2 hi).symm
      · rw [dif_neg hi]
        exact (((mem_range_embedRuns_iff n S hne _).mp hU_mem).1 i hi).symm
    have hbij : ((phiSet n d S hne).filter (fun φ => toSub φ = U)).card =
        (Finset.univ : Finset ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2))).card := by
      symm
      refine Finset.card_bij (fun g _ => mkPhi g) ?_ ?_ ?_
      · intro g _
        have htoSub : toSub (mkPhi g) = U := by
          ext x
          constructor
          · rintro ⟨v, rfl⟩
            have hx : (embedRuns n S hne (fun a => ∑ j : Fin d, v j * mkPhi g a j)) = (e0 (g v)).1 :=
              funext fun i => hmk_eq_eval g v i
            change (embedRuns n S hne (fun a => ∑ j : Fin d, v j * mkPhi g a j)) ∈ U
            rw [hx]; exact (e0 (g v)).2
          · intro hx
            let v := g.symm (e0.symm ⟨x, hx⟩)
            refine ⟨v, ?_⟩
            funext i
            change embedRuns n S hne (fun a => ∑ j : Fin d, v j * mkPhi g a j) i = x i
            rw [hmk_eq_eval g v i]; simp [v]
        have hnz : ∀ a : exitsS n S, mkPhi g a ≠ 0 := by
          intro a h0
          have haS : a.1 ∈ suppSub n U := hU_supp.symm ▸ (Finset.mem_filter.mp a.2).1
          rcases mem_suppSub.mp haS with ⟨x, hxU, hxa⟩
          have hx_in : x ∈ toSub (mkPhi g) := htoSub.symm ▸ hxU
          rcases hx_in with ⟨v, hv⟩
          have hval : x a.1 = 0 := by
            rw [← hv]; dsimp only [LinearMap.comp_apply, embedRuns, LinearMap.coe_mk, AddHom.coe_mk]
            rw [dif_pos (Finset.mem_filter.mp a.2).1]
            have hre : (⟨runExit n S hne a.1, runExit_mem_exits n S hne (Finset.mem_filter.mp a.2).1⟩ : exitsS n S) = a :=
              Subtype.ext (runExit_of_exit n S hne a.2)
            rw [hre]
            refine Finset.sum_eq_zero fun j _ => by simp [congrFun h0 j]
          exact hxa hval
        have hpar : ∀ b : Fin 4, (∑ a : exitsS n S, runSig n S hne a b • mkPhi g a) = 0 := by
          intro b; funext j
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
          have hx := hU_good.1 (e0 (g (Pi.single j 1))).1 (e0 (g (Pi.single j 1))).2 b
          have h1 : (e0 (g (Pi.single j 1))).1 = embedRuns n S hne (fun a => mkPhi g a j) := by
            funext i; rw [← hmk_eq_eval g (Pi.single j 1) i]
            exact congrFun (congrArg (embedRuns n S hne) (by funext a; simp [Pi.single_apply])) i
          have h2 : parityMap n (embedRuns n S hne (fun a => mkPhi g a j)) b = 0 := by
            dsimp only [parityMap, LinearMap.coe_mk, AddHom.coe_mk]; rw [← h1]; exact hx
          rwa [parityMap_embedRuns] at h2
        have hspan : Submodule.span (ZMod 2) (Set.range (mkPhi g)) = ⊤ := by
          by_contra hne_top
          have hlt : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (mkPhi g))) < d := by
            have := Submodule.finrank_lt hne_top; rwa [Module.finrank_fin_fun] at this
          let K := Submodule.span (ZMod 2) (Set.range (mkPhi g))
          have hq_pos : 0 < Module.finrank (ZMod 2) ((Fin d → ZMod 2) ⧸ K) := by
            have hadd := Submodule.finrank_quotient_add_finrank K
            rw [Module.finrank_fin_fun] at hadd
            have hlt' : Module.finrank (ZMod 2) K < d := hlt
            omega
          have hq_nt : Nontrivial ((Fin d → ZMod 2) ⧸ K) := by
            by_contra hnt; rw [not_nontrivial_iff_subsingleton] at hnt
            have := Module.finrank_zero_of_subsingleton (R := ZMod 2) (M := (Fin d → ZMod 2) ⧸ K); omega
          rcases exists_ne (0 : (Fin d → ZMod 2) ⧸ K) with ⟨q0, hq0⟩
          have hex_d : ∃ φ : ((Fin d → ZMod 2) ⧸ K) →ₗ[ZMod 2] ZMod 2, φ q0 ≠ 0 := by
            let b := Module.Basis.ofVectorSpace (ZMod 2) ((Fin d → ZMod 2) ⧸ K)
            by_contra hall; push_neg at hall
            exact hq0 (b.repr.injective (by rw [map_zero]; ext i; exact hall ((Finsupp.lapply i).comp b.repr.toLinearMap)))
          rcases hex_d with ⟨ψ0, hψ0⟩
          let ψ := ψ0.comp (Submodule.mkQ K)
          let v : Fin d → ZMod 2 := fun j => ψ (Pi.single j 1)
          have hv_nz : v ≠ 0 := by
            intro h0; rcases Submodule.Quotient.mk_surjective K q0 with ⟨w0, rfl⟩
            apply hψ0; change ψ w0 = 0
            have hw : w0 = ∑ j : Fin d, w0 j • Pi.single j (1 : ZMod 2) := by
              funext j; simp [Finset.sum_apply, Pi.single_apply]
            conv_lhs => rw [hw]
            rw [map_sum]
            refine Finset.sum_eq_zero fun j _ => by rw [map_smul, show ψ (Pi.single j 1) = 0 from congrFun h0 j, smul_zero]
          have hzero : (e0 (g v)).1 = 0 := by
            funext i; rw [← hmk_eq_eval g v i]
            have hvan : (fun a : exitsS n S => ∑ j : Fin d, v j * mkPhi g a j) = 0 := by
              funext a
              have hmem : mkPhi g a ∈ K := Submodule.subset_span ⟨a, rfl⟩
              have hz : ψ (mkPhi g a) = 0 := by
                dsimp only [ψ, LinearMap.comp_apply]; rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero K).mpr hmem, map_zero]
              have hrepr : mkPhi g a = ∑ j : Fin d, mkPhi g a j • Pi.single j (1 : ZMod 2) := by
                funext j; simp [Finset.sum_apply, Pi.single_apply]
              conv_lhs at hz => rw [hrepr]
              rw [map_sum] at hz
              simpa [v, map_smul, smul_eq_mul, mul_comm] using hz
            rw [hvan, map_zero]
          have hgv0 : g v = 0 := e0.injective (Subtype.ext (by simpa using hzero))
          exact hv_nz (g.injective (hgv0.trans (map_zero g).symm))
        exact Finset.mem_filter.mpr ⟨mem_phiSet.mpr ⟨hnz, hpar, hspan⟩, htoSub⟩
      · intro g1 _ g2 _ heq
        ext v j
        have h1 : (e0 (g1 v)).1 = (e0 (g2 v)).1 := by
          funext i; rw [← hmk_eq_eval g1 v i, ← hmk_eq_eval g2 v i, heq]
        have h2 : g1 v = g2 v := e0.injective (Subtype.ext h1)
        exact congrFun h2 j
      · intro φ hφ
        have hφ_in := (Finset.mem_filter.mp hφ).1
        have htoU := (Finset.mem_filter.mp hφ).2
        rcases mem_phiSet.mp hφ_in with ⟨_, _, hφ_span⟩
        let Lφ : (Fin d → ZMod 2) →ₗ[ZMod 2] (exitsS n S → ZMod 2) :=
          { toFun := fun v a => ∑ j : Fin d, v j * φ a j
            map_add' := fun v1 v2 => by funext a; simp [add_mul, Finset.sum_add_distrib]
            map_smul' := fun r v => by
              funext a; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => by ring }
        let fU : (Fin d → ZMod 2) →ₗ[ZMod 2] U :=
          ((embedRuns n S hne).comp Lφ).codRestrict U fun v => htoU ▸ ⟨v, rfl⟩
        have hfU_inj : Function.Injective fU := by
          intro v1 v2 h12
          have h12' : ((embedRuns n S hne).comp Lφ) v1 = ((embedRuns n S hne).comp Lφ) v2 := congrArg Subtype.val h12
          have hL := embedRuns_injective n S hne h12'
          have hv : v1 - v2 = 0 := by
            have hL0 : Lφ (v1 - v2) = 0 := by rw [map_sub, hL, sub_self]
            have hdot : ∀ w ∈ Submodule.span (ZMod 2) (Set.range φ), (∑ j : Fin d, (v1 - v2) j * w j) = 0 := by
              intro w hw
              refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
              · rintro _ ⟨a, rfl⟩; exact congrFun hL0 a
              · simp
              · intro x y _ _ hx hy; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hx, hy, add_zero]
              · intro r x _ hx
                simp only [Pi.smul_apply, smul_eq_mul]
                calc ∑ j : Fin d, (v1 - v2) j * (r * x j) = r * ∑ j : Fin d, (v1 - v2) j * x j := by
                      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
                  _ = 0 := by rw [hx, mul_zero]
            funext j0
            have h0 := hdot (Pi.single j0 1) (by rw [hφ_span]; trivial)
            simpa [Pi.single_apply] using h0
          exact sub_eq_zero.mp hv
        let g : (Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2) :=
          LinearEquiv.ofBijective (e0.symm.toLinearMap.comp fU)
            ((LinearMap.injective_iff_surjective.mp (e0.symm.injective.comp hfU_inj)) |> fun hs => ⟨e0.symm.injective.comp hfU_inj, hs⟩)
        refine ⟨g, Finset.mem_univ _, ?_⟩
        funext a j
        change (e0 (e0.symm (fU (Pi.single j 1)))).1 a.1 = φ a j
        rw [e0.apply_symm_apply]
        change (embedRuns n S hne (Lφ (Pi.single j 1))) a.1 = φ a j
        dsimp only [embedRuns, LinearMap.coe_mk, AddHom.coe_mk, Lφ]
        rw [dif_pos (Finset.mem_filter.mp a.2).1]
        have hre : (⟨runExit n S hne a.1, runExit_mem_exits n S hne (Finset.mem_filter.mp a.2).1⟩ : exitsS n S) = a :=
          Subtype.ext (runExit_of_exit n S hne a.2)
        rw [hre]; simp [Pi.single_apply]
    have hcard_u : (Finset.univ : Finset ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2))).card = glCard d := by
      rw [Finset.card_univ]
      dsimp only [glCard]
      convert rfl
    exact hbij.trans hcard_u
  have hsum := Finset.card_eq_sum_card_fiberwise (f := toSub) (s := phiSet n d S hne) (t := fiber) hmap_mem
  rw [hsum]
  calc fiber.card * glCard d = ∑ _U ∈ fiber, glCard d := by rw [Finset.sum_const, smul_eq_mul]
    _ = ∑ U ∈ fiber, ((phiSet n d S hne).filter (fun φ => toSub φ = U)).card :=
        Finset.sum_congr rfl fun U hU => (hfiber_card U hU).symm

private lemma phiCount_le_pow (n d : ℕ) (S : Finset (Fin n)) (hne : S ≠ Finset.univ) :
    (phiSet n d S hne).card ≤ (2 ^ d - 1) ^ (exitsS n S).card := by
  classical
  let nz := (Finset.univ : Finset (Fin d → ZMod 2)).filter (fun v => v ≠ 0)
  have hnz_card : nz.card = 2 ^ d - 1 := by
    have h1 : nz = Finset.univ.erase 0 := by ext v; simp [nz]
    rw [h1, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hsub : phiSet n d S hne ⊆ Fintype.piFinset (fun _ : exitsS n S => nz) := by
    intro φ hφ
    rw [Fintype.mem_piFinset]
    intro a; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_phiSet.mp hφ).1 a⟩
  have hle := Finset.card_le_card hsub
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_coe, hnz_card] at hle
  exact hle

private lemma phiCount_le_rank4 (n d : ℕ) (hd : 2 ≤ d) (S : Finset (Fin n)) (hne : S ≠ Finset.univ)
    (hsurj : Function.Surjective ((parityMap n).comp (embedRuns n S hne))) :
    2 ^ (4 * d) * (phiSet n d S hne).card ≤ 4 * (2 ^ d - 1) ^ (exitsS n S).card := by
  classical
  have hspan_sig : Submodule.span (ZMod 2) (Set.range (fun a : exitsS n S => fun b : Fin 4 => runSig n S hne a b)) = ⊤ := by
    rw [eq_top_iff]; intro y _
    rcases hsurj y with ⟨c, hc⟩
    have hy : y = ∑ a : exitsS n S, c a • (fun b : Fin 4 => runSig n S hne a b) := by
      funext b; rw [← hc]; change parityMap n (embedRuns n S hne c) b = _
      rw [parityMap_embedRuns]; simp [Finset.sum_apply, mul_comm]
    rw [hy]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have hex_basis : ∃ I : Finset (exitsS n S), I.card = 4 ∧
      LinearIndependent (ZMod 2) (fun a : I => fun b : Fin 4 => runSig n S hne a.1 b) := by
    rcases exists_linearIndependent (ZMod 2) (Set.range (fun a : exitsS n S => fun b : Fin 4 => runSig n S hne a b)) with
      ⟨s, hs_sub, hs_span, hs_li⟩
    rw [hspan_sig] at hs_span
    haveI : Fintype s := Fintype.ofFinite s
    have hs_card : Fintype.card s = 4 := by
      let b : Module.Basis s (ZMod 2) (Fin 4 → ZMod 2) := Module.Basis.mk hs_li (by rw [Subtype.range_coe_subtype]; exact le_of_eq hs_span.symm)
      have := Module.finrank_eq_card_basis b
      rw [Module.finrank_fin_fun] at this; omega
    have hpick : ∀ v : s, ∃ a : exitsS n S, (fun b : Fin 4 => runSig n S hne a b) = v.1 := fun v => hs_sub v.2
    let f : s → exitsS n S := fun v => Classical.choose (hpick v)
    have hf_spec : ∀ v : s, (fun b : Fin 4 => runSig n S hne (f v) b) = v.1 := fun v => Classical.choose_spec (hpick v)
    have hf_inj : Function.Injective f := fun v1 v2 h => Subtype.ext (by rw [← hf_spec v1, ← hf_spec v2, h])
    let I := Finset.univ.image f
    have hI_card : I.card = 4 := by rw [Finset.card_image_of_injective _ hf_inj, Finset.card_univ, hs_card]
    refine ⟨I, hI_card, ?_⟩
    let e : I ≃ s := Equiv.ofBijective (fun a => Classical.choose (Finset.mem_image.mp a.2))
      ⟨fun a1 a2 h => by
        have h1 := (Classical.choose_spec (Finset.mem_image.mp a1.2)).2
        have h2 := (Classical.choose_spec (Finset.mem_image.mp a2.2)).2
        dsimp only at h
        exact Subtype.ext (by rw [← h1, ← h2, h]),
       fun v => ⟨⟨f v, Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩⟩,
         hf_inj (Classical.choose_spec (Finset.mem_image.mp (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩))).2⟩⟩
    have hcomp : (fun a : I => fun b : Fin 4 => runSig n S hne a.1 b) = (fun v : s => (v.1 : Fin 4 → ZMod 2)) ∘ e := by
      funext a; dsimp only [Function.comp_apply, e, Equiv.ofBijective_apply]
      rw [← hf_spec, (Classical.choose_spec (Finset.mem_image.mp a.2)).2]
    rw [hcomp]
    exact hs_li.comp e e.injective
  rcases hex_basis with ⟨I, hI_card, hI_li⟩
  let rest := (Finset.univ : Finset (exitsS n S)) \ I
  have hrest_card : rest.card = (exitsS n S).card - 4 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_coe, hI_card]
  have hcard_ge4 : 4 ≤ (exitsS n S).card := by
    have := Finset.card_le_univ I; rw [Fintype.card_coe] at this; omega
  let nz := (Finset.univ : Finset (Fin d → ZMod 2)).filter (fun v => v ≠ 0)
  have hnz_card : nz.card = 2 ^ d - 1 := by
    have h1 : nz = Finset.univ.erase 0 := by ext v; simp [nz]
    rw [h1, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hphi_le : (phiSet n d S hne).card ≤ (2 ^ d - 1) ^ ((exitsS n S).card - 4) := by
    have hle := Finset.card_le_card_of_injOn (s := phiSet n d S hne)
      (t := Fintype.piFinset (fun _ : rest => nz))
      (fun (φ : exitsS n S → (Fin d → ZMod 2)) (a : rest) => φ a.1)
      (fun φ hφ => by
        rw [Finset.mem_coe, Fintype.mem_piFinset]
        intro a; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_phiSet.mp (Finset.mem_coe.mp hφ)).1 a.1⟩)
      (fun φ1 hφ1 φ2 hφ2 heq => by
        have hpar1 := (mem_phiSet.mp (Finset.mem_coe.mp hφ1)).2.1
        have hpar2 := (mem_phiSet.mp (Finset.mem_coe.mp hφ2)).2.1
        have hrest_eq : ∀ a ∈ rest, φ1 a = φ2 a := fun a ha => congrFun heq ⟨a, ha⟩
        have hdiff_zero : ∀ j : Fin d, ∑ a : I, (φ1 a.1 j - φ2 a.1 j) • (fun b : Fin 4 => runSig n S hne a.1 b) = 0 := by
          intro j; funext b
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
          have h1 := congrFun (hpar1 b) j
          have h2 := congrFun (hpar2 b) j
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 h2
          have hsplit : ∑ a : exitsS n S, runSig n S hne a b * (φ1 a j - φ2 a j) = 0 := by
            simp_rw [mul_sub, Finset.sum_sub_distrib, h1, h2, sub_self]
          have hu : (Finset.univ : Finset (exitsS n S)) = I ∪ rest := by ext a; simp [rest]
          have hd_ir : Disjoint I rest := disjoint_sdiff_self_right
          rw [hu, Finset.sum_union hd_ir] at hsplit
          have hzr : ∑ a ∈ rest, runSig n S hne a b * (φ1 a j - φ2 a j) = 0 :=
            Finset.sum_eq_zero fun a ha => by rw [hrest_eq a ha, sub_self, mul_zero]
          rw [hzr, add_zero] at hsplit
          rw [← Finset.sum_coe_sort I] at hsplit
          simpa [mul_comm] using hsplit
        funext a j
        by_cases ha : a ∈ I
        · have hdep := Fintype.linearIndependent_iff.mp hI_li (fun x : I => φ1 x.1 j - φ2 x.1 j) (hdiff_zero j) ⟨a, ha⟩
          exact sub_eq_zero.mp hdep
        · exact congrFun (hrest_eq a (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩)) j)
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_coe, hrest_card, hnz_card] at hle
    exact hle
  have hpow4 : 2 ^ (4 * d) ≤ 4 * (2 ^ d - 1) ^ 4 := by
    have h2d : 4 ≤ 2 ^ d := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by omega) hd
    have h34 : 3 * 2 ^ d ≤ 4 * (2 ^ d - 1) := by omega
    have h34p : (3 * 2 ^ d) ^ 4 ≤ (4 * (2 ^ d - 1)) ^ 4 := Nat.pow_le_pow_left h34 4
    have h81 : 81 * (2 ^ d) ^ 4 ≤ 256 * (2 ^ d - 1) ^ 4 := by
      calc 81 * (2 ^ d) ^ 4 = (3 * 2 ^ d) ^ 4 := by ring
        _ ≤ (4 * (2 ^ d - 1)) ^ 4 := h34p
        _ = 256 * (2 ^ d - 1) ^ 4 := by ring
    have hpow_eq : 2 ^ (4 * d) = (2 ^ d) ^ 4 := by rw [mul_comm, pow_mul]
    rw [hpow_eq]; omega
  calc 2 ^ (4 * d) * (phiSet n d S hne).card
      ≤ 2 ^ (4 * d) * (2 ^ d - 1) ^ ((exitsS n S).card - 4) := Nat.mul_le_mul_left _ hphi_le
    _ ≤ (4 * (2 ^ d - 1) ^ 4) * (2 ^ d - 1) ^ ((exitsS n S).card - 4) := Nat.mul_le_mul_right _ hpow4
    _ = 4 * ((2 ^ d - 1) ^ 4 * (2 ^ d - 1) ^ ((exitsS n S).card - 4)) := by ring
    _ = 4 * (2 ^ d - 1) ^ (exitsS n S).card := by
        rw [← pow_add, show 4 + ((exitsS n S).card - 4) = (exitsS n S).card by omega]

private lemma prod_le_prod_nonneg {ι R : Type*} [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]
    {s : Finset ι} {f g : ι → R} (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact mul_le_mul (hfg a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) (fun i hi => hfg i (Finset.mem_insert_of_mem hi)))
      (Finset.prod_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (le_trans (hf a (Finset.mem_insert_self _ _)) (hfg a (Finset.mem_insert_self _ _)))

private def signZ2 (z : ZMod 2) : ℤ :=
  if z = 0 then 1 else -1

private lemma signZ2_add (a b : ZMod 2) : signZ2 (a + b) = signZ2 a * signZ2 b := by
  fin_cases a <;> fin_cases b <;> decide

private lemma signZ2_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    signZ2 (∑ i ∈ s, f i) = ∏ i ∈ s, signZ2 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [signZ2]
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, signZ2_add, ih]

private lemma sum_signZ2_dot (d : ℕ) (u : Fin d → ZMod 2) :
    ∑ c : Fin d → ZMod 2, signZ2 (∑ j : Fin d, u j * c j) = if u = 0 then (2 ^ d : ℤ) else 0 := by
  have hprod : ∑ c : Fin d → ZMod 2, signZ2 (∑ j : Fin d, u j * c j) =
      ∏ j : Fin d, ∑ x : ZMod 2, signZ2 (u j * x) := by
    have h1 : ∀ c : Fin d → ZMod 2, signZ2 (∑ j : Fin d, u j * c j) = ∏ j : Fin d, signZ2 (u j * c j) :=
      fun c => signZ2_sum Finset.univ _
    rw [Finset.sum_congr rfl fun c _ => h1 c, ← Fintype.prod_sum (fun (j : Fin d) (x : ZMod 2) => signZ2 (u j * x))]
  rw [hprod]
  by_cases hu : u = 0
  · rw [if_pos hu, hu]
    have hterm : ∀ j : Fin d, ∑ x : ZMod 2, signZ2 ((0 : Fin d → ZMod 2) j * x) = 2 := fun j => by
      simp [signZ2, Fin.sum_univ_two]
    rw [Finset.prod_congr rfl fun j _ => hterm j, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · rw [if_neg hu]
    have hex : ∃ j0 : Fin d, u j0 ≠ 0 := by by_contra hall; push_neg at hall; exact hu (funext hall)
    rcases hex with ⟨j0, hj0⟩
    refine Finset.prod_eq_zero (Finset.mem_univ j0) ?_
    have hu1 : u j0 = 1 := by generalize u j0 = z at hj0 ⊢; fin_cases z <;> first | exact absurd rfl hj0 | rfl
    rw [hu1]; decide

set_option maxHeartbeats 800000 in
private lemma phiCount_fourier_approx (n d : ℕ) (hd : 2 ≤ d) (S : Finset (Fin n)) (hne : S ≠ Finset.univ)
    (hm : 6 * d ≤ (exitsS n S).card)
    (hbad : ∀ α : Fin 4 → ZMod 2, α ≠ 0 → 10 ≤ badRuns n S hne α) :
    |(2 ^ (4 * d) : ℝ) * ((phiSet n d S hne).card : ℝ) - ((2 ^ d - 1 : ℝ) ^ (exitsS n S).card)| ≤
      (1024 / (2 : ℝ) ^ (6 * d) + 1 / (2 : ℝ) ^ d) * ((2 ^ d - 1 : ℝ) ^ (exitsS n S).card) := by
  classical
  let m := (exitsS n S).card
  let q : ℕ := 2 ^ d - 1
  let nz := (Finset.univ : Finset (Fin d → ZMod 2)).filter (fun v => v ≠ 0)
  have hnz_card : nz.card = q := by
    have h1 : nz = Finset.univ.erase 0 := by ext v; simp [nz]
    rw [h1, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  let Pnz : Finset (exitsS n S → (Fin d → ZMod 2)) := Fintype.piFinset (fun _ : exitsS n S => nz)
  have hfour : ((2 ^ (4 * d) * (phiSet0 n d S hne).card : ℕ) : ℤ) =
      ∑ χ : Fin 4 → (Fin d → ZMod 2),
        ∏ a : exitsS n S, (if (∑ b : Fin 4, runSig n S hne a b • χ b) = 0 then (q : ℤ) else -1) := by
    have hind : ∀ φ ∈ Pnz,
        (∑ χ : Fin 4 → (Fin d → ZMod 2),
          ∏ b : Fin 4, signZ2 (∑ j : Fin d, χ b j * (∑ a : exitsS n S, runSig n S hne a b • φ a) j)) =
        if ∀ b : Fin 4, (∑ a : exitsS n S, runSig n S hne a b • φ a) = 0 then (2 ^ (4 * d) : ℤ) else 0 := by
      intro φ _
      rw [← Fintype.prod_sum (fun (b : Fin 4) (c : Fin d → ZMod 2) =>
        signZ2 (∑ j : Fin d, c j * (∑ a : exitsS n S, runSig n S hne a b • φ a) j))]
      have hterm : ∀ b : Fin 4,
          (∑ c : Fin d → ZMod 2, signZ2 (∑ j : Fin d, c j * (∑ a : exitsS n S, runSig n S hne a b • φ a) j)) =
          if (∑ a : exitsS n S, runSig n S hne a b • φ a) = 0 then (2 ^ d : ℤ) else 0 := by
        intro b
        have hcomm := sum_signZ2_dot d (∑ a : exitsS n S, runSig n S hne a b • φ a)
        rw [← hcomm]
        refine Finset.sum_congr rfl fun c _ => by congr 1; refine Finset.sum_congr rfl fun j _ => mul_comm _ _
      rw [Finset.prod_congr rfl fun b _ => hterm b]
      by_cases hall : ∀ b : Fin 4, (∑ a : exitsS n S, runSig n S hne a b • φ a) = 0
      · rw [if_pos hall]
        have h1 : ∀ b : Fin 4, (if (∑ a : exitsS n S, runSig n S hne a b • φ a) = 0 then (2 ^ d : ℤ) else 0) = 2 ^ d :=
          fun b => if_pos (hall b)
        rw [Finset.prod_congr rfl fun b _ => h1 b, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]
      · rw [if_neg hall]
        push_neg at hall; rcases hall with ⟨b0, hb0⟩
        exact Finset.prod_eq_zero (Finset.mem_univ b0) (if_neg hb0)
    have hlhs : ((2 ^ (4 * d) * (phiSet0 n d S hne).card : ℕ) : ℤ) =
        ∑ φ ∈ Pnz, ∑ χ : Fin 4 → (Fin d → ZMod 2),
          ∏ b : Fin 4, signZ2 (∑ j : Fin d, χ b j * (∑ a : exitsS n S, runSig n S hne a b • φ a) j) := by
      rw [Finset.sum_congr rfl hind, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hfeq : Pnz.filter (fun φ => ∀ b : Fin 4, (∑ a : exitsS n S, runSig n S hne a b • φ a) = 0) =
          phiSet0 n d S hne := by
        ext φ; simp only [Finset.mem_filter, Pnz, Fintype.mem_piFinset, nz, Finset.mem_univ, true_and, mem_phiSet0]
      rw [hfeq]; push_cast; ring
    rw [hlhs, Finset.sum_comm]
    refine Finset.sum_congr rfl fun χ _ => ?_
    have hrearr : ∀ φ ∈ Pnz,
        (∏ b : Fin 4, signZ2 (∑ j : Fin d, χ b j * (∑ a : exitsS n S, runSig n S hne a b • φ a) j)) =
        ∏ a : exitsS n S, signZ2 (∑ j : Fin d, (∑ b : Fin 4, runSig n S hne a b • χ b) j * φ a j) := by
      intro φ _
      rw [← signZ2_sum, ← signZ2_sum]
      congr 1
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    rw [Finset.sum_congr rfl hrearr]
    have hfac : ∑ φ ∈ Pnz, ∏ a : exitsS n S, signZ2 (∑ j : Fin d, (∑ b : Fin 4, runSig n S hne a b • χ b) j * φ a j) =
        ∏ a : exitsS n S, ∑ c ∈ nz, signZ2 (∑ j : Fin d, (∑ b : Fin 4, runSig n S hne a b • χ b) j * c j) := by
      dsimp only [Pnz]
      exact (Finset.prod_univ_sum (t := fun _ : exitsS n S => nz)
        (f := fun (a : exitsS n S) (c : Fin d → ZMod 2) =>
          signZ2 (∑ j : Fin d, (∑ b : Fin 4, runSig n S hne a b • χ b) j * c j))).symm
    rw [hfac]
    refine Finset.prod_congr rfl fun a _ => ?_
    let u := ∑ b : Fin 4, runSig n S hne a b • χ b
    have hsplit : ∑ c : Fin d → ZMod 2, signZ2 (∑ j : Fin d, u j * c j) =
        signZ2 (∑ j : Fin d, u j * (0 : Fin d → ZMod 2) j) +
        ∑ c ∈ nz, signZ2 (∑ j : Fin d, u j * c j) := by
      have hnz_eq : nz = Finset.univ.erase 0 := by ext c; simp [nz]
      rw [hnz_eq, Finset.add_sum_erase Finset.univ (fun c : Fin d → ZMod 2 => signZ2 (∑ j : Fin d, u j * c j)) (Finset.mem_univ (0 : Fin d → ZMod 2))]
    have h0_term : signZ2 (∑ j : Fin d, u j * (0 : Fin d → ZMod 2) j) = 1 := by simp [signZ2]
    have htot := sum_signZ2_dot d u
    rw [hsplit, h0_term] at htot
    by_cases hu : u = 0
    · rw [if_pos hu] at htot ⊢
      have h2d : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by omega)
      have hq_cast : (q : ℤ) = (2 ^ d : ℤ) - 1 := by dsimp only [q]; rw [Int.ofNat_sub h2d]; push_cast; rfl
      linarith
    · rw [if_neg hu] at htot ⊢
      linarith
  have hdiff0 : |((2 ^ (4 * d) * (phiSet0 n d S hne).card : ℕ) : ℤ) - (q : ℤ) ^ m| ≤
      (2 ^ (4 * d) : ℤ) * (q : ℤ) ^ (m - 10) := by
    rw [hfour]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : Fin 4 → (Fin d → ZMod 2)))]
    have hzero_term : ∏ a : exitsS n S, (if (∑ b : Fin 4, runSig n S hne a b • (0 : Fin 4 → (Fin d → ZMod 2)) b) = 0 then (q : ℤ) else -1) =
        (q : ℤ) ^ m := by
      have h1 : ∀ a : exitsS n S, (if (∑ b : Fin 4, runSig n S hne a b • (0 : Fin 4 → (Fin d → ZMod 2)) b) = 0 then (q : ℤ) else -1) = (q : ℤ) := by
        intro a; simp
      rw [Finset.prod_congr rfl fun a _ => h1 a, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
    rw [hzero_term, add_sub_cancel_left]
    have hterm_le : ∀ χ ∈ (Finset.univ : Finset (Fin 4 → (Fin d → ZMod 2))).erase 0,
        |∏ a : exitsS n S, (if (∑ b : Fin 4, runSig n S hne a b • χ b) = 0 then (q : ℤ) else -1)| ≤ (q : ℤ) ^ (m - 10) := by
      intro χ hχ
      have hχ_nz : χ ≠ 0 := (Finset.mem_erase.mp hχ).1
      have hex_bj : ∃ b : Fin 4, ∃ j : Fin d, χ b j ≠ 0 := by
        by_contra hall; push_neg at hall; exact hχ_nz (funext fun b => funext fun j => hall b j)
      rcases hex_bj with ⟨b0, j0, hbj0⟩
      let α : Fin 4 → ZMod 2 := fun b => χ b j0
      have hα_nz : α ≠ 0 := fun h0 => hbj0 (congrFun h0 b0)
      have hbad10 : 10 ≤ badRuns n S hne α := hbad α hα_nz
      let B := (Finset.univ : Finset (exitsS n S)).filter (fun a => (∑ b : Fin 4, α b * runSig n S hne a b) ≠ 0)
      have hB_card : 10 ≤ B.card := hbad10
      have hB_nz : ∀ a ∈ B, (∑ b : Fin 4, runSig n S hne a b • χ b) ≠ 0 := by
        intro a ha h0
        have hcoord := congrFun h0 j0
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcoord
        have hnz := (Finset.mem_filter.mp ha).2
        apply hnz
        rw [← hcoord]
        refine Finset.sum_congr rfl fun b _ => mul_comm _ _
      rw [Finset.abs_prod]
      have hprod_le : ∏ a : exitsS n S, |(if (∑ b : Fin 4, runSig n S hne a b • χ b) = 0 then (q : ℤ) else -1)| ≤
          ∏ a : exitsS n S, (if a ∈ B then (1 : ℤ) else (q : ℤ)) := by
        refine prod_le_prod_nonneg (fun _ _ => abs_nonneg _) fun a _ => ?_
        by_cases ha : a ∈ B
        · rw [if_pos ha, if_neg (hB_nz a ha)]; norm_num
        · rw [if_neg ha]
          split_ifs
          · rw [abs_of_nonneg (Int.natCast_nonneg q)]
          · have hq1 : 1 ≤ q := by
              dsimp only [q]
              have h4 : 4 ≤ 2 ^ d := by
                calc 4 = 2 ^ 2 := by norm_num
                  _ ≤ 2 ^ d := Nat.pow_le_pow_right (by omega) hd
              omega
            norm_num; omega
      have hprod_eq : ∏ a : exitsS n S, (if a ∈ B then (1 : ℤ) else (q : ℤ)) = (q : ℤ) ^ (m - B.card) := by
        rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun a => a ∈ B)]
        have h1 : ∏ a ∈ Finset.univ.filter (fun a : exitsS n S => a ∈ B), (if a ∈ B then (1 : ℤ) else (q : ℤ)) = 1 :=
          Finset.prod_eq_one fun a ha => if_pos (Finset.mem_filter.mp ha).2
        have h2 : ∏ a ∈ Finset.univ.filter (fun a : exitsS n S => a ∉ B), (if a ∈ B then (1 : ℤ) else (q : ℤ)) =
            (q : ℤ) ^ (Finset.univ.filter (fun a : exitsS n S => a ∉ B)).card := by
          rw [Finset.prod_congr rfl fun a ha => if_neg (Finset.mem_filter.mp ha).2, Finset.prod_const]
        have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (exitsS n S))) (p := fun a => a ∈ B)
        have hBeq : Finset.univ.filter (fun a : exitsS n S => a ∈ B) = B := by ext a; simp
        rw [hBeq, Finset.card_univ, Fintype.card_coe] at htot
        rw [h1, one_mul, h2]; congr 1; omega
      have hq_ge1 : (1 : ℤ) ≤ (q : ℤ) := by
        have h4 : 4 ≤ 2 ^ d := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ d := Nat.pow_le_pow_right (by omega) hd
        dsimp only [q]; omega
      calc _ ≤ (q : ℤ) ^ (m - B.card) := hprod_eq ▸ hprod_le
        _ ≤ (q : ℤ) ^ (m - 10) := pow_le_pow_right₀ hq_ge1 (by omega)
    calc |∑ χ ∈ Finset.univ.erase 0, _|
        ≤ ∑ χ ∈ Finset.univ.erase 0, |_| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _χ ∈ Finset.univ.erase 0, (q : ℤ) ^ (m - 10) := Finset.sum_le_sum hterm_le
      _ = ((Finset.univ.erase (0 : Fin 4 → (Fin d → ZMod 2))).card : ℤ) * (q : ℤ) ^ (m - 10) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 ^ (4 * d) : ℤ) * (q : ℤ) ^ (m - 10) := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (Int.natCast_nonneg q) _)
          have hc : (Finset.univ.erase (0 : Fin 4 → (Fin d → ZMod 2))).card ≤ 2 ^ (4 * d) := by
            calc _ ≤ (Finset.univ : Finset (Fin 4 → (Fin d → ZMod 2))).card := Finset.card_le_card (Finset.erase_subset _ _)
              _ = 2 ^ (4 * d) := by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_fin, ← pow_mul, mul_comm]
          exact_mod_cast hc
  have hnonspan : (phiSet0 n d S hne).card - (phiSet n d S hne).card ≤ (2 ^ d - 1) * (2 ^ (d - 1) - 1) ^ m := by
    have hsub : phiSet n d S hne ⊆ phiSet0 n d S hne := fun φ hφ =>
      mem_phiSet0.mpr ⟨(mem_phiSet.mp hφ).1, (mem_phiSet.mp hφ).2.1⟩
    rw [← Finset.card_sdiff_of_subset hsub]
    let badSpan := phiSet0 n d S hne \ phiSet n d S hne
    let hyp (β : Fin d → ZMod 2) : Finset (Fin d → ZMod 2) :=
      (Finset.univ : Finset (Fin d → ZMod 2)).filter (fun v => v ≠ 0 ∧ (∑ j : Fin d, β j * v j) = 0)
    have hhyp_card : ∀ β : Fin d → ZMod 2, β ≠ 0 → (hyp β).card = 2 ^ (d - 1) - 1 := by
      intro β hβ
      let fβ : (Fin d → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
        { toFun := fun v => ∑ j : Fin d, β j * v j
          map_add' := fun v1 v2 => by simp [mul_add, Finset.sum_add_distrib]
          map_smul' := fun r v => by
            simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => by ring }
      have hsurj_β : Function.Surjective fβ := by
        have hex : ∃ j0 : Fin d, β j0 ≠ 0 := by by_contra hall; push_neg at hall; exact hβ (funext hall)
        rcases hex with ⟨j0, hj0⟩
        have hb1 : β j0 = 1 := by generalize β j0 = z at hj0 ⊢; fin_cases z <;> first | exact absurd rfl hj0 | rfl
        intro z; refine ⟨z • Pi.single j0 1, ?_⟩
        rw [map_smul]; dsimp only [fβ, LinearMap.coe_mk, AddHom.coe_mk]
        simp [Pi.single_apply, hb1]
      have hker_dim : Module.finrank (ZMod 2) (LinearMap.ker fβ) = d - 1 := by
        have hrn := LinearMap.finrank_range_add_finrank_ker fβ
        rw [LinearMap.range_eq_top.mpr hsurj_β, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at hrn
        omega
      have hker_card : Fintype.card (LinearMap.ker fβ) = 2 ^ (d - 1) := by
        have := Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker fβ)
        rwa [ZMod.card, hker_dim] at this
      have hker_fcard : ((Finset.univ : Finset (Fin d → ZMod 2)).filter (fun v => fβ v = 0)).card = 2 ^ (d - 1) := by
        rw [← hker_card, ← Fintype.card_subtype]
        exact Fintype.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
      have hhyp_eq : hyp β = ((Finset.univ : Finset (Fin d → ZMod 2)).filter (fun v => fβ v = 0)).erase 0 := by
        ext v; simp [hyp, fβ]
      have h0_mem : (0 : Fin d → ZMod 2) ∈ (Finset.univ : Finset (Fin d → ZMod 2)).filter (fun v => fβ v = 0) := by
        simp [fβ]
      rw [hhyp_eq, Finset.card_erase_of_mem h0_mem, hker_fcard]
    have hcover : badSpan ⊆ nz.biUnion (fun β => Fintype.piFinset (fun _ : exitsS n S => hyp β)) := by
      intro φ hφ
      have hφ0 := (Finset.mem_sdiff.mp hφ).1
      have hnot := (Finset.mem_sdiff.mp hφ).2
      have hφ_nz := (mem_phiSet0.mp hφ0).1
      have hφ_par := (mem_phiSet0.mp hφ0).2
      have hne_top : Submodule.span (ZMod 2) (Set.range φ) ≠ ⊤ := fun htop =>
        hnot (mem_phiSet.mpr ⟨hφ_nz, hφ_par, htop⟩)
      let K := Submodule.span (ZMod 2) (Set.range φ)
      have hq_pos : 0 < Module.finrank (ZMod 2) ((Fin d → ZMod 2) ⧸ K) := by
        have hlt : Module.finrank (ZMod 2) K < d := by
          have := Submodule.finrank_lt hne_top; rwa [Module.finrank_fin_fun] at this
        have hr := Submodule.finrank_quotient_add_finrank K
        rw [Module.finrank_fin_fun] at hr; omega
      have hq_nt : Nontrivial ((Fin d → ZMod 2) ⧸ K) := by
        by_contra hnt; rw [not_nontrivial_iff_subsingleton] at hnt
        have := Module.finrank_zero_of_subsingleton (R := ZMod 2) (M := (Fin d → ZMod 2) ⧸ K); omega
      rcases exists_ne (0 : (Fin d → ZMod 2) ⧸ K) with ⟨q0, hq0⟩
      have hex_d : ∃ ψ0 : ((Fin d → ZMod 2) ⧸ K) →ₗ[ZMod 2] ZMod 2, ψ0 q0 ≠ 0 := by
        let b := Module.Basis.ofVectorSpace (ZMod 2) ((Fin d → ZMod 2) ⧸ K)
        by_contra hall; push_neg at hall
        exact hq0 (b.repr.injective (by rw [map_zero]; ext i; exact hall ((Finsupp.lapply i).comp b.repr.toLinearMap)))
      rcases hex_d with ⟨ψ0, hψ0⟩
      let ψ := ψ0.comp (Submodule.mkQ K)
      let β : Fin d → ZMod 2 := fun j => ψ (Pi.single j 1)
      have hβ_nz : β ≠ 0 := by
        intro h0; rcases Submodule.Quotient.mk_surjective K q0 with ⟨w0, rfl⟩
        apply hψ0; change ψ w0 = 0
        have hw : w0 = ∑ j : Fin d, w0 j • Pi.single j (1 : ZMod 2) := by
          funext j; simp [Finset.sum_apply, Pi.single_apply]
        conv_lhs => rw [hw]
        rw [map_sum]
        refine Finset.sum_eq_zero fun j _ => by rw [map_smul, show ψ (Pi.single j 1) = 0 from congrFun h0 j, smul_zero]
      refine Finset.mem_biUnion.mpr ⟨β, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hβ_nz⟩, ?_⟩
      rw [Fintype.mem_piFinset]
      intro a
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hφ_nz a, ?_⟩
      have hmem : φ a ∈ K := Submodule.subset_span ⟨a, rfl⟩
      have hz : ψ (φ a) = 0 := by
        dsimp only [ψ, LinearMap.comp_apply]; rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero K).mpr hmem, map_zero]
      have hrepr : φ a = ∑ j : Fin d, φ a j • Pi.single j (1 : ZMod 2) := by
        funext j; simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs at hz => rw [hrepr]
      rw [map_sum] at hz
      simpa [β, map_smul, smul_eq_mul, mul_comm] using hz
    calc badSpan.card
        ≤ (nz.biUnion (fun β => Fintype.piFinset (fun _ : exitsS n S => hyp β))).card := Finset.card_le_card hcover
      _ ≤ ∑ β ∈ nz, (Fintype.piFinset (fun _ : exitsS n S => hyp β)).card := Finset.card_biUnion_le
      _ = ∑ β ∈ nz, (2 ^ (d - 1) - 1) ^ m := Finset.sum_congr rfl fun β hβ => by
          rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_coe,
            hhyp_card β (Finset.mem_filter.mp hβ).2]
      _ = (2 ^ d - 1) * (2 ^ (d - 1) - 1) ^ m := by rw [Finset.sum_const, smul_eq_mul, hnz_card]
  have hsub_le : (phiSet n d S hne).card ≤ (phiSet0 n d S hne).card :=
    Finset.card_le_card fun φ hφ => mem_phiSet0.mpr ⟨(mem_phiSet.mp hφ).1, (mem_phiSet.mp hφ).2.1⟩
  have hq_real : (q : ℝ) = (2 : ℝ) ^ d - 1 := by
    dsimp only [q]
    have h1 : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by omega)
    rw [Nat.cast_sub h1]; push_cast; rfl
  have hq_pos : (0 : ℝ) < (q : ℝ) := by
    have : 4 ≤ 2 ^ d := by calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ d := Nat.pow_le_pow_right (by omega) hd
    dsimp only [q]; exact_mod_cast (by omega : 0 < 2 ^ d - 1)
  have h1_r : |(2 ^ (4 * d) : ℝ) * ((phiSet0 n d S hne).card : ℝ) - (q : ℝ) ^ m| ≤
      (1024 / (2 : ℝ) ^ (6 * d)) * (q : ℝ) ^ m := by
    have hcast : |(2 ^ (4 * d) : ℝ) * ((phiSet0 n d S hne).card : ℝ) - (q : ℝ) ^ m| ≤
        (2 ^ (4 * d) : ℝ) * (q : ℝ) ^ (m - 10) := by
      have h' : (|((2 ^ (4 * d) * (phiSet0 n d S hne).card : ℕ) : ℤ) - (q : ℤ) ^ m| : ℝ) ≤
          ((2 ^ (4 * d) : ℤ) * (q : ℤ) ^ (m - 10) : ℝ) := by exact_mod_cast hdiff0
      push_cast at h'; exact h'
    have hm10 : 10 ≤ m := by omega
    have hq_ge : (2 : ℝ) ^ (d - 1) ≤ (q : ℝ) := by
      have hnat : 2 ^ (d - 1) ≤ q := by
        dsimp only [q]
        have h2d : 2 ^ d = 2 * 2 ^ (d - 1) := by
          rw [← pow_succ', show d - 1 + 1 = d by omega]
        have hpos : 1 ≤ 2 ^ (d - 1) := Nat.one_le_pow _ 2 (by omega)
        omega
      exact_mod_cast hnat
    have hq10 : (2 : ℝ) ^ (10 * d) / 1024 ≤ (q : ℝ) ^ 10 := by
      have h1 : ((2 : ℝ) ^ (d - 1)) ^ 10 ≤ (q : ℝ) ^ 10 := pow_le_pow_left₀ (by positivity) hq_ge 10
      have h2 : (2 : ℝ) ^ (10 * d) = 1024 * ((2 : ℝ) ^ (d - 1)) ^ 10 := by
        rw [← pow_mul, show (1024 : ℝ) = (2 : ℝ) ^ 10 by norm_num, ← pow_add]
        congr 1; omega
      linarith
    have hmul_q : (q : ℝ) ^ (m - 10) * (q : ℝ) ^ 10 = (q : ℝ) ^ m := by
      rw [← pow_add, Nat.sub_add_cancel hm10]
    have hstep : (2 ^ (4 * d) : ℝ) * (q : ℝ) ^ (m - 10) ≤ (1024 / (2 : ℝ) ^ (6 * d)) * (q : ℝ) ^ m := by
      rw [← hmul_q]
      have h2eq : (2 : ℝ) ^ (4 * d) * (2 : ℝ) ^ (6 * d) = (2 : ℝ) ^ (10 * d) := by
        rw [← pow_add]; congr 1; omega
      have hle_div : (2 : ℝ) ^ (4 * d) ≤ (1024 / (2 : ℝ) ^ (6 * d)) * (q : ℝ) ^ 10 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), h2eq]
        linarith
      calc (2 : ℝ) ^ (4 * d) * (q : ℝ) ^ (m - 10)
          ≤ ((1024 / (2 : ℝ) ^ (6 * d)) * (q : ℝ) ^ 10) * (q : ℝ) ^ (m - 10) :=
              mul_le_mul_of_nonneg_right hle_div (by positivity)
        _ = (1024 / (2 : ℝ) ^ (6 * d)) * ((q : ℝ) ^ (m - 10) * (q : ℝ) ^ 10) := by ring
    exact hcast.trans hstep
  have h2_r : (2 ^ (4 * d) : ℝ) * (((phiSet0 n d S hne).card : ℝ) - ((phiSet n d S hne).card : ℝ)) ≤
      (1 / (2 : ℝ) ^ d) * (q : ℝ) ^ m := by
    have hdiff_nat : (((phiSet0 n d S hne).card : ℝ) - ((phiSet n d S hne).card : ℝ)) ≤
        (q : ℝ) * ((2 ^ (d - 1) - 1 : ℕ) : ℝ) ^ m := by
      have h1 : (((phiSet0 n d S hne).card - (phiSet n d S hne).card : ℕ) : ℝ) ≤
          (((2 ^ d - 1) * (2 ^ (d - 1) - 1) ^ m : ℕ) : ℝ) := by exact_mod_cast hnonspan
      rw [Nat.cast_sub hsub_le, Nat.cast_mul, Nat.cast_pow] at h1
      exact h1
    have hhalf : ((2 ^ (d - 1) - 1 : ℕ) : ℝ) ≤ (q : ℝ) / 2 := by
      have h2d : 2 ^ d = 2 * 2 ^ (d - 1) := by rw [← pow_succ', show d - 1 + 1 = d by omega]
      have h1 : 1 ≤ 2 ^ (d - 1) := Nat.one_le_pow _ 2 (by omega)
      have hnat : 2 * (2 ^ (d - 1) - 1) ≤ q := by dsimp only [q]; omega
      have hr : (2 : ℝ) * ((2 ^ (d - 1) - 1 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hnat
      linarith
    have hpow_half : ((2 ^ (d - 1) - 1 : ℕ) : ℝ) ^ m ≤ (q : ℝ) ^ m / (2 : ℝ) ^ m := by
      rw [← div_pow]
      exact pow_le_pow_left₀ (by positivity) hhalf m
    have hq_le_2d : (q : ℝ) ≤ (2 : ℝ) ^ d := by
      have : q ≤ 2 ^ d := Nat.sub_le _ _
      exact_mod_cast this
    have h2m_ge : (2 : ℝ) ^ (6 * d) ≤ (2 : ℝ) ^ m := by exact_mod_cast Nat.pow_le_pow_right (by omega) hm
    have hcomb : (2 ^ (4 * d) : ℝ) * ((q : ℝ) * ((2 : ℝ) ^ m)⁻¹) ≤ (1 / (2 : ℝ) ^ d) := by
      rw [one_div, ← mul_assoc, mul_inv_le_iff₀ (by positivity)]
      calc (2 : ℝ) ^ (4 * d) * (q : ℝ)
          ≤ (2 : ℝ) ^ (4 * d) * (2 : ℝ) ^ d := mul_le_mul_of_nonneg_left hq_le_2d (by positivity)
        _ = (2 : ℝ) ^ (5 * d) := by rw [← pow_add]; congr 1; omega
        _ = ((2 : ℝ) ^ d)⁻¹ * (2 : ℝ) ^ (6 * d) := by
            rw [inv_mul_eq_div, eq_div_iff (by positivity), ← pow_add]; congr 1; omega
        _ ≤ ((2 : ℝ) ^ d)⁻¹ * (2 : ℝ) ^ m := mul_le_mul_of_nonneg_left h2m_ge (by positivity)
    calc (2 ^ (4 * d) : ℝ) * (((phiSet0 n d S hne).card : ℝ) - ((phiSet n d S hne).card : ℝ))
        ≤ (2 ^ (4 * d) : ℝ) * ((q : ℝ) * ((2 ^ (d - 1) - 1 : ℕ) : ℝ) ^ m) :=
            mul_le_mul_of_nonneg_left hdiff_nat (by positivity)
      _ ≤ (2 ^ (4 * d) : ℝ) * ((q : ℝ) * ((q : ℝ) ^ m / (2 : ℝ) ^ m)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow_half (by positivity)) (by positivity)
      _ = ((2 ^ (4 * d) : ℝ) * ((q : ℝ) * ((2 : ℝ) ^ m)⁻¹)) * (q : ℝ) ^ m := by rw [div_eq_mul_inv]; ring
      _ ≤ (1 / (2 : ℝ) ^ d) * (q : ℝ) ^ m := mul_le_mul_of_nonneg_right hcomb (by positivity)
  have hdiff_nn : 0 ≤ (2 ^ (4 * d) : ℝ) * (((phiSet0 n d S hne).card : ℝ) - ((phiSet n d S hne).card : ℝ)) := by
    have : ((phiSet n d S hne).card : ℝ) ≤ ((phiSet0 n d S hne).card : ℝ) := by exact_mod_cast hsub_le
    have : 0 ≤ ((phiSet0 n d S hne).card : ℝ) - ((phiSet n d S hne).card : ℝ) := by linarith
    positivity
  rw [← hq_real]
  have htri : (2 ^ (4 * d) : ℝ) * ((phiSet n d S hne).card : ℝ) - (q : ℝ) ^ m =
      ((2 ^ (4 * d) : ℝ) * ((phiSet0 n d S hne).card : ℝ) - (q : ℝ) ^ m) -
      (2 ^ (4 * d) : ℝ) * (((phiSet0 n d S hne).card : ℝ) - ((phiSet n d S hne).card : ℝ)) := by ring
  rw [htri]
  have habs := abs_sub ((2 ^ (4 * d) : ℝ) * ((phiSet0 n d S hne).card : ℝ) - (q : ℝ) ^ m)
    ((2 ^ (4 * d) : ℝ) * (((phiSet0 n d S hne).card : ℝ) - ((phiSet n d S hne).card : ℝ)))
  rw [abs_of_nonneg hdiff_nn] at habs
  linarith

private def step2 (q : ℝ) (u v : Bool) : ℝ :=
  if u = false ∧ v = true then q else 1

private noncomputable def mat2Pow (q : ℝ) (k : ℕ) (u v : Bool) : ℝ :=
  let L := 1 + Real.sqrt q
  let L' := 1 - Real.sqrt q
  match u, v with
  | false, false => (L ^ k + L' ^ k) / 2
  | true, true => (L ^ k + L' ^ k) / 2
  | false, true => Real.sqrt q * (L ^ k - L' ^ k) / 2
  | true, false => (L ^ k - L' ^ k) / (2 * Real.sqrt q)

private lemma mat2Pow_zero (q : ℝ) (hq : 0 < q) (u v : Bool) :
    mat2Pow q 0 u v = if u = v then 1 else 0 := by
  have hs : Real.sqrt q ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hq)
  cases u <;> cases v <;> simp [mat2Pow, hs]

private lemma mat2Pow_succ (q : ℝ) (hq : 0 < q) (k : ℕ) (u v : Bool) :
    mat2Pow q (k + 1) u v = ∑ w : Bool, mat2Pow q k u w * step2 q w v := by
  have hs : Real.sqrt q ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hq)
  have hsq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt (le_of_lt hq)
  rw [Fintype.sum_bool]
  cases u <;> cases v <;>
    (simp only [mat2Pow, step2, pow_succ, Bool.false_eq_true, Bool.true_eq_false,
      true_and, false_and, and_true, and_false, ↓reduceIte, mul_one]
     generalize Real.sqrt q = s at hs hsq ⊢
     subst hsq; field_simp [hs]; ring)

private lemma sum_path_step2 (q : ℝ) (hq : 0 < q) (k : ℕ) (u v : Bool) :
    (∑ b ∈ (Finset.univ : Finset (Fin (k + 1) → Bool)).filter (fun b => b 0 = u ∧ b ⟨k, by omega⟩ = v),
      ∏ i : Fin k, step2 q (b ⟨i.val, by omega⟩) (b ⟨i.val + 1, by omega⟩)) =
    mat2Pow q k u v := by
  induction k generalizing v with
  | zero =>
    rw [mat2Pow_zero q hq u v]
    by_cases huv : u = v
    · rw [if_pos huv]
      have hsing : ((Finset.univ : Finset (Fin 1 → Bool)).filter (fun b => b 0 = u ∧ b ⟨0, by omega⟩ = v)) =
          {fun _ => u} := by
        ext b; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨h0, _⟩; funext i; fin_cases i; exact h0
        · rintro rfl; exact ⟨rfl, huv⟩
      rw [hsing, Finset.sum_singleton]; simp
    · rw [if_neg huv]
      have hemp : ((Finset.univ : Finset (Fin 1 → Bool)).filter (fun b => b 0 = u ∧ b ⟨0, by omega⟩ = v)) = ∅ := by
        ext b; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        rintro ⟨h0, h1⟩; exact huv (h0.symm.trans h1)
      rw [hemp, Finset.sum_empty]
  | succ k ih =>
    rw [mat2Pow_succ q hq k u v]
    let S := (Finset.univ : Finset (Fin (k + 2) → Bool)).filter (fun b => b 0 = u ∧ b ⟨k + 1, by omega⟩ = v)
    have hsplit : ∑ b ∈ S, ∏ i : Fin (k + 1), step2 q (b ⟨i.val, by omega⟩) (b ⟨i.val + 1, by omega⟩) =
        ∑ w : Bool, ∑ b ∈ S.filter (fun b => b ⟨k, by omega⟩ = w),
          ∏ i : Fin (k + 1), step2 q (b ⟨i.val, by omega⟩) (b ⟨i.val + 1, by omega⟩) := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := fun b : Fin (k + 2) → Bool => b ⟨k, by omega⟩)
        (t := (Finset.univ : Finset Bool)) (fun _ _ => Finset.mem_univ _)]
    rw [hsplit]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← ih w, Finset.sum_mul]
    refine Finset.sum_bij (fun b _ => fun j : Fin (k + 1) => b ⟨j.val, by omega⟩) ?_ ?_ ?_ ?_
    · intro b hb
      have hS := (Finset.mem_filter.mp hb).1
      have hw := (Finset.mem_filter.mp hb).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hS).2.1, hw⟩
    · intro b1 hb1 b2 hb2 heq
      have hv1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hb1).1).2.2
      have hv2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hb2).1).2.2
      funext j
      by_cases hj : j.val < k + 1
      · exact congrFun heq ⟨j.val, hj⟩
      · have hjeq : j = ⟨k + 1, by omega⟩ := Fin.ext (by dsimp only; have := j.isLt; omega)
        rw [hjeq, hv1, hv2]
    · intro b' hb'
      let b : Fin (k + 2) → Bool := fun j => if h : j.val < k + 1 then b' ⟨j.val, h⟩ else v
      refine ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩, ?_⟩
      · simp [b, (Finset.mem_filter.mp hb').2.1]
      · simp [b]
      · simp [b, (Finset.mem_filter.mp hb').2.2]
      · funext j; dsimp only [b]; rw [dif_pos j.isLt]
    · intro b hb
      have hv := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2.2
      have hw := (Finset.mem_filter.mp hb).2
      rw [Fin.prod_univ_castSucc]
      congr 1
      simp only [Fin.val_last, hw, hv]

private lemma card_entries_eq_exits (n : ℕ) (S : Finset (Fin n)) :
    (Finset.univ.filter (fun i : Fin n => i ∉ S ∧ nextC n i ∈ S)).card = (exitsS n S).card := by
  have hsum : (∑ i : Fin n, ((if nextC n i ∈ S then (1 : ℤ) else 0) - (if i ∈ S then 1 else 0))) = 0 := by
    rw [Finset.sum_sub_distrib]
    have hbij : ∑ i : Fin n, (if nextC n i ∈ S then (1 : ℤ) else 0) =
        ∑ i : Fin n, (if i ∈ S then (1 : ℤ) else 0) :=
      Fintype.sum_bijective (nextC n) (nextC_bijective n) _ _ fun _ => rfl
    rw [hbij, sub_self]
  have hterm : ∀ i : Fin n, (if nextC n i ∈ S then (1 : ℤ) else 0) - (if i ∈ S then 1 else 0) =
      (if i ∉ S ∧ nextC n i ∈ S then 1 else 0) - (if i ∈ S ∧ nextC n i ∉ S then 1 else 0) := by
    intro i; by_cases h1 : i ∈ S <;> by_cases h2 : nextC n i ∈ S <;> simp [h1, h2]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
    Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_one] at hsum
  have heq : (Finset.univ.filter (fun i : Fin n => i ∈ S ∧ nextC n i ∉ S)) = exitsS n S := by
    ext i; simp [exitsS]
  rw [heq] at hsum
  omega

private lemma prod_step2_eq_pow (n : ℕ) (q : ℝ) (S : Finset (Fin n)) :
    ∏ i : Fin n, step2 q (decide (i ∈ S)) (decide (nextC n i ∈ S)) = q ^ (exitsS n S).card := by
  rw [← card_entries_eq_exits n S]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : Fin n => i ∉ S ∧ nextC n i ∈ S)]
  have h1 : ∏ i ∈ Finset.univ.filter (fun i : Fin n => i ∉ S ∧ nextC n i ∈ S),
      step2 q (decide (i ∈ S)) (decide (nextC n i ∈ S)) =
      q ^ (Finset.univ.filter (fun i : Fin n => i ∉ S ∧ nextC n i ∈ S)).card := by
    have heq : ∀ i ∈ Finset.univ.filter (fun i : Fin n => i ∉ S ∧ nextC n i ∈ S),
        step2 q (decide (i ∈ S)) (decide (nextC n i ∈ S)) = q := fun i hi => by
      have h := (Finset.mem_filter.mp hi).2
      simp [step2, h.1, h.2]
    rw [Finset.prod_congr rfl heq, Finset.prod_const]
  have h2 : ∏ i ∈ Finset.univ.filter (fun i : Fin n => ¬ (i ∉ S ∧ nextC n i ∈ S)),
      step2 q (decide (i ∈ S)) (decide (nextC n i ∈ S)) = 1 :=
    Finset.prod_eq_one fun i hi => by
      have h := (Finset.mem_filter.mp hi).2
      dsimp only [step2]; rw [if_neg]; intro hc; exact h ⟨by simpa using hc.1, by simpa using hc.2⟩
  rw [h1, h2, mul_one]

private lemma sum_W_all (n : ℕ) (hn : 1 ≤ n) (q : ℝ) (hq : 0 < q) :
    ∑ S : Finset (Fin n), q ^ (exitsS n S).card =
      (1 + Real.sqrt q) ^ n + (1 - Real.sqrt q) ^ n := by
  have h1 : ∑ S : Finset (Fin n), q ^ (exitsS n S).card =
      ∑ b : Fin n → Bool, ∏ i : Fin n, step2 q (b i) (b (nextC n i)) := by
    refine Finset.sum_bij (fun S _ => fun i => decide (i ∈ S)) (fun _ _ => Finset.mem_univ _)
      (fun S1 _ S2 _ heq => by ext i; have := congrFun heq i; simpa using this)
      (fun b _ => ⟨Finset.univ.filter (fun i => b i = true), Finset.mem_univ _, by funext i; simp⟩)
      (fun S _ => (prod_step2_eq_pow n q S).symm)
  rw [h1]
  have hsplit : ∑ b : Fin n → Bool, ∏ i : Fin n, step2 q (b i) (b (nextC n i)) =
      ∑ u : Bool, ∑ b ∈ (Finset.univ : Finset (Fin n → Bool)).filter (fun b => b ⟨0, hn⟩ = u),
        ∏ i : Fin n, step2 q (b i) (b (nextC n i)) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun b : Fin n → Bool => b ⟨0, hn⟩)
      (t := (Finset.univ : Finset Bool)) (fun _ _ => Finset.mem_univ _)]
  rw [hsplit]
  have heach : ∀ u : Bool,
      ∑ b ∈ (Finset.univ : Finset (Fin n → Bool)).filter (fun b => b ⟨0, hn⟩ = u),
        ∏ i : Fin n, step2 q (b i) (b (nextC n i)) = mat2Pow q n u u := by
    intro u
    rw [← sum_path_step2 q hq n u u]
    refine Finset.sum_bij (fun b _ => fun j : Fin (n + 1) => b ⟨j.val % n, Nat.mod_lt _ hn⟩) ?_ ?_ ?_ ?_
    · intro b hb
      have h0 := (Finset.mem_filter.mp hb).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · simpa using h0
      · simpa [Nat.mod_self] using h0
    · intro b1 _ b2 _ heq
      funext i
      have hi := congrFun heq ⟨i.val, by omega⟩
      dsimp only at hi
      rwa [show (⟨i.val % n, Nat.mod_lt _ hn⟩ : Fin n) = i from Fin.ext (Nat.mod_eq_of_lt i.isLt)] at hi
    · intro p hp
      have hp0 := (Finset.mem_filter.mp hp).2.1
      have hpn := (Finset.mem_filter.mp hp).2.2
      refine ⟨fun i => p ⟨i.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp0⟩, ?_⟩
      funext j
      by_cases hj : j.val < n
      · simp [Nat.mod_eq_of_lt hj]
      · have hjeq : j = ⟨n, by omega⟩ := Fin.ext (by dsimp only; have := j.isLt; omega)
        rw [hjeq]; simp [Nat.mod_self, hp0, hpn]
    · intro b _
      refine Finset.prod_congr rfl fun i _ => ?_
      dsimp only
      have hi1 : (⟨i.val % n, Nat.mod_lt _ hn⟩ : Fin n) = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
      rw [hi1]; rfl
  rw [Finset.sum_congr rfl fun u _ => heach u, Fintype.sum_bool]
  simp [mat2Pow]

private lemma sum_W_proper (n : ℕ) (hn : 1 ≤ n) (q : ℝ) (hq : 0 < q) :
    ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S ≠ ∅ ∧ S ≠ Finset.univ),
      q ^ (exitsS n S).card =
      (1 + Real.sqrt q) ^ n + (1 - Real.sqrt q) ^ n - 2 := by
  have hne_eu : (∅ : Finset (Fin n)) ≠ Finset.univ := by
    intro h; have : (⟨0, hn⟩ : Fin n) ∈ (∅ : Finset (Fin n)) := h.symm ▸ Finset.mem_univ _
    exact Finset.notMem_empty _ this
  have hall := sum_W_all n hn q hq
  have hpart : Finset.univ.filter (fun S : Finset (Fin n) => S ≠ ∅ ∧ S ≠ Finset.univ) =
      (Finset.univ.erase (∅ : Finset (Fin n))).erase Finset.univ := by
    ext S; simp [and_comm]
  rw [hpart]
  have hu_mem : (Finset.univ : Finset (Fin n)) ∈ (Finset.univ : Finset (Finset (Fin n))).erase ∅ :=
    Finset.mem_erase.mpr ⟨hne_eu.symm, Finset.mem_univ _⟩
  have h1 := Finset.add_sum_erase ((Finset.univ : Finset (Finset (Fin n))).erase ∅)
    (fun S => q ^ (exitsS n S).card) hu_mem
  have h2 := Finset.add_sum_erase (Finset.univ : Finset (Finset (Fin n)))
    (fun S => q ^ (exitsS n S).card) (Finset.mem_univ (∅ : Finset (Fin n)))
  have hex_e : exitsS n ∅ = ∅ := by ext i; simp [exitsS]
  have hex_u : exitsS n Finset.univ = ∅ := by ext i; simp [exitsS]
  rw [hex_e, Finset.card_empty, pow_zero] at h2
  rw [hex_u, Finset.card_empty, pow_zero] at h1
  linarith

private lemma sum_W_small_m_le (n : ℕ) (hn : 1 ≤ n) (q : ℝ) (hq : 4 ≤ q) (B : ℕ) :
    ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => (exitsS n S).card < B),
      q ^ (exitsS n S).card ≤
      2 * (4 : ℝ) ^ B * ((3 / 4 : ℝ) * (1 + Real.sqrt q)) ^ n := by
  have hq4_pos : 0 < q / 4 := by linarith
  have hle1 : ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => (exitsS n S).card < B),
      q ^ (exitsS n S).card ≤
      (4 : ℝ) ^ B * ∑ S : Finset (Fin n), (q / 4) ^ (exitsS n S).card := by
    rw [Finset.mul_sum]
    calc ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => (exitsS n S).card < B), q ^ (exitsS n S).card
        ≤ ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => (exitsS n S).card < B), (4 : ℝ) ^ B * (q / 4) ^ (exitsS n S).card := by
            refine Finset.sum_le_sum fun S hS => ?_
            have hlt := (Finset.mem_filter.mp hS).2
            calc q ^ (exitsS n S).card = ((4 : ℝ) * (q / 4)) ^ (exitsS n S).card := by ring
              _ = (4 : ℝ) ^ (exitsS n S).card * (q / 4) ^ (exitsS n S).card := mul_pow _ _ _
              _ ≤ (4 : ℝ) ^ B * (q / 4) ^ (exitsS n S).card :=
                  mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (le_of_lt hlt)) (by positivity)
      _ ≤ ∑ S : Finset (Fin n), (4 : ℝ) ^ B * (q / 4) ^ (exitsS n S).card :=
            Finset.sum_le_univ_sum_of_nonneg fun _ => by positivity
  rw [sum_W_all n hn (q / 4) hq4_pos] at hle1
  have hs_eq : Real.sqrt (q / 4) = Real.sqrt q / 2 := by
    rw [Real.sqrt_div (by linarith), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  have hsq_ge2 : 2 ≤ Real.sqrt q := by
    calc (2 : ℝ) = Real.sqrt (2 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt q := Real.sqrt_le_sqrt (by linarith)
  have hL_le : 1 + Real.sqrt (q / 4) ≤ (3 / 4 : ℝ) * (1 + Real.sqrt q) := by
    rw [hs_eq]; linarith
  have hL'_abs : |1 - Real.sqrt (q / 4)| ≤ 1 + Real.sqrt (q / 4) := by
    rw [abs_le]; constructor <;> linarith [Real.sqrt_nonneg (q / 4)]
  have hpow2 : (1 - Real.sqrt (q / 4)) ^ n ≤ (1 + Real.sqrt (q / 4)) ^ n := by
    calc (1 - Real.sqrt (q / 4)) ^ n ≤ |(1 - Real.sqrt (q / 4)) ^ n| := le_abs_self _
      _ = |1 - Real.sqrt (q / 4)| ^ n := abs_pow _ _
      _ ≤ (1 + Real.sqrt (q / 4)) ^ n := pow_le_pow_left₀ (abs_nonneg _) hL'_abs n
  have hpow3 : (1 + Real.sqrt (q / 4)) ^ n ≤ ((3 / 4 : ℝ) * (1 + Real.sqrt q)) ^ n :=
    pow_le_pow_left₀ (by positivity) hL_le n
  calc _ ≤ (4 : ℝ) ^ B * ((1 + Real.sqrt (q / 4)) ^ n + (1 - Real.sqrt (q / 4)) ^ n) := hle1
    _ ≤ (4 : ℝ) ^ B * (2 * ((3 / 4 : ℝ) * (1 + Real.sqrt q)) ^ n) := by
        refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 2 * (4 : ℝ) ^ B * ((3 / 4 : ℝ) * (1 + Real.sqrt q)) ^ n := by ring

private lemma sum_union_le_nonneg {α : Type*} [DecidableEq α] {s t : Finset α} {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) : ∑ x ∈ s ∪ t, f x ≤ ∑ x ∈ s, f x + ∑ x ∈ t, f x := by
  have h := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := f)
  have hnn : 0 ≤ ∑ x ∈ s ∩ t, f x := Finset.sum_nonneg fun x _ => hf x
  linarith

private lemma sum_biUnion_le_sum_nonneg {ι α : Type*} [DecidableEq α] {s : Finset ι}
    {t : ι → Finset α} {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    exact (sum_union_le_nonneg hf).trans (add_le_add le_rfl ih)

private lemma sum_W_big_gap_le (n g0 : ℕ) (hg1 : 1 ≤ g0) (hgn : g0 < n) (q : ℝ) (hq : 1 ≤ q) :
    ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => ∃ a ∈ exitsS n S, g0 ≤ gapS n S a),
      q ^ (exitsS n S).card ≤
      (n : ℝ) * Real.sqrt q * (1 + Real.sqrt q) ^ (n - g0) := by
  have hq_pos : 0 < q := by linarith
  have hsub : (Finset.univ : Finset (Finset (Fin n))).filter (fun S => ∃ a ∈ exitsS n S, g0 ≤ gapS n S a) ⊆
      (Finset.univ : Finset (Fin n)).biUnion (fun a =>
        Finset.univ.filter (fun S : Finset (Fin n) => a ∈ S ∧ ∀ v < g0, moveC n a (v + 1) ∉ S)) := by
    intro S hS
    rcases (Finset.mem_filter.mp hS).2 with ⟨a, ha, hge⟩
    have haS := (Finset.mem_filter.mp ha).1
    have hspec := (gapS_iff n S haS (gapS n S a)).mp rfl
    exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, haS, fun v hv => hspec.2.1 v (lt_of_lt_of_le hv hge)⟩⟩
  have hone : ∀ a : Fin n,
      ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => a ∈ S ∧ ∀ v < g0, moveC n a (v + 1) ∉ S),
        q ^ (exitsS n S).card = mat2Pow q (n - g0) false true := by
    intro a
    rw [← sum_path_step2 q hq_pos (n - g0) false true]
    refine Finset.sum_bij (fun S _ => fun j : Fin (n - g0 + 1) => decide (moveC n a (g0 + j.val) ∈ S)) ?_ ?_ ?_ ?_
    · intro S hS
      rcases (Finset.mem_filter.mp hS).2 with ⟨haS, hnot⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · have h0 := hnot (g0 - 1) (by omega)
        rw [Nat.sub_add_cancel hg1] at h0
        simp [h0]
      · simp [show g0 + (n - g0) = n by omega, moveC_self, haS]
    · intro S1 hS1 S2 hS2 heq
      rcases (Finset.mem_filter.mp hS1).2 with ⟨ha1, hnot1⟩
      rcases (Finset.mem_filter.mp hS2).2 with ⟨ha2, hnot2⟩
      ext x
      have hpos_n : 0 < n := by omega
      let d := (x.val + n - a.val) % n
      have hd_lt : d < n := Nat.mod_lt _ hpos_n
      have hx_eq : moveC n a d = x := moveC_mod_sub n a x
      rw [← hx_eq]
      by_cases hd0 : d = 0
      · rw [hd0, moveC_zero]; simp [ha1, ha2]
      · by_cases hdg : d ≤ g0
        · have h1 := hnot1 (d - 1) (by omega)
          have h2 := hnot2 (d - 1) (by omega)
          rw [Nat.sub_add_cancel (by omega)] at h1 h2
          simp [h1, h2]
        · have hval := congrFun heq ⟨d - g0, by omega⟩
          dsimp only at hval
          rw [show g0 + (d - g0) = d by omega] at hval
          simpa using hval
    · intro p hp
      have hp0 := (Finset.mem_filter.mp hp).2.1
      have hpn := (Finset.mem_filter.mp hp).2.2
      let S : Finset (Fin n) := (Finset.univ : Finset (Fin (n - g0 + 1))).filter (fun j => p j = true) |>.image
        (fun j => moveC n a (g0 + j.val))
      have hmem_S : ∀ (k : ℕ) (hk : k < n), moveC n a k ∈ S ↔ (k = 0 ∨ (g0 ≤ k ∧ p ⟨k - g0, by omega⟩ = true)) := by
        intro k hk
        simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨j, hj, heq⟩
          by_cases hjlast : j.val = n - g0
          · left
            have h1 : moveC n a (g0 + j.val) = moveC n a 0 := by
              rw [show g0 + j.val = n by omega, moveC_self, moveC_zero]
            exact (moveC_injective_lt n a (by omega) hk (h1.symm.trans heq)).symm
          · have hlt_j : g0 + j.val < n := by have := j.isLt; omega
            have hkeq : g0 + j.val = k := moveC_injective_lt n a hlt_j hk heq
            right; refine ⟨by omega, ?_⟩
            have hje : (⟨k - g0, by omega⟩ : Fin (n - g0 + 1)) = j := Fin.ext (by dsimp only; omega)
            rwa [hje]
        · rintro (rfl | ⟨hge, hpj⟩)
          · refine ⟨⟨n - g0, by omega⟩, hpn, ?_⟩
            rw [show g0 + (n - g0) = n by omega, moveC_self, moveC_zero]
          · refine ⟨⟨k - g0, by omega⟩, hpj, ?_⟩
            rw [show g0 + (k - g0) = k by omega]
      have haS : a ∈ S := by rw [← moveC_zero n a, hmem_S 0 (by omega)]; left; rfl
      have hnot : ∀ v < g0, moveC n a (v + 1) ∉ S := by
        intro v hv hm
        rw [hmem_S (v + 1) (by omega)] at hm
        rcases hm with h0 | ⟨hge, hpj⟩
        · omega
        · have hv' : v + 1 = g0 := by omega
          have h0 : (⟨v + 1 - g0, by omega⟩ : Fin (n - g0 + 1)) = 0 := Fin.ext (by simp [hv'])
          rw [h0, hp0] at hpj; cases hpj
      refine ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, haS, hnot⟩, ?_⟩
      funext j
      by_cases hj : j.val < n - g0
      · have hlt : g0 + j.val < n := by omega
        have hm := hmem_S (g0 + j.val) hlt
        have hsub : (⟨g0 + j.val - g0, by omega⟩ : Fin (n - g0 + 1)) = j := Fin.ext (by dsimp only; omega)
        rw [hsub] at hm
        have hiff : moveC n a (g0 + j.val) ∈ S ↔ p j = true := by
          rw [hm]; constructor
          · rintro (h0 | ⟨_, h⟩)
            · omega
            · exact h
          · intro h; right; exact ⟨by omega, h⟩
        cases hpj : p j <;> simp [hiff, hpj]
      · have hjeq : j = ⟨n - g0, by omega⟩ := Fin.ext (by dsimp only; have := j.isLt; omega)
        rw [hjeq, hpn]; simp [show g0 + (n - g0) = n by omega, moveC_self, haS]
    · intro S hS
      rcases (Finset.mem_filter.mp hS).2 with ⟨haS, hnot⟩
      rw [← prod_step2_eq_pow n q S]
      let eShift : Fin n ≃ Fin n :=
        { toFun := fun k => moveC n a k.val
          invFun := fun x => ⟨(x.val + n - a.val) % n, Nat.mod_lt _ (by omega)⟩
          left_inv := fun k => Fin.ext (mod_sub_moveC n a k.isLt)
          right_inv := fun x => moveC_mod_sub n a x }
      rw [← Fintype.prod_equiv eShift (fun k => step2 q (decide (moveC n a k.val ∈ S)) (decide (nextC n (moveC n a k.val) ∈ S)))
        (fun i => step2 q (decide (i ∈ S)) (decide (nextC n i ∈ S))) (fun _ => rfl)]
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k : Fin n => k.val < g0)]
      have hpref : ∏ k ∈ Finset.univ.filter (fun k : Fin n => k.val < g0),
          step2 q (decide (moveC n a k.val ∈ S)) (decide (nextC n (moveC n a k.val) ∈ S)) = 1 :=
        Finset.prod_eq_one fun k hk => by
          have hlt := (Finset.mem_filter.mp hk).2
          have hnm : nextC n (moveC n a k.val) ∉ S := by
            rw [← moveC_one, moveC_add]; exact hnot k.val hlt
          simp [step2, hnm]
      rw [hpref, one_mul]
      refine Finset.prod_bij (fun k hk => (⟨k.val - g0, by have := (Finset.mem_filter.mp hk).2; omega⟩ : Fin (n - g0)))
        (fun _ _ => Finset.mem_univ _)
        (fun k1 hk1 k2 hk2 heq => by
          have h1 := (Finset.mem_filter.mp hk1).2; have h2 := (Finset.mem_filter.mp hk2).2
          have hv := congrArg Fin.val heq; dsimp only at hv; exact Fin.ext (by omega))
        (fun j _ => ⟨⟨g0 + j.val, by have := j.isLt; omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩, Fin.ext (by simp)⟩)
        (fun k hk => by
          have hge : g0 ≤ k.val := not_lt.mp (Finset.mem_filter.mp hk).2
          dsimp only
          rw [show g0 + (k.val - g0) = k.val by omega, show g0 + (k.val - g0 + 1) = k.val + 1 by omega,
            ← moveC_add, moveC_one])
  have hmat_le : mat2Pow q (n - g0) false true ≤ Real.sqrt q * (1 + Real.sqrt q) ^ (n - g0) := by
    dsimp only [mat2Pow]
    have hsq_pos : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
    have hL'_abs : |1 - Real.sqrt q| ≤ 1 + Real.sqrt q := by rw [abs_le]; constructor <;> linarith
    have hpow : -(1 + Real.sqrt q) ^ (n - g0) ≤ (1 - Real.sqrt q) ^ (n - g0) := by
      have h1 : |(1 - Real.sqrt q) ^ (n - g0)| ≤ (1 + Real.sqrt q) ^ (n - g0) := by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hL'_abs _
      exact (abs_le.mp h1).1
    nlinarith
  calc ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => ∃ a ∈ exitsS n S, g0 ≤ gapS n S a), q ^ (exitsS n S).card
      ≤ ∑ S ∈ (Finset.univ : Finset (Fin n)).biUnion (fun a =>
          Finset.univ.filter (fun S : Finset (Fin n) => a ∈ S ∧ ∀ v < g0, moveC n a (v + 1) ∉ S)), q ^ (exitsS n S).card :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ ∑ a : Fin n, ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => a ∈ S ∧ ∀ v < g0, moveC n a (v + 1) ∉ S),
          q ^ (exitsS n S).card :=
          sum_biUnion_le_sum_nonneg fun _ => by positivity
    _ = ∑ _a : Fin n, mat2Pow q (n - g0) false true := Finset.sum_congr rfl fun a _ => hone a
    _ = (n : ℝ) * mat2Pow q (n - g0) false true := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ (n : ℝ) * (Real.sqrt q * (1 + Real.sqrt q) ^ (n - g0)) := mul_le_mul_of_nonneg_left hmat_le (Nat.cast_nonneg n)
    _ = (n : ℝ) * Real.sqrt q * (1 + Real.sqrt q) ^ (n - g0) := by ring

private def step3 (q eps : ℝ) (bit : Bool) (u v : Fin 3) : ℝ :=
  if u = 0 then
    if v = 0 then 1 else if v = (if bit then 2 else 1) then q else 0
  else if u = 1 then
    if v = 0 then 1 else if v = (if bit then 2 else 1) then 1 else 0
  else
    if v = 0 then eps else if v = (if bit then 1 else 2) then 1 else 0

private lemma step3_nonneg (q eps : ℝ) (hq : 0 ≤ q) (heps : 0 ≤ eps) (bit : Bool) (u v : Fin 3) :
    0 ≤ step3 q eps bit u v := by
  dsimp only [step3]; split_ifs <;> linarith

private lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma step3_stay (q eps : ℝ) (b1 p0 : ZMod 2) :
    step3 q eps (decide (b1 ≠ 0)) (if p0 = 0 then 1 else 2) (if b1 + p0 = 0 then 1 else 2) = 1 := by
  rcases zmod2_cases b1 with rfl | rfl <;> rcases zmod2_cases p0 with rfl | rfl <;>
    (dsimp only [step3]; simp [show (1 : ZMod 2) + 1 = 0 by decide])

private lemma step3_enter (q eps : ℝ) (b1 : ZMod 2) :
    step3 q eps (decide (b1 ≠ 0)) 0 (if b1 = 0 then 1 else 2) = q := by
  rcases zmod2_cases b1 with rfl | rfl <;> (dsimp only [step3]; simp)

private lemma step3_vec_bound (q : ℝ) (hL6 : 6 ≤ 1 + Real.sqrt q) (bit : Bool) :
    let s := Real.sqrt q
    let L := 1 + s
    let v : Fin 3 → ℝ := fun u => if u = 0 then s else if u = 1 then 1 else 3 / L
    ∀ u : Fin 3,
      ∑ w : Fin 3, step3 q (1 / L) bit u w * v w ≤
        (if bit then (1 - 1 / (2 * L)) * L else L) * v u := by
  intro s L v u
  have hs5 : 5 ≤ s := by dsimp only [s]; linarith
  have hq_nn : 0 ≤ q := by
    by_contra hlt; push_neg at hlt
    have : s = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_lt hlt)
    linarith
  have hsq : s * s = q := Real.mul_self_sqrt hq_nn
  have hL_pos : 0 < L := by dsimp only [L]; linarith
  have hL_ne : L ≠ 0 := ne_of_gt hL_pos
  rw [Fin.sum_univ_three]
  cases bit <;> fin_cases u <;> simp [step3, v]
  · dsimp only [L]; nlinarith [hsq]
  · dsimp only [L]; linarith
  · have h1 : L⁻¹ * s + 3 / L ≤ 3 := by
      have hm : (L⁻¹ * s + 3 / L) * L ≤ 3 * L := by
        have hl : (L⁻¹ * s + 3 / L) * L = s + 3 := by field_simp [hL_ne]
        rw [hl]; dsimp only [L]; linarith
      exact le_of_mul_le_mul_right hm hL_pos
    have h2 : L * (3 / L) = 3 := by field_simp [hL_ne]
    linarith
  · refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < 2 * L)
    have hlhs : (s + q * (3 / L)) * (2 * L) = 2 * s * L + 6 * q := by field_simp [hL_ne]; ring
    have hrhs : ((1 - L⁻¹ * 2⁻¹) * L * s) * (2 * L) = (2 * L - 1) * L * s := by field_simp [hL_ne]
    rw [hlhs, hrhs]; dsimp only [L]; nlinarith [hsq]
  · refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < 2 * L)
    have hlhs : (s + 3 / L) * (2 * L) = 2 * s * L + 6 := by field_simp [hL_ne]; ring
    have hrhs : ((1 - L⁻¹ * 2⁻¹) * L) * (2 * L) = (2 * L - 1) * L := by field_simp [hL_ne]
    rw [hlhs, hrhs]; dsimp only [L]; nlinarith
  · refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < 2 * L)
    have hlhs : (L⁻¹ * s + 1) * (2 * L) = 2 * s + 2 * L := by field_simp [hL_ne]
    have hrhs : ((1 - L⁻¹ * 2⁻¹) * L * (3 / L)) * (2 * L) = 6 * L - 3 := by field_simp [hL_ne]; ring
    rw [hlhs, hrhs]; dsimp only [L]; linarith

set_option maxHeartbeats 800000 in
private lemma sum_W_bad_alpha_le (t : ℕ) (ht : 1 ≤ t) (q : ℝ) (hL6 : 6 ≤ 1 + Real.sqrt q)
    (α : Fin 4 → ZMod 2) (hα : α ≠ 0) :
    let n := 6 * t
    let L := 1 + Real.sqrt q
    ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
        (fun S => ∃ hne : S ≠ Finset.univ, S ≠ ∅ ∧ badRuns n S hne α < 10),
      q ^ (exitsS n S).card ≤
      L ^ 11 * (1 - 1 / (2 * L)) ^ t * L ^ n := by
  classical
  intro n L
  have hs5 : 5 ≤ Real.sqrt q := by linarith
  have hq_pos : 0 < q := by
    by_contra hle; push_neg at hle
    have : Real.sqrt q = 0 := Real.sqrt_eq_zero_of_nonpos hle; linarith
  have hL_pos : 0 < L := by linarith
  have hn_pos : 0 < n := by dsimp only [n]; omega
  let bit : Fin n → Bool := fun i => decide ((∑ b : Fin 4, α b * hMat n i b) ≠ 0)
  let eps : ℝ := 1 / L
  have heps_pos : 0 < eps := by dsimp only [eps]; positivity
  let goodStates : Finset (Fin n → Fin 3) := Finset.univ
  have htr_bound : ∑ st : Fin n → Fin 3, ∏ i : Fin n, step3 q eps (bit (nextC n i)) (st i) (st (nextC n i)) ≤
      L ^ 2 * (1 - 1 / (2 * L)) ^ t * L ^ n := by
    let v : Fin 3 → ℝ := fun u => if u = 0 then Real.sqrt q else if u = 1 then 1 else 3 / L
    have hv_pos : ∀ u : Fin 3, 0 < v u := fun u => by fin_cases u <;> dsimp only [v] <;> positivity
    let fBit : ℕ → Bool := fun k => bit ⟨(k + 1) % n, Nat.mod_lt _ hn_pos⟩
    let stepM : ℕ → Fin 3 → Fin 3 → ℝ := fun k u w => step3 q eps (fBit k) u w
    have hpath_le : ∀ m : ℕ, ∀ u : Fin 3,
        (∑ p ∈ (Finset.univ : Finset (Fin (m + 1) → Fin 3)).filter (fun p => p 0 = u),
          (∏ k : Fin m, stepM k (p ⟨k.val, by omega⟩) (p ⟨k.val + 1, by omega⟩)) * v (p ⟨m, by omega⟩)) ≤
        (∏ k : Fin m, (if fBit k.val then (1 - 1 / (2 * L)) * L else L)) * v u := by
      intro m
      induction m with
      | zero =>
        intro u
        have hsing : ((Finset.univ : Finset (Fin 1 → Fin 3)).filter (fun p => p 0 = u)) = {fun _ => u} := by
          ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro h0; funext i; fin_cases i; exact h0
          · rintro rfl; rfl
        rw [hsing, Finset.sum_singleton]; simp
      | succ m ih =>
        intro u
        have hsplit : ∑ p ∈ (Finset.univ : Finset (Fin (m + 2) → Fin 3)).filter (fun p => p 0 = u),
            (∏ k : Fin (m + 1), stepM k (p ⟨k.val, by omega⟩) (p ⟨k.val + 1, by omega⟩)) * v (p ⟨m + 1, by omega⟩) =
            ∑ p' ∈ (Finset.univ : Finset (Fin (m + 1) → Fin 3)).filter (fun p => p 0 = u),
              (∏ k : Fin m, stepM k (p' ⟨k.val, by omega⟩) (p' ⟨k.val + 1, by omega⟩)) *
              (∑ w : Fin 3, stepM m (p' ⟨m, by omega⟩) w * v w) := by
          have hfib := (Finset.sum_fiberwise_of_maps_to
            (s := (Finset.univ : Finset (Fin (m + 2) → Fin 3)).filter (fun p => p 0 = u))
            (t := (Finset.univ : Finset (Fin (m + 1) → Fin 3)).filter (fun p => p 0 = u))
            (g := fun p => fun j : Fin (m + 1) => p ⟨j.val, by omega⟩)
            (f := fun p => (∏ k : Fin (m + 1), stepM k (p ⟨k.val, by omega⟩) (p ⟨k.val + 1, by omega⟩)) * v (p ⟨m + 1, by omega⟩))
            (fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩)).symm
          rw [hfib]
          refine Finset.sum_congr rfl fun p' hp' => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_bij (fun p _ => p ⟨m + 1, by omega⟩) (fun _ _ => Finset.mem_univ _)
            (fun p1 hp1 p2 hp2 heq => by
              have h1 := (Finset.mem_filter.mp hp1).2; have h2 := (Finset.mem_filter.mp hp2).2
              funext j; by_cases hj : j.val < m + 1
              · have := congrFun (h1.trans h2.symm) ⟨j.val, hj⟩; exact this
              · have hjeq : j = ⟨m + 1, by omega⟩ := Fin.ext (by dsimp only; have := j.isLt; omega); rw [hjeq]; exact heq)
            (fun w _ =>
              let p : Fin (m + 2) → Fin 3 := fun j => if h : j.val < m + 1 then p' ⟨j.val, h⟩ else w
              ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [p, (Finset.mem_filter.mp hp').2]⟩,
                by funext j; dsimp only [p]; rw [dif_pos j.isLt]⟩, by simp [p]⟩)
            (fun p hp => by
              have heq := (Finset.mem_filter.mp hp).2
              rw [Fin.prod_univ_castSucc, mul_assoc]
              congr 1
              · refine Finset.prod_congr rfl fun k _ => by
                  simp only [Fin.val_castSucc]
                  rw [show p ⟨k.val, by omega⟩ = p' ⟨k.val, by omega⟩ from congrFun heq ⟨k.val, by omega⟩,
                    show p ⟨k.val + 1, by omega⟩ = p' ⟨k.val + 1, by omega⟩ from congrFun heq ⟨k.val + 1, by omega⟩]
              · simp only [Fin.val_last]
                rw [show p ⟨m, by omega⟩ = p' ⟨m, by omega⟩ from congrFun heq ⟨m, by omega⟩])
        rw [hsplit]
        have hstep_le : ∑ p' ∈ (Finset.univ : Finset (Fin (m + 1) → Fin 3)).filter (fun p => p 0 = u),
            (∏ k : Fin m, stepM k (p' ⟨k.val, by omega⟩) (p' ⟨k.val + 1, by omega⟩)) *
            (∑ w : Fin 3, stepM m (p' ⟨m, by omega⟩) w * v w) ≤
            (if fBit m then (1 - 1 / (2 * L)) * L else L) *
            ∑ p' ∈ (Finset.univ : Finset (Fin (m + 1) → Fin 3)).filter (fun p => p 0 = u),
              (∏ k : Fin m, stepM k (p' ⟨k.val, by omega⟩) (p' ⟨k.val + 1, by omega⟩)) * v (p' ⟨m, by omega⟩) := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun p' _ => ?_
          have hnn : 0 ≤ ∏ k : Fin m, stepM k (p' ⟨k.val, by omega⟩) (p' ⟨k.val + 1, by omega⟩) :=
            Finset.prod_nonneg fun k _ => step3_nonneg q eps (le_of_lt hq_pos) (le_of_lt heps_pos) _ _ _
          have hvb := step3_vec_bound q hL6 (fBit m) (p' ⟨m, by omega⟩)
          calc _ ≤ (∏ k : Fin m, stepM k (p' ⟨k.val, by omega⟩) (p' ⟨k.val + 1, by omega⟩)) *
                ((if fBit m then (1 - 1 / (2 * L)) * L else L) * v (p' ⟨m, by omega⟩)) :=
                mul_le_mul_of_nonneg_left hvb hnn
            _ = _ := by ring
        have hfac_nn : 0 ≤ (if fBit m then (1 - 1 / (2 * L)) * L else L) := by
          split_ifs
          · have : 0 ≤ 1 - 1 / (2 * L) := by
              rw [sub_nonneg, div_le_one (by linarith)]; linarith
            exact mul_nonneg this (le_of_lt hL_pos)
          · exact le_of_lt hL_pos
        calc _ ≤ (if fBit m then (1 - 1 / (2 * L)) * L else L) *
              ((∏ k : Fin m, (if fBit k.val then (1 - 1 / (2 * L)) * L else L)) * v u) :=
              hstep_le.trans (mul_le_mul_of_nonneg_left (ih u) hfac_nn)
          _ = (∏ k : Fin (m + 1), (if fBit k.val then (1 - 1 / (2 * L)) * L else L)) * v u := by
              rw [Fin.prod_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]; ring
    have hprod_fBit : (∏ k : Fin n, (if fBit k.val then (1 - 1 / (2 * L)) * L else L)) ≤
        (1 - 1 / (2 * L)) ^ t * L ^ n := by
      have hfactor : ∀ k : Fin n, (if fBit k.val then (1 - 1 / (2 * L)) * L else L) =
          (if fBit k.val then 1 - 1 / (2 * L) else 1) * L := fun k => by split_ifs <;> ring
      rw [Finset.prod_congr rfl fun k _ => hfactor k, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (le_of_lt hL_pos) n)
      have h01 : 0 ≤ 1 - 1 / (2 * L) ∧ 1 - 1 / (2 * L) ≤ 1 := by
        constructor
        · rw [sub_nonneg, div_le_one (by linarith)]; linarith
        · linarith [show 0 < 1 / (2 * L) by positivity]
      have hex_r : ∃ r : Fin 6, ∀ m : Fin t, fBit (6 * m.val + r.val) = true := by
        have hex_b : ∃ b0 : Fin 4, α b0 ≠ 0 := by by_contra hall; push_neg at hall; exact hα (funext hall)
        rcases hex_b with ⟨b0, hb0⟩
        have hb1 : α b0 = 1 := by generalize α b0 = z at hb0 ⊢; fin_cases z <;> first | exact absurd rfl hb0 | rfl
        let idx6 : Fin 6 :=
          if b0 = 0 then 5 else if b0 = 1 then 1 else if b0 = 2 then 0 else 2
        refine ⟨idx6, fun m => ?_⟩
        dsimp only [fBit, bit]
        rw [decide_eq_true_eq]
        have hmod6 : ((6 * m.val + idx6.val + 1) % n) % 6 = (idx6.val + 1) % 6 := by
          have h6dvd : 6 ∣ n := ⟨t, rfl⟩
          rw [Nat.mod_mod_of_dvd _ h6dvd]
          rw [show 6 * m.val + idx6.val + 1 = (idx6.val + 1) + 6 * m.val by omega, Nat.add_mul_mod_self_left]
        have hh_eq : ∀ b : Fin 4, hMat n ⟨(6 * m.val + idx6.val + 1) % n, Nat.mod_lt _ hn_pos⟩ b =
            hMat 6 ⟨(idx6.val + 1) % 6, Nat.mod_lt _ (by omega)⟩ b := by
          intro b
          dsimp only [hMat]
          have hm2 : ((6 * m.val + idx6.val + 1) % n) % 2 = ((idx6.val + 1) % 6) % 2 := by
            rw [← Nat.mod_mod_of_dvd _ (show 2 ∣ 6 by decide), hmod6]
          have hm3 : ((6 * m.val + idx6.val + 1) % n) / 2 % 3 = ((idx6.val + 1) % 6) / 2 % 3 := by
            have hq : ∀ x : ℕ, x / 2 % 3 = (x % 6) / 2 % 3 := fun x => by omega
            rw [hq, hmod6]
          rw [hm2, hm3]
        simp_rw [hh_eq]
        fin_cases b0 <;> (rw [Fin.sum_univ_four]; dsimp only [idx6]; simp [hMat]; exact hb0)
      rcases hex_r with ⟨r0, hr0⟩
      let S_hit : Finset (Fin n) := Finset.univ.image (fun m : Fin t => ⟨6 * m.val + r0.val, by dsimp only [n]; omega⟩)
      have hShit_card : S_hit.card = t := by
        rw [Finset.card_image_of_injective _ (fun m1 m2 h => Fin.ext (by have := congrArg Fin.val h; dsimp only at this; omega)),
          Finset.card_univ, Fintype.card_fin]
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k : Fin n => k ∈ S_hit)]
      have hrest_le : ∏ k ∈ Finset.univ.filter (fun k : Fin n => k ∉ S_hit), (if fBit k.val then 1 - 1 / (2 * L) else 1) ≤ 1 :=
        (prod_le_prod_nonneg (g := fun _ => (1 : ℝ)) (fun k _ => by split_ifs <;> linarith) (fun k _ => by split_ifs <;> linarith)).trans (by simp)
      have hhit_eq : ∏ k ∈ Finset.univ.filter (fun k : Fin n => k ∈ S_hit), (if fBit k.val then 1 - 1 / (2 * L) else 1) =
          (1 - 1 / (2 * L)) ^ t := by
        have hfeq : Finset.univ.filter (fun k : Fin n => k ∈ S_hit) = S_hit := by ext k; simp
        rw [hfeq]
        have hall_t : ∀ k ∈ S_hit, (if fBit k.val then 1 - 1 / (2 * L) else 1) = 1 - 1 / (2 * L) := by
          intro k hk
          rcases Finset.mem_image.mp hk with ⟨m, _, rfl⟩
          rw [if_pos (hr0 m)]
        rw [Finset.prod_congr rfl hall_t, Finset.prod_const, hShit_card]
      rw [hhit_eq]
      calc (1 - 1 / (2 * L)) ^ t * _ ≤ (1 - 1 / (2 * L)) ^ t * 1 := mul_le_mul_of_nonneg_left hrest_le (pow_nonneg h01.1 t)
        _ = (1 - 1 / (2 * L)) ^ t := mul_one _
    have hsum_u : ∀ u : Fin 3,
        (∑ st ∈ (Finset.univ : Finset (Fin n → Fin 3)).filter (fun st => st ⟨0, hn_pos⟩ = u),
          ∏ i : Fin n, step3 q eps (bit (nextC n i)) (st i) (st (nextC n i))) ≤
        (1 / v u) * ((1 - 1 / (2 * L)) ^ t * L ^ n * v u) := by
      intro u
      have hle_p : (∑ st ∈ (Finset.univ : Finset (Fin n → Fin 3)).filter (fun st => st ⟨0, hn_pos⟩ = u),
          ∏ i : Fin n, step3 q eps (bit (nextC n i)) (st i) (st (nextC n i))) * v u ≤
          (∑ p ∈ (Finset.univ : Finset (Fin (n + 1) → Fin 3)).filter (fun p => p 0 = u),
            (∏ k : Fin n, stepM k (p ⟨k.val, by omega⟩) (p ⟨k.val + 1, by omega⟩)) * v (p ⟨n, by omega⟩)) := by
        rw [Finset.sum_mul]
        let embP : (Fin n → Fin 3) → (Fin (n + 1) → Fin 3) := fun st j => st ⟨j.val % n, Nat.mod_lt _ hn_pos⟩
        have hemb_inj : Set.InjOn embP (((Finset.univ : Finset (Fin n → Fin 3)).filter (fun st => st ⟨0, hn_pos⟩ = u)) : Set (Fin n → Fin 3)) := by
          intro st1 _ st2 _ heq
          funext i; have hi := congrFun heq ⟨i.val, by omega⟩; dsimp only [embP] at hi
          rwa [show (⟨i.val % n, Nat.mod_lt _ hn_pos⟩ : Fin n) = i from Fin.ext (Nat.mod_eq_of_lt i.isLt)] at hi
        calc ∑ st ∈ (Finset.univ : Finset (Fin n → Fin 3)).filter (fun st => st ⟨0, hn_pos⟩ = u),
              (∏ i : Fin n, step3 q eps (bit (nextC n i)) (st i) (st (nextC n i))) * v u
            = ∑ st ∈ (Finset.univ : Finset (Fin n → Fin 3)).filter (fun st => st ⟨0, hn_pos⟩ = u),
                (∏ k : Fin n, stepM k (embP st ⟨k.val, by omega⟩) (embP st ⟨k.val + 1, by omega⟩)) * v (embP st ⟨n, by omega⟩) := by
              refine Finset.sum_congr rfl fun st hst => ?_
              have h0 := (Finset.mem_filter.mp hst).2
              dsimp only [embP]
              have hlast : st ⟨n % n, Nat.mod_lt _ hn_pos⟩ = u := by simpa [Nat.mod_self] using h0
              rw [hlast]
              refine congrArg (· * v u) (Finset.prod_congr rfl fun k _ => ?_)
              have hk : (⟨k.val % n, Nat.mod_lt _ hn_pos⟩ : Fin n) = k := Fin.ext (Nat.mod_eq_of_lt k.isLt)
              rw [hk]; rfl
          _ = ∑ p ∈ ((Finset.univ : Finset (Fin n → Fin 3)).filter (fun st => st ⟨0, hn_pos⟩ = u)).image embP,
                (∏ k : Fin n, stepM k (p ⟨k.val, by omega⟩) (p ⟨k.val + 1, by omega⟩)) * v (p ⟨n, by omega⟩) :=
              (Finset.sum_image (f := fun p : Fin (n + 1) → Fin 3 =>
                (∏ k : Fin n, stepM k (p ⟨k.val, by omega⟩) (p ⟨k.val + 1, by omega⟩)) * v (p ⟨n, by omega⟩)) hemb_inj).symm
          _ ≤ ∑ p ∈ (Finset.univ : Finset (Fin (n + 1) → Fin 3)).filter (fun p => p 0 = u),
                (∏ k : Fin n, stepM k (p ⟨k.val, by omega⟩) (p ⟨k.val + 1, by omega⟩)) * v (p ⟨n, by omega⟩) :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (fun p hp => by
                  rcases Finset.mem_image.mp hp with ⟨st, hst, rfl⟩
                  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [embP] using (Finset.mem_filter.mp hst).2⟩)
                (fun p _ _ => mul_nonneg (Finset.prod_nonneg fun _ _ => step3_nonneg q eps (le_of_lt hq_pos) (le_of_lt heps_pos) _ _ _) (le_of_lt (hv_pos _)))
      have htot := hle_p.trans (hpath_le n u)
      have htot2 := htot.trans (mul_le_mul_of_nonneg_right hprod_fBit (le_of_lt (hv_pos u)))
      have hvne : v u ≠ 0 := ne_of_gt (hv_pos u)
      rw [one_div, inv_mul_eq_div, le_div_iff₀ (hv_pos u)]
      exact htot2
    have hsplit_st : ∑ st : Fin n → Fin 3, ∏ i : Fin n, step3 q eps (bit (nextC n i)) (st i) (st (nextC n i)) =
        ∑ u : Fin 3, ∑ st ∈ (Finset.univ : Finset (Fin n → Fin 3)).filter (fun st => st ⟨0, hn_pos⟩ = u),
          ∏ i : Fin n, step3 q eps (bit (nextC n i)) (st i) (st (nextC n i)) := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := fun st : Fin n → Fin 3 => st ⟨0, hn_pos⟩)
        (t := (Finset.univ : Finset (Fin 3))) (fun _ _ => Finset.mem_univ _)]
    rw [hsplit_st]
    calc _ ≤ ∑ u : Fin 3, (1 / v u) * ((1 - 1 / (2 * L)) ^ t * L ^ n * v u) := Finset.sum_le_sum fun u _ => hsum_u u
      _ = 3 * ((1 - 1 / (2 * L)) ^ t * L ^ n) := by
          rw [Fin.sum_univ_three]
          have h0 : 1 / v 0 * ((1 - 1 / (2 * L)) ^ t * L ^ n * v 0) = (1 - 1 / (2 * L)) ^ t * L ^ n := by
            field_simp [ne_of_gt (hv_pos 0)]
          have h1 : 1 / v 1 * ((1 - 1 / (2 * L)) ^ t * L ^ n * v 1) = (1 - 1 / (2 * L)) ^ t * L ^ n := by
            field_simp [ne_of_gt (hv_pos 1)]
          have h2 : 1 / v 2 * ((1 - 1 / (2 * L)) ^ t * L ^ n * v 2) = (1 - 1 / (2 * L)) ^ t * L ^ n := by
            field_simp [ne_of_gt (hv_pos 2)]
          rw [h0, h1, h2]; ring
      _ ≤ L ^ 2 * (1 - 1 / (2 * L)) ^ t * L ^ n := by
          have h3L2 : (3 : ℝ) ≤ L ^ 2 := by nlinarith
          have hnn : 0 ≤ (1 - 1 / (2 * L)) ^ t * L ^ n := by
            have h1 : 0 ≤ 1 - 1 / (2 * L) := by rw [sub_nonneg, div_le_one (by linarith)]; linarith
            exact mul_nonneg (pow_nonneg h1 t) (pow_nonneg (le_of_lt hL_pos) n)
          nlinarith
  let badS := (Finset.univ : Finset (Finset (Fin n))).filter
    (fun S => ∃ hne : S ≠ Finset.univ, S ≠ ∅ ∧ badRuns n S hne α < 10)
  let mkSt : ∀ S : Finset (Fin n), Fin n → Fin 3 := fun S i =>
    if h : S ≠ Finset.univ ∧ i ∈ S then
      let k0 := Nat.find (show ∃ k < n, moveC n i (n - k) ∉ S by
        have hcomp : ∃ j : Fin n, j ∉ S := by
          by_contra hall; push_neg at hall; exact h.1 (Finset.eq_univ_iff_forall.mpr hall)
        rcases hcomp with ⟨j, hj⟩
        let d := (i.val + n - j.val) % n
        have hd_pos : 0 < d := by
          by_contra h0; have hd0 : d = 0 := by omega
          have hij : i = j := by
            ext; dsimp only [d] at hd0
            have := i.isLt; have := j.isLt
            by_cases hle : j.val ≤ i.val
            · have : (i.val + n - j.val) % n = i.val - j.val := by
                rw [show i.val + n - j.val = (i.val - j.val) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
              omega
            · have : (i.val + n - j.val) % n = i.val + n - j.val := Nat.mod_eq_of_lt (by omega)
              omega
          exact hj (hij ▸ h.2)
        have hd_lt : d < n := Nat.mod_lt _ hn_pos
        refine ⟨d, hd_lt, ?_⟩
        have hm : moveC n i (n - d) = j := by
          ext; simp only [moveC]
          have := i.isLt; have := j.isLt
          by_cases hle : j.val ≤ i.val
          · have hd_eq : d = i.val - j.val := by
              dsimp only [d]; rw [show i.val + n - j.val = (i.val - j.val) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            rw [hd_eq, show i.val + (n - (i.val - j.val)) = j.val + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
          · have hd_eq : d = i.val + n - j.val := by dsimp only [d]; exact Nat.mod_eq_of_lt (by omega)
            rw [hd_eq, show i.val + (n - (i.val + n - j.val)) = j.val by omega, Nat.mod_eq_of_lt j.isLt]
        rwa [hm])
      let par : ZMod 2 := ∑ s ∈ Finset.range k0, ∑ b : Fin 4, α b * hMat n (moveC n i (n - s)) b
      if par = 0 then 1 else 2
    else 0
  have hmk_weight : ∀ S ∈ badS,
      q ^ (exitsS n S).card * eps ^ 9 ≤ ∏ i : Fin n, step3 q eps (bit (nextC n i)) (mkSt S i) (mkSt S (nextC n i)) := by
    intro S hS
    rcases (Finset.mem_filter.mp hS).2 with ⟨hne, hne0, hbad10⟩
    have hex_not : ∀ i : Fin n, i ∈ S → ∃ k < n, moveC n i (n - k) ∉ S := by
      intro i hi
      have hcomp : ∃ j : Fin n, j ∉ S := by
        by_contra hall; push_neg at hall; exact hne (Finset.eq_univ_iff_forall.mpr hall)
      rcases hcomp with ⟨j, hj⟩
      let d := (i.val + n - j.val) % n
      have hd_pos : 0 < d := by
        by_contra h0; have hd0 : d = 0 := by omega
        have hij : i = j := by
          ext; dsimp only [d] at hd0
          have := i.isLt; have := j.isLt
          by_cases hle : j.val ≤ i.val
          · have : (i.val + n - j.val) % n = i.val - j.val := by
              rw [show i.val + n - j.val = (i.val - j.val) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            omega
          · have : (i.val + n - j.val) % n = i.val + n - j.val := Nat.mod_eq_of_lt (by omega)
            omega
        exact hj (hij ▸ hi)
      refine ⟨d, Nat.mod_lt _ hn_pos, ?_⟩
      have hm : moveC n i (n - d) = j := by
        ext; simp only [moveC]
        have := i.isLt; have := j.isLt
        by_cases hle : j.val ≤ i.val
        · have hd_eq : d = i.val - j.val := by
            dsimp only [d]; rw [show i.val + n - j.val = (i.val - j.val) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hd_eq, show i.val + (n - (i.val - j.val)) = j.val + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
        · have hd_eq : d = i.val + n - j.val := by dsimp only [d]; exact Nat.mod_eq_of_lt (by omega)
          rw [hd_eq, show i.val + (n - (i.val + n - j.val)) = j.val by omega, Nat.mod_eq_of_lt j.isLt]
      rwa [hm]
    have hrun_pref : ∀ i : Fin n, (hi : i ∈ S) →
        let k0 := Nat.find (hex_not i hi)
        0 < k0 ∧ k0 < n ∧ moveC n i (n - k0) ∉ S ∧ (∀ s < k0, moveC n i (n - s) ∈ S) := by
      intro i hi k0
      have hspec := Nat.find_spec (hex_not i hi)
      have hk0_pos : 0 < k0 := by
        by_contra h0; have hk0 : k0 = 0 := by omega
        have hm : moveC n i (n - k0) ∉ S := hspec.2; rw [hk0, Nat.sub_zero, moveC_self] at hm; exact hm hi
      refine ⟨hk0_pos, hspec.1, hspec.2, fun s hs => ?_⟩
      by_contra hnot
      exact Nat.find_min (hex_not i hi) hs ⟨lt_trans hs hspec.1, hnot⟩
    have hstep_each : ∀ i : Fin n,
        step3 q eps (bit (nextC n i)) (mkSt S i) (mkSt S (nextC n i)) =
        if i ∉ S ∧ nextC n i ∈ S then q
        else if h : i ∈ S ∧ nextC n i ∉ S then
          if (∑ b : Fin 4, α b * runSig n S hne ⟨i, Finset.mem_filter.mpr h⟩ b) ≠ 0 then eps else 1
        else 1 := by
      intro i
      by_cases hi : i ∈ S
      · by_cases hni : nextC n i ∈ S
        · rw [if_neg (by tauto), dif_neg (by tauto)]
          have hpi := hrun_pref i hi
          have hpni := hrun_pref (nextC n i) hni
          dsimp only [mkSt]
          rw [dif_pos ⟨hne, hi⟩, dif_pos ⟨hne, hni⟩]
          set ki := Nat.find (hex_not i hi)
          set kni := Nat.find (hex_not (nextC n i) hni)
          have hshift : ∀ s < n, moveC n (nextC n i) (n - (s + 1)) = moveC n i (n - s) := by
            intro s hs
            rw [← moveC_one, moveC_add]
            have h1 : 1 + (n - (s + 1)) = n - s := by omega
            rw [h1]
          have hkni_eq : kni = ki + 1 := by
            apply le_antisymm
            · apply Nat.find_le
              have hlt : ki + 1 < n := by
                by_contra hge
                have hki_n : ki = n - 1 := by omega
                have hnm : moveC n i (n - ki) ∉ S := hpi.2.2.1
                rw [hki_n, show n - (n - 1) = 1 by omega, moveC_one] at hnm
                exact hnm hni
              refine ⟨hlt, ?_⟩
              rw [hshift ki hpi.2.1]; exact hpi.2.2.1
            · by_contra hlt; push_neg at hlt
              have hlt' : kni - 1 < ki := by omega
              have hmem := hpi.2.2.2 (kni - 1) hlt'
              have hnm := hpni.2.2.1
              have h1 := hshift (kni - 1) (by omega)
              rw [Nat.sub_add_cancel hpni.1] at h1
              rw [h1] at hnm
              exact hnm hmem
          have hpar_eq : (∑ s ∈ Finset.range kni, ∑ b : Fin 4, α b * hMat n (moveC n (nextC n i) (n - s)) b) =
              (∑ b : Fin 4, α b * hMat n (nextC n i) b) +
              (∑ s ∈ Finset.range ki, ∑ b : Fin 4, α b * hMat n (moveC n i (n - s)) b) := by
            rw [hkni_eq, Finset.sum_range_succ']
            rw [Nat.sub_zero, moveC_self, add_comm]
            congr 1
            refine Finset.sum_congr rfl fun s hs => ?_
            rw [hshift s (lt_trans (Finset.mem_range.mp hs) hpi.2.1)]
          rw [hpar_eq]
          generalize (∑ s ∈ Finset.range ki, ∑ b : Fin 4, α b * hMat n (moveC n i (n - s)) b) = p0
          generalize hbn : (∑ b : Fin 4, α b * hMat n (nextC n i) b) = b1
          have hbit_eq : bit (nextC n i) = decide (b1 ≠ 0) := by dsimp only [bit]; rw [hbn]
          rw [hbit_eq]
          convert step3_stay q eps b1 p0
        · rw [if_neg (by tauto), dif_pos ⟨hi, hni⟩]
          dsimp only [mkSt]
          rw [dif_pos ⟨hne, hi⟩, dif_neg (by tauto)]
          set ki := Nat.find (hex_not i hi)
          have hpi := hrun_pref i hi
          have hset_eq : (Finset.univ : Finset (Fin n)).filter
              (fun j => j ∈ S ∧ runExit n S hne j = i) =
              (Finset.range ki).image (fun s => moveC n i (n - s)) := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_range]
            constructor
            · rintro ⟨hjS, hjrun⟩
              let r := runDist n S hne j
              have hr_lt : r < n := runDist_lt n S hne j
              have hmove_ji : moveC n j r = i := hjrun
              have hmove_ij : moveC n i (n - r) = j := by
                rw [← hmove_ji, moveC_add]
                by_cases hr0 : r = 0
                · rw [hr0, Nat.sub_zero, zero_add, moveC_self]
                · rw [Nat.add_sub_cancel' (le_of_lt hr_lt), moveC_self]
              have hr_lt_ki : r < ki := by
                by_contra hge; push_neg at hge
                have hm := runDist_mem_prefix n S hne j hjS (r - ki) (by omega)
                have heq : moveC n j (r - ki) = moveC n i (n - ki) := by
                  rw [← hmove_ij, moveC_add]
                  have h1 : n - r + (r - ki) = n - ki := by omega
                  rw [h1]
                exact hpi.2.2.1 (heq ▸ hm)
              exact ⟨r, hr_lt_ki, hmove_ij⟩
            · rintro ⟨s, hs, rfl⟩
              refine ⟨hpi.2.2.2 s hs, ?_⟩
              have hmove_back : moveC n (moveC n i (n - s)) s = i := by
                rw [moveC_add]
                by_cases hs0 : s = 0
                · rw [hs0, Nat.sub_zero, add_zero, moveC_self]
                · rw [Nat.sub_add_cancel (le_of_lt (lt_trans hs hpi.2.1)), moveC_self]
              have hdist_eq : runDist n S hne (moveC n i (n - s)) = s := by
                apply le_antisymm
                · apply Nat.find_le
                  refine ⟨lt_trans hs hpi.2.1, ?_⟩
                  rw [show s + 1 = s + 1 from rfl, ← moveC_add, hmove_back, moveC_one]
                  exact hni
                · by_contra hlt; push_neg at hlt
                  have hspec := Nat.find_spec (exists_not_mem_moveC n S hne (moveC n i (n - s)))
                  have hm := hpi.2.2.2 (s - (runDist n S hne (moveC n i (n - s)) + 1)) (by omega)
                  have heq : moveC n (moveC n i (n - s)) (runDist n S hne (moveC n i (n - s)) + 1) =
                      moveC n i (n - (s - (runDist n S hne (moveC n i (n - s)) + 1))) := by
                    rw [moveC_add]; congr 1; omega
                  exact hspec.2 (heq ▸ hm)
              dsimp only [runExit]; rw [hdist_eq]; exact hmove_back
          have hsig_eq : (∑ s ∈ Finset.range ki, ∑ b : Fin 4, α b * hMat n (moveC n i (n - s)) b) =
              ∑ b : Fin 4, α b * runSig n S hne ⟨i, Finset.mem_filter.mpr ⟨hi, hni⟩⟩ b := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [← Finset.mul_sum]
            congr 1
            dsimp only [runSig, parityMap, embedRuns, LinearMap.coe_mk, AddHom.coe_mk]
            have hterm : ∀ j : Fin n, hMat n j b * (if h : j ∈ S then (Pi.single (⟨i, Finset.mem_filter.mpr ⟨hi, hni⟩⟩ : exitsS n S) (1 : ZMod 2) : exitsS n S → ZMod 2)
                ⟨runExit n S hne j, runExit_mem_exits n S hne h⟩ else 0) =
                if j ∈ S ∧ runExit n S hne j = i then hMat n j b else 0 := by
              intro j
              by_cases hj : j ∈ S
              · rw [dif_pos hj]
                by_cases hr : runExit n S hne j = i
                · have hsub : (⟨runExit n S hne j, runExit_mem_exits n S hne hj⟩ : exitsS n S) =
                      ⟨i, Finset.mem_filter.mpr ⟨hi, hni⟩⟩ := Subtype.ext hr
                  rw [hsub, Pi.single_eq_same, mul_one, if_pos ⟨hj, hr⟩]
                · have hsub : (⟨runExit n S hne j, runExit_mem_exits n S hne hj⟩ : exitsS n S) ≠
                      ⟨i, Finset.mem_filter.mpr ⟨hi, hni⟩⟩ := fun h => hr (congrArg Subtype.val h)
                  rw [Pi.single_eq_of_ne hsub, mul_zero, if_neg (by tauto)]
              · rw [dif_neg hj, mul_zero, if_neg (by tauto)]
            rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.sum_filter, hset_eq]
            rw [Finset.sum_image]
            intro s1 hs1 s2 hs2 heq
            have h1 := Finset.mem_range.mp hs1; have h2 := Finset.mem_range.mp hs2
            dsimp only at heq
            by_cases h10 : s1 = 0 <;> by_cases h20 : s2 = 0
            · rw [h10, h20]
            · rw [h10, Nat.sub_zero, moveC_self] at heq
              have heq' : moveC n i 0 = moveC n i (n - s2) := (moveC_zero n i).trans heq
              have := moveC_injective_lt n i (by omega) (by omega) heq'; omega
            · rw [h20, Nat.sub_zero, moveC_self] at heq
              have heq' : moveC n i (n - s1) = moveC n i 0 := heq.trans (moveC_zero n i).symm
              have := moveC_injective_lt n i (by omega) (by omega) heq'; omega
            · have := moveC_injective_lt n i (by omega) (by omega) heq; omega
          rw [hsig_eq]
          by_cases hz : (∑ b : Fin 4, α b * runSig n S hne ⟨i, Finset.mem_filter.mpr ⟨hi, hni⟩⟩ b) = 0
          · rw [if_pos hz, if_neg (not_not.mpr hz)]; simp [step3]
          · rw [if_neg hz, if_pos hz]; simp [step3]
      · by_cases hni : nextC n i ∈ S
        · rw [if_pos ⟨hi, hni⟩]
          dsimp only [mkSt]
          rw [dif_neg (by tauto), dif_pos ⟨hne, hni⟩]
          set kni := Nat.find (hex_not (nextC n i) hni)
          have hpni := hrun_pref (nextC n i) hni
          have hkni1 : kni = 1 := by
            apply le_antisymm
            · apply Nat.find_le
              refine ⟨by omega, ?_⟩
              have h1 : moveC n (nextC n i) (n - 1) = i := by
                rw [← moveC_one, moveC_add, show 1 + (n - 1) = n by omega, moveC_self]
              rwa [h1]
            · exact hpni.1
          rw [hkni1, Finset.sum_range_one, Nat.sub_zero, moveC_self]
          generalize hbn : (∑ b : Fin 4, α b * hMat n (nextC n i) b) = b1
          have hbit_eq : bit (nextC n i) = decide (b1 ≠ 0) := by dsimp only [bit]; rw [hbn]
          rw [hbit_eq]
          convert step3_enter q eps b1
        · rw [if_neg (by tauto), dif_neg (by tauto)]
          dsimp only [mkSt]
          rw [dif_neg (by tauto), dif_neg (by tauto)]
          simp [step3]
    rw [Finset.prod_congr rfl fun i _ => hstep_each i]
    let E_ent := Finset.univ.filter (fun i : Fin n => i ∉ S ∧ nextC n i ∈ S)
    let E_bad := Finset.univ.filter (fun i : Fin n => ∃ h : i ∈ S ∧ nextC n i ∉ S,
      (∑ b : Fin 4, α b * runSig n S hne ⟨i, Finset.mem_filter.mpr h⟩ b) ≠ 0)
    have hdisj : Disjoint E_ent E_bad := by
      rw [Finset.disjoint_left]; intro i h1 h2
      rcases (Finset.mem_filter.mp h2).2 with ⟨h, _⟩
      exact (Finset.mem_filter.mp h1).2.1 h.1
    have hprod_eq : (∏ i : Fin n, if i ∉ S ∧ nextC n i ∈ S then q
        else if h : i ∈ S ∧ nextC n i ∉ S then
          if (∑ b : Fin 4, α b * runSig n S hne ⟨i, Finset.mem_filter.mpr h⟩ b) ≠ 0 then eps else 1
        else 1) = q ^ E_ent.card * eps ^ E_bad.card := by
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : Fin n => i ∈ E_ent ∪ E_bad)]
      have hrest : ∏ i ∈ Finset.univ.filter (fun i : Fin n => i ∉ E_ent ∪ E_bad),
          (if i ∉ S ∧ nextC n i ∈ S then q
          else if h : i ∈ S ∧ nextC n i ∉ S then
            if (∑ b : Fin 4, α b * runSig n S hne ⟨i, Finset.mem_filter.mpr h⟩ b) ≠ 0 then eps else 1
          else 1) = 1 :=
        Finset.prod_eq_one fun i hi => by
          have hnot := (Finset.mem_filter.mp hi).2
          simp only [Finset.mem_union, E_ent, E_bad, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hnot
          rw [if_neg hnot.1]
          split_ifs with h h2
          · exact (hnot.2 ⟨h, h2⟩).elim
          · rfl
          · rfl
      rw [hrest, mul_one]
      have hfeq : Finset.univ.filter (fun i : Fin n => i ∈ E_ent ∪ E_bad) = E_ent ∪ E_bad := by ext i; simp
      rw [hfeq, Finset.prod_union hdisj]
      congr 1
      · rw [Finset.prod_congr rfl fun i hi => if_pos (Finset.mem_filter.mp hi).2, Finset.prod_const]
      · rw [Finset.prod_congr rfl fun i hi => by
          rcases (Finset.mem_filter.mp hi).2 with ⟨h, hnz⟩
          rw [if_neg (by tauto), dif_pos h, if_pos hnz], Finset.prod_const]
    rw [hprod_eq]
    have hEent_eq : E_ent.card = (exitsS n S).card := card_entries_eq_exits n S
    have hEbad_eq : E_bad.card = badRuns n S hne α := by
      dsimp only [E_bad, badRuns]
      refine Finset.card_bij (fun i hi => ⟨i, Finset.mem_filter.mpr (Classical.choose (Finset.mem_filter.mp hi).2)⟩)
        (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, Classical.choose_spec (Finset.mem_filter.mp hi).2⟩)
        (fun i1 _ i2 _ heq => congrArg Subtype.val heq)
        (fun a ha => ⟨a.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mp a.2, (Finset.mem_filter.mp ha).2⟩, Subtype.ext rfl⟩)
    rw [hEent_eq, hEbad_eq]
    have heps_le1 : eps ≤ 1 := by dsimp only [eps]; rw [div_le_one hL_pos]; linarith
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (le_of_lt heps_pos) heps_le1 (by omega)) (by positivity)
  have hmk_inj : Set.InjOn mkSt (badS : Set (Finset (Fin n))) := by
    intro S1 hS1 S2 hS2 heq
    rcases (Finset.mem_filter.mp (Finset.mem_coe.mp hS1)).2 with ⟨hne1, _, _⟩
    rcases (Finset.mem_filter.mp (Finset.mem_coe.mp hS2)).2 with ⟨hne2, _, _⟩
    ext i
    have hi := congrFun heq i
    have hnz : ∀ (S : Finset (Fin n)) (hne : S ≠ Finset.univ), mkSt S i ≠ 0 ↔ i ∈ S := fun S hne => by
      dsimp only [mkSt]
      by_cases hm : i ∈ S
      · rw [dif_pos ⟨hne, hm⟩]; split_ifs <;> simp [hm]
      · rw [dif_neg (by tauto)]; simp [hm]
    rw [← hnz S1 hne1, ← hnz S2 hne2, hi]
  have hsum_eps : (∑ S ∈ badS, q ^ (exitsS n S).card) * eps ^ 9 ≤
      L ^ 2 * (1 - 1 / (2 * L)) ^ t * L ^ n := by
    rw [Finset.sum_mul]
    calc ∑ S ∈ badS, q ^ (exitsS n S).card * eps ^ 9
        ≤ ∑ S ∈ badS, ∏ i : Fin n, step3 q eps (bit (nextC n i)) (mkSt S i) (mkSt S (nextC n i)) :=
            Finset.sum_le_sum hmk_weight
      _ = ∑ st ∈ badS.image mkSt, ∏ i : Fin n, step3 q eps (bit (nextC n i)) (st i) (st (nextC n i)) :=
            (Finset.sum_image (f := fun st : Fin n → Fin 3 => ∏ i : Fin n, step3 q eps (bit (nextC n i)) (st i) (st (nextC n i))) hmk_inj).symm
      _ ≤ ∑ st : Fin n → Fin 3, ∏ i : Fin n, step3 q eps (bit (nextC n i)) (st i) (st (nextC n i)) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun _ _ _ => Finset.prod_nonneg fun _ _ => step3_nonneg q eps (le_of_lt hq_pos) (le_of_lt heps_pos) _ _ _)
      _ ≤ L ^ 2 * (1 - 1 / (2 * L)) ^ t * L ^ n := htr_bound
  have hinv : L ^ 9 * eps ^ 9 = 1 := by
    dsimp only [eps]; rw [← mul_pow, mul_one_div_cancel (ne_of_gt hL_pos), one_pow]
  calc ∑ S ∈ badS, q ^ (exitsS n S).card
      = L ^ 9 * ((∑ S ∈ badS, q ^ (exitsS n S).card) * eps ^ 9) := by
          calc _ = (∑ S ∈ badS, q ^ (exitsS n S).card) * (L ^ 9 * eps ^ 9) := by rw [hinv, mul_one]
            _ = _ := by ring
    _ ≤ L ^ 9 * (L ^ 2 * (1 - 1 / (2 * L)) ^ t * L ^ n) := mul_le_mul_of_nonneg_left hsum_eps (by positivity)
    _ = L ^ 11 * (1 - 1 / (2 * L)) ^ t * L ^ n := by ring



private def gapCount (n r : ℕ) (S : Finset (Fin n)) : ℕ :=
  ((exitsS n S).filter (fun a => gapS n S a = 2 * r + 2)).card

private def compFin (p N : ℕ) : Finset (Fin p → ℕ) :=
  (Fintype.piFinset (fun _ : Fin p => Finset.range (N + 1))).filter (fun ℓ => ∑ u : Fin p, ℓ u = N)

private lemma sum_range_choose_add (a N : ℕ) :
    ∑ m ∈ Finset.range (N + 1), Nat.choose (m + a) a = Nat.choose (N + a + 1) (a + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : N + 1 + a + 1 = (N + a + 1) + 1 := by omega
    have h2 : N + 1 + a = N + a + 1 := by omega
    rw [h1, h2, Nat.choose_succ_succ (N + a + 1) a, add_comm]

private lemma card_compFin (p N : ℕ) (hp : 1 ≤ p) :
    (compFin p N).card = Nat.choose (N + p - 1) (p - 1) := by
  induction p generalizing N with
  | zero => omega
  | succ p ih =>
    by_cases hp0 : p = 0
    · subst hp0
      have hsing : compFin 1 N = {fun _ => N} := by
        ext ℓ
        simp only [compFin, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range, Finset.mem_singleton]
        constructor
        · rintro ⟨_, hs⟩; funext u; fin_cases u; simpa using hs
        · rintro rfl; exact ⟨fun _ => by dsimp only; omega, by simp⟩
      rw [hsing, Finset.card_singleton]; simp
    · have hp1 : 1 ≤ p := by omega
      have hfib := Finset.card_eq_sum_card_fiberwise
        (s := compFin (p + 1) N) (t := Finset.range (N + 1)) (f := fun ℓ => ℓ (Fin.last p))
        (fun ℓ hℓ => (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hℓ).1) (Fin.last p))
      rw [hfib]
      have hfiber_card : ∀ k ∈ Finset.range (N + 1),
          ((compFin (p + 1) N).filter (fun ℓ => ℓ (Fin.last p) = k)).card = (compFin p (N - k)).card := by
        intro k hk
        have hk_le : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        refine Finset.card_bij (fun ℓ _ => fun u : Fin p => ℓ u.castSucc) ?_ ?_ ?_
        · intro ℓ hℓ
          have hℓc := (Finset.mem_filter.mp hℓ).1
          have hlast := (Finset.mem_filter.mp hℓ).2
          have hsum := (Finset.mem_filter.mp hℓc).2
          rw [Fin.sum_univ_castSucc, hlast] at hsum
          refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun u => Finset.mem_range.mpr ?_, by dsimp only; omega⟩
          have hle_u : ℓ u.castSucc ≤ ∑ v : Fin p, ℓ v.castSucc :=
            Finset.single_le_sum (f := fun v : Fin p => ℓ v.castSucc) (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)
          omega
        · intro ℓ1 hℓ1 ℓ2 hℓ2 heq
          have h1 := (Finset.mem_filter.mp hℓ1).2
          have h2 := (Finset.mem_filter.mp hℓ2).2
          funext u
          refine Fin.lastCases ?_ ?_ u
          · rw [h1, h2]
          · intro v; exact congrFun heq v
        · intro ℓ' hℓ'
          have hsum' := (Finset.mem_filter.mp hℓ').2
          let ℓ : Fin (p + 1) → ℕ := Fin.snoc ℓ' k
          refine ⟨ℓ, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun u => ?_, ?_⟩, ?_⟩, ?_⟩
          · refine Fin.lastCases ?_ ?_ u
            · simpa [ℓ] using hk
            · intro v
              have hv := Finset.mem_range.mp (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hℓ').1 v)
              simpa [ℓ] using (Finset.mem_range.mpr (show ℓ' v < N + 1 by omega))
          · rw [Fin.sum_univ_castSucc]; simp only [ℓ, Fin.snoc_castSucc, Fin.snoc_last]; omega
          · simp [ℓ]
          · funext v; simp [ℓ]
      rw [Finset.sum_congr rfl hfiber_card]
      simp_rw [ih _ hp1]
      have hrev : ∑ k ∈ Finset.range (N + 1), Nat.choose (N - k + p - 1) (p - 1) =
          ∑ m ∈ Finset.range (N + 1), Nat.choose (m + (p - 1)) (p - 1) := by
        refine Finset.sum_bij (fun k _ => N - k)
          (fun k hk => Finset.mem_range.mpr (by have := Finset.mem_range.mp hk; omega))
          (fun k1 hk1 k2 hk2 h => by have := Finset.mem_range.mp hk1; have := Finset.mem_range.mp hk2; omega)
          (fun m hm => ⟨N - m, Finset.mem_range.mpr (by have := Finset.mem_range.mp hm; omega),
            by have := Finset.mem_range.mp hm; omega⟩)
          (fun k _ => by congr 1; omega)
      rw [hrev, sum_range_choose_add]
      congr 1 <;> omega

private def offF (g p : ℕ) (ℓ : Fin p → ℕ) (u : Fin p) : ℕ :=
  ∑ v ∈ (Finset.univ : Finset (Fin p)).filter (fun v => v.val < u.val), (g + 1 + ℓ v)

private def mkAF (n g p : ℕ) (a0 : Fin n) (ℓ : Fin p → ℕ) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin p)).image (fun u => moveC n a0 (offF g p ℓ u))

private lemma offF_zero (g p : ℕ) (hp : 1 ≤ p) (ℓ : Fin p → ℕ) :
    offF g p ℓ ⟨0, hp⟩ = 0 := by
  dsimp only [offF]
  have hemp : (Finset.univ : Finset (Fin p)).filter (fun v => v.val < 0) = ∅ := by
    ext v; simp
  rw [hemp, Finset.sum_empty]

private lemma offF_succ (g p : ℕ) (ℓ : Fin p → ℕ) (u : Fin p) (hu : u.val + 1 < p) :
    offF g p ℓ ⟨u.val + 1, hu⟩ = offF g p ℓ u + (g + 1 + ℓ u) := by
  dsimp only [offF]
  have hins : (Finset.univ : Finset (Fin p)).filter (fun v => v.val < u.val + 1) =
      insert u ((Finset.univ : Finset (Fin p)).filter (fun v => v.val < u.val)) := by
    ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      by_cases heq : v.val = u.val
      · left; exact Fin.ext heq
      · right; omega
    · rintro (rfl | h)
      · omega
      · omega
  have hnm : u ∉ (Finset.univ : Finset (Fin p)).filter (fun v => v.val < u.val) := by simp
  rw [hins, Finset.sum_insert hnm, add_comm]

private lemma offF_last (g p : ℕ) (hp : 1 ≤ p) (ℓ : Fin p → ℕ) :
    offF g p ℓ ⟨p - 1, by omega⟩ + (g + 1 + ℓ ⟨p - 1, by omega⟩) = ∑ v : Fin p, (g + 1 + ℓ v) := by
  dsimp only [offF]
  have hins : insert (⟨p - 1, by omega⟩ : Fin p)
      ((Finset.univ : Finset (Fin p)).filter (fun v => v.val < p - 1)) = Finset.univ := by
    ext v; simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    by_cases h : v.val = p - 1
    · left; exact Fin.ext h
    · right; have := v.isLt; omega
  have hnm : (⟨p - 1, by omega⟩ : Fin p) ∉ (Finset.univ : Finset (Fin p)).filter (fun v => v.val < p - 1) := by simp
  rw [add_comm, ← Finset.sum_insert (f := fun v => g + 1 + ℓ v) hnm, hins]

private lemma offF_step_le_of_lt (g p : ℕ) (ℓ : Fin p → ℕ) {u w : Fin p} (huw : u.val < w.val) :
    offF g p ℓ u + (g + 1 + ℓ u) ≤ offF g p ℓ w := by
  dsimp only [offF]
  have hnm : u ∉ (Finset.univ : Finset (Fin p)).filter (fun v => v.val < u.val) := by simp
  rw [add_comm, ← Finset.sum_insert (f := fun v => g + 1 + ℓ v) hnm]
  refine Finset.sum_le_sum_of_subset ?_
  intro v hv
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  rcases hv with rfl | hlt <;> omega

private lemma offF_step_le_total (g p : ℕ) (ℓ : Fin p → ℕ) (u : Fin p) :
    offF g p ℓ u + (g + 1 + ℓ u) ≤ ∑ v : Fin p, (g + 1 + ℓ v) := by
  dsimp only [offF]
  have hnm : u ∉ (Finset.univ : Finset (Fin p)).filter (fun v => v.val < u.val) := by simp
  rw [add_comm, ← Finset.sum_insert (f := fun v => g + 1 + ℓ v) hnm]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

set_option maxHeartbeats 800000 in
private lemma sum_choose_gapCount_exact (n r p : ℕ) (hr : 1 ≤ r) (hp : 1 ≤ p)
    (hn : p * (2 * r + 3) < n) (q : ℝ) (hq : 0 < q) :
    (p : ℝ) * ∑ S : Finset (Fin n),
        (Nat.choose (gapCount n r S) p : ℝ) * q ^ (exitsS n S).card =
      (n : ℝ) * q ^ p *
        ∑ ℓ ∈ compFin p (n - p * (2 * r + 3)), ∏ u : Fin p, mat2Pow q (ℓ u) true true := by
  classical
  let g := 2 * r + 2
  have hg1 : 1 ≤ g := by dsimp only [g]; omega
  have hgn : g + 1 < n := by
    have : 1 * (2 * r + 3) ≤ p * (2 * r + 3) := Nat.mul_le_mul_right _ hp
    dsimp only [g]; omega
  let N := n - p * (g + 1)
  have hN_eq : p * (g + 1) + N = n := by
    dsimp only [N, g]
    have hmul : p * (2 * r + 2 + 1) = p * (2 * r + 3) := by congr 1
    omega
  have hn_pos : 0 < n := by omega
  let validA := ((Finset.univ : Finset (Fin n)).powersetCard p).filter
    (fun A => ∀ a ∈ A, ∀ v : ℕ, 1 ≤ v → v ≤ g → moveC n a v ∉ A)
  have hsum_A : ∑ S : Finset (Fin n), (Nat.choose (gapCount n r S) p : ℝ) * q ^ (exitsS n S).card =
      ∑ A ∈ validA, ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
        (fun S => ∀ a ∈ A, a ∈ exitsS n S ∧ gapS n S a = g), q ^ (exitsS n S).card := by
    have hstep1 : ∀ S : Finset (Fin n),
        (Nat.choose (gapCount n r S) p : ℝ) * q ^ (exitsS n S).card =
        ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard p,
          if (∀ a ∈ A, a ∈ exitsS n S ∧ gapS n S a = g) then q ^ (exitsS n S).card else 0 := by
      intro S
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      congr 1
      have hfeq : ((Finset.univ : Finset (Fin n)).powersetCard p).filter
          (fun A => ∀ a ∈ A, a ∈ exitsS n S ∧ gapS n S a = g) =
          ((exitsS n S).filter (fun a => gapS n S a = g)).powersetCard p := by
        ext A
        simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
        constructor
        · rintro ⟨hc, hall⟩
          exact ⟨fun a ha => Finset.mem_filter.mpr (hall a ha), hc⟩
        · rintro ⟨hsub, hc⟩
          exact ⟨hc, fun a ha => Finset.mem_filter.mp (hsub ha)⟩
      rw [hfeq, Finset.card_powersetCard]; rfl
    rw [Finset.sum_congr rfl fun S _ => hstep1 S, Finset.sum_comm]
    have hzero_bad : ∀ A ∈ (Finset.univ : Finset (Fin n)).powersetCard p, A ∉ validA →
        (∑ S : Finset (Fin n),
          if (∀ a ∈ A, a ∈ exitsS n S ∧ gapS n S a = g) then q ^ (exitsS n S).card else 0) = 0 := by
      intro A hA hnot
      refine Finset.sum_eq_zero fun S _ => ?_
      rw [if_neg]
      intro hall
      apply hnot
      refine Finset.mem_filter.mpr ⟨hA, fun a ha v hv1 hvg hm => ?_⟩
      have haS := (Finset.mem_filter.mp (hall a ha).1).1
      have hspec := (gapS_iff n S haS g).mp (hall a ha).2
      have hnm := hspec.2.1 (v - 1) (by omega)
      rw [Nat.sub_add_cancel hv1] at hnm
      exact hnm (Finset.mem_filter.mp (hall _ hm).1).1
    rw [← Finset.sum_filter_add_sum_filter_not ((Finset.univ : Finset (Fin n)).powersetCard p)
      (fun A => A ∈ validA)]
    have hbad0 : ∑ A ∈ ((Finset.univ : Finset (Fin n)).powersetCard p).filter (fun A => A ∉ validA),
        ∑ S : Finset (Fin n),
          (if (∀ a ∈ A, a ∈ exitsS n S ∧ gapS n S a = g) then q ^ (exitsS n S).card else 0) = 0 :=
      Finset.sum_eq_zero fun A hA => hzero_bad A (Finset.mem_filter.mp hA).1 (Finset.mem_filter.mp hA).2
    rw [hbad0, add_zero]
    have hfeq : ((Finset.univ : Finset (Fin n)).powersetCard p).filter (fun A => A ∈ validA) = validA := by
      ext A; simp only [Finset.mem_filter, validA]; tauto
    rw [hfeq]
    refine Finset.sum_congr rfl fun A _ => by rw [Finset.sum_filter]
  have hinner : ∀ (a0 : Fin n) (ℓ : Fin p → ℕ), ℓ ∈ compFin p N →
      (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
          (fun S => ∀ a ∈ mkAF n g p a0 ℓ, a ∈ exitsS n S ∧ gapS n S a = g),
        q ^ (exitsS n S).card) =
      q ^ p * ∏ u : Fin p, mat2Pow q (ℓ u) true true := by
    intro a0 ℓ hℓ
    have hsum_ℓ : ∑ v : Fin p, ℓ v = N := (Finset.mem_filter.mp hℓ).2
    have hsum_tot : ∑ v : Fin p, (g + 1 + ℓ v) = n := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hsum_ℓ, hN_eq]
    have hoff_lt : ∀ u : Fin p, offF g p ℓ u < n := fun u => by
      have := offF_step_le_total g p ℓ u; omega
    have hseg : ∀ k < n, ∃! u : Fin p, offF g p ℓ u ≤ k ∧ k < offF g p ℓ u + (g + 1 + ℓ u) := by
      intro k hk
      let cand := (Finset.univ : Finset (Fin p)).filter (fun u => offF g p ℓ u ≤ k)
      have hcand_ne : cand.Nonempty := ⟨⟨0, hp⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [offF_zero]; omega⟩⟩
      let u0 := cand.max' hcand_ne
      have hu0_le : offF g p ℓ u0 ≤ k := (Finset.mem_filter.mp (Finset.max'_mem cand hcand_ne)).2
      have hu0_lt : k < offF g p ℓ u0 + (g + 1 + ℓ u0) := by
        by_cases hlast : u0.val + 1 < p
        · rw [← offF_succ g p ℓ u0 hlast]
          by_contra hge; push_neg at hge
          have hmem : (⟨u0.val + 1, hlast⟩ : Fin p) ∈ cand :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hge⟩
          have hle := Finset.le_max' cand _ hmem
          have : u0.val + 1 ≤ u0.val := hle
          omega
        · have hu0_eq : u0 = ⟨p - 1, by omega⟩ := Fin.ext (by dsimp only; have := u0.isLt; omega)
          rw [hu0_eq, offF_last g p hp ℓ, hsum_tot]
          exact hk
      refine ⟨u0, ⟨hu0_le, hu0_lt⟩, ?_⟩
      intro u1 ⟨h1l, h1u⟩
      by_contra hne
      have hne_v : u1.val ≠ u0.val := fun h => hne (Fin.ext h)
      rcases lt_or_gt_of_ne hne_v with hlt | hgt
      · have := offF_step_le_of_lt g p ℓ hlt; omega
      · have := offF_step_le_of_lt g p ℓ hgt; omega
    have hnext_off : ∀ u : Fin p,
        moveC n a0 (offF g p ℓ u + g + 1 + ℓ u) ∈ mkAF n g p a0 ℓ := by
      intro u
      by_cases hlast : u.val + 1 < p
      · have heq : offF g p ℓ u + g + 1 + ℓ u = offF g p ℓ ⟨u.val + 1, hlast⟩ := by
          rw [offF_succ g p ℓ u hlast]; omega
        rw [heq]
        exact Finset.mem_image.mpr ⟨⟨u.val + 1, hlast⟩, Finset.mem_univ _, rfl⟩
      · have hu_eq : u = ⟨p - 1, by omega⟩ := Fin.ext (by dsimp only; have := u.isLt; omega)
        have heq : offF g p ℓ u + g + 1 + ℓ u = n := by
          have := offF_last g p hp ℓ
          rw [hu_eq] at ⊢; omega
        have hmv : moveC n a0 (offF g p ℓ u + g + 1 + ℓ u) = moveC n a0 (offF g p ℓ ⟨0, hp⟩) := by
          rw [heq, moveC_self, offF_zero g p hp ℓ, moveC_zero]
        rw [hmv]
        exact Finset.mem_image.mpr ⟨⟨0, hp⟩, Finset.mem_univ _, rfl⟩
    let segDom (u : Fin p) : Finset (Fin (ℓ u + 1) → Bool) :=
      (Finset.univ : Finset (Fin (ℓ u + 1) → Bool)).filter (fun b => b 0 = true ∧ b ⟨ℓ u, by omega⟩ = true)
    have hrhs_eq : q ^ p * ∏ u : Fin p, mat2Pow q (ℓ u) true true =
        ∑ φ ∈ Fintype.piFinset segDom,
          q ^ p * ∏ u : Fin p, ∏ j : Fin (ℓ u), step2 q (φ u ⟨j.val, by omega⟩) (φ u ⟨j.val + 1, by omega⟩) := by
      rw [← Finset.mul_sum]
      congr 1
      have hfac := Finset.prod_univ_sum (t := segDom)
        (f := fun (u : Fin p) (b : Fin (ℓ u + 1) → Bool) =>
          ∏ j : Fin (ℓ u), step2 q (b ⟨j.val, by omega⟩) (b ⟨j.val + 1, by omega⟩))
      rw [← hfac]
      refine Finset.prod_congr rfl fun u _ => (sum_path_step2 q hq (ℓ u) true true).symm
    rw [hrhs_eq]
    let toPhi (S : Finset (Fin n)) : ∀ u : Fin p, Fin (ℓ u + 1) → Bool :=
      fun u j => decide (moveC n a0 (offF g p ℓ u + g + 1 + j.val) ∈ S)
    refine Finset.sum_bij (fun S _ => toPhi S) ?_ ?_ ?_ ?_
    · intro S hS
      have hall := (Finset.mem_filter.mp hS).2
      rw [Fintype.mem_piFinset]
      intro u
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · dsimp only [toPhi]
        have huA : moveC n a0 (offF g p ℓ u) ∈ mkAF n g p a0 ℓ :=
          Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
        have hgap := (hall _ huA).2
        have haS := (Finset.mem_filter.mp (hall _ huA).1).1
        have hspec := (gapS_iff n S haS g).mp hgap
        have hm := hspec.2.2
        rw [moveC_add] at hm
        have heq : offF g p ℓ u + g + 1 + 0 = offF g p ℓ u + (g + 1) := by omega
        simp [heq, hm]
      · dsimp only [toPhi]
        have hm := hnext_off u
        have hmemS := (Finset.mem_filter.mp (hall _ hm).1).1
        simp [hmemS]
    · intro S1 hS1 S2 hS2 heq
      have hall1 := (Finset.mem_filter.mp hS1).2
      have hall2 := (Finset.mem_filter.mp hS2).2
      ext x
      let k := (x.val + n - a0.val) % n
      have hk_lt : k < n := Nat.mod_lt _ hn_pos
      have hx_eq : moveC n a0 k = x := moveC_mod_sub n a0 x
      rw [← hx_eq]
      rcases (hseg k hk_lt).exists with ⟨u, hle_u, hlt_u⟩
      have huA : moveC n a0 (offF g p ℓ u) ∈ mkAF n g p a0 ℓ :=
        Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
      by_cases h0 : k = offF g p ℓ u
      · rw [h0]
        have h1 := (Finset.mem_filter.mp (hall1 _ huA).1).1
        have h2 := (Finset.mem_filter.mp (hall2 _ huA).1).1
        simp [h1, h2]
      · by_cases hg_le : k ≤ offF g p ℓ u + g
        · have h1 := ((gapS_iff n S1 (Finset.mem_filter.mp (hall1 _ huA).1).1 g).mp (hall1 _ huA).2).2.1
            (k - offF g p ℓ u - 1) (by omega)
          have h2 := ((gapS_iff n S2 (Finset.mem_filter.mp (hall2 _ huA).1).1 g).mp (hall2 _ huA).2).2.1
            (k - offF g p ℓ u - 1) (by omega)
          rw [moveC_add, show offF g p ℓ u + (k - offF g p ℓ u - 1 + 1) = k by omega] at h1 h2
          simp [h1, h2]
        · let j : Fin (ℓ u + 1) := ⟨k - (offF g p ℓ u + g + 1), by omega⟩
          have hphi := congrFun (congrFun heq u) j
          dsimp only [toPhi, j] at hphi
          rw [show offF g p ℓ u + g + 1 + (k - (offF g p ℓ u + g + 1)) = k by omega] at hphi
          simpa using hphi
    · intro φ hφ
      have hφ_mem := Fintype.mem_piFinset.mp hφ
      let bOfK : ∀ k < n, Bool := fun k hk =>
        let u := Classical.choose (hseg k hk).exists
        if k = offF g p ℓ u then true
        else if k ≤ offF g p ℓ u + g then false
        else φ u ⟨k - (offF g p ℓ u + g + 1), by
          have hu := Classical.choose_spec (hseg k hk).exists
          change offF g p ℓ u ≤ k ∧ k < offF g p ℓ u + (g + 1 + ℓ u) at hu
          omega⟩
      have hbOfK_eq : ∀ (u : Fin p) (r : ℕ) (hr_lt : r < g + 1 + ℓ u),
          bOfK (offF g p ℓ u + r) (by have := offF_step_le_total g p ℓ u; omega) =
          if r = 0 then true else if r ≤ g then false else φ u ⟨r - (g + 1), by omega⟩ := by
        intro u r hr_lt
        have hk_lt : offF g p ℓ u + r < n := by have := offF_step_le_total g p ℓ u; omega
        have hu_uniq : Classical.choose (hseg (offF g p ℓ u + r) hk_lt).exists = u :=
          (hseg (offF g p ℓ u + r) hk_lt).unique (Classical.choose_spec (hseg _ hk_lt).exists) ⟨by omega, by omega⟩
        dsimp only [bOfK]
        have haux : ∀ (u' : Fin p)
            (hp' : offF g p ℓ u' ≤ offF g p ℓ u + r ∧ offF g p ℓ u + r < offF g p ℓ u' + (g + 1 + ℓ u')),
            u' = u →
            (if offF g p ℓ u + r = offF g p ℓ u' then true
             else if offF g p ℓ u + r ≤ offF g p ℓ u' + g then false
             else φ u' ⟨offF g p ℓ u + r - (offF g p ℓ u' + g + 1), by omega⟩) =
            if r = 0 then true else if r ≤ g then false else φ u ⟨r - (g + 1), by omega⟩ := by
          rintro u' hp' rfl
          by_cases hr0 : r = 0
          · rw [if_pos (by omega), if_pos hr0]
          · by_cases hrg : r ≤ g
            · rw [if_neg (by omega), if_pos (by omega), if_neg hr0, if_pos hrg]
            · rw [if_neg (by omega), if_neg (by omega), if_neg hr0, if_neg hrg]
              congr 1; exact Fin.ext (by dsimp only; omega)
        exact haux _ (Classical.choose_spec (hseg (offF g p ℓ u + r) hk_lt).exists) hu_uniq
      let S : Finset (Fin n) := Finset.univ.filter fun x =>
        bOfK ((x.val + n - a0.val) % n) (Nat.mod_lt _ hn_pos) = true
      have hmem_moveC : ∀ k (hk : k < n), moveC n a0 k ∈ S ↔ bOfK k hk = true := by
        intro k hk
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        have hback : ((moveC n a0 k).val + n - a0.val) % n = k := mod_sub_moveC n a0 hk
        simp_rw [hback]
      have hmem_seg : ∀ (u : Fin p) (j : Fin (ℓ u + 1)),
          moveC n a0 (offF g p ℓ u + g + 1 + j.val) ∈ S ↔ φ u j = true := by
        intro u j
        by_cases hj : j.val < ℓ u
        · have hk_lt : offF g p ℓ u + (g + 1 + j.val) < n := by
            have := offF_step_le_total g p ℓ u; omega
          rw [show offF g p ℓ u + g + 1 + j.val = offF g p ℓ u + (g + 1 + j.val) by omega,
            hmem_moveC _ hk_lt, hbOfK_eq u (g + 1 + j.val) (by omega)]
          rw [if_neg (by omega), if_neg (by omega)]
          have hj_eq : (⟨g + 1 + j.val - (g + 1), by omega⟩ : Fin (ℓ u + 1)) = j := Fin.ext (by dsimp only; omega)
          rw [hj_eq]
        · have hj_eq : j = ⟨ℓ u, by omega⟩ := Fin.ext (by dsimp only; have := j.isLt; omega)
          rw [hj_eq, (Finset.mem_filter.mp (hφ_mem u)).2.2]
          simp only [iff_true]
          by_cases hlast : u.val + 1 < p
          · have heq : offF g p ℓ u + g + 1 + ℓ u = offF g p ℓ ⟨u.val + 1, hlast⟩ + 0 := by
              rw [offF_succ g p ℓ u hlast]; omega
            rw [heq, hmem_moveC _ (by have := hoff_lt ⟨u.val + 1, hlast⟩; omega), hbOfK_eq _ 0 (by omega)]
            simp
          · have hu_eq : u = ⟨p - 1, by omega⟩ := Fin.ext (by dsimp only; have := u.isLt; omega)
            have heq : offF g p ℓ u + g + 1 + ℓ u = n := by
              have := offF_last g p hp ℓ; rw [hu_eq] at ⊢; omega
            rw [heq, moveC_self, ← moveC_zero n a0, ← offF_zero g p hp ℓ,
              show offF g p ℓ ⟨0, hp⟩ = offF g p ℓ ⟨0, hp⟩ + 0 by omega,
              hmem_moveC _ (by rw [offF_zero]; omega), hbOfK_eq _ 0 (by omega)]
            simp
      have hS_ok : ∀ a ∈ mkAF n g p a0 ℓ, a ∈ exitsS n S ∧ gapS n S a = g := by
        intro a ha
        rcases Finset.mem_image.mp ha with ⟨u, _, rfl⟩
        have haS : moveC n a0 (offF g p ℓ u) ∈ S := by
          rw [show offF g p ℓ u = offF g p ℓ u + 0 by omega,
            hmem_moveC _ (by have := hoff_lt u; omega), hbOfK_eq u 0 (by omega)]
          simp
        have hnot_gap : ∀ v < g, moveC n (moveC n a0 (offF g p ℓ u)) (v + 1) ∉ S := by
          intro v hv
          rw [moveC_add, hmem_moveC _ (by have := offF_step_le_total g p ℓ u; omega),
            hbOfK_eq u (v + 1) (by omega), if_neg (by omega), if_pos (by omega)]
          simp
        have hend : moveC n (moveC n a0 (offF g p ℓ u)) (g + 1) ∈ S := by
          rw [moveC_add, show offF g p ℓ u + (g + 1) = offF g p ℓ u + g + 1 + (0 : Fin (ℓ u + 1)).val by simp only [Fin.val_zero, add_zero]; omega,
            hmem_seg u 0]
          exact (Finset.mem_filter.mp (hφ_mem u)).2.1
        have hex : moveC n a0 (offF g p ℓ u) ∈ exitsS n S := by
          refine Finset.mem_filter.mpr ⟨haS, ?_⟩
          rw [← moveC_one]; exact hnot_gap 0 (by omega)
        have hgap : gapS n S (moveC n a0 (offF g p ℓ u)) = g :=
          (gapS_iff n S haS g).mpr ⟨by omega, hnot_gap, hend⟩
        exact ⟨hex, hgap⟩
      refine ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS_ok⟩, ?_⟩
      funext u j
      dsimp only [toPhi]
      cases hval : φ u j
      · simp [hmem_seg u j, hval]
      · simp [hmem_seg u j, hval]
    · intro S hS
      have hall := (Finset.mem_filter.mp hS).2
      rw [← prod_step2_eq_pow n q S]
      let eShift : Fin n ≃ Fin n :=
        { toFun := fun k => moveC n a0 k.val
          invFun := fun x => ⟨(x.val + n - a0.val) % n, Nat.mod_lt _ hn_pos⟩
          left_inv := fun k => Fin.ext (mod_sub_moveC n a0 k.isLt)
          right_inv := fun x => moveC_mod_sub n a0 x }
      rw [← Fintype.prod_equiv eShift
        (fun k => step2 q (decide (moveC n a0 k.val ∈ S)) (decide (nextC n (moveC n a0 k.val) ∈ S)))
        (fun i => step2 q (decide (i ∈ S)) (decide (nextC n i ∈ S))) (fun _ => rfl)]
      let segSet (u : Fin p) : Finset (Fin n) :=
        Finset.univ.filter fun k => offF g p ℓ u ≤ k.val ∧ k.val < offF g p ℓ u + (g + 1 + ℓ u)
      have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin p)) segSet := by
        intro u1 _ u2 _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro k hk1 hk2
        exact hne ((hseg k.val k.isLt).unique (Finset.mem_filter.mp hk1).2 (Finset.mem_filter.mp hk2).2)
      have hcov : (Finset.univ : Finset (Fin p)).biUnion segSet = Finset.univ := by
        ext k; simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, segSet, Finset.mem_filter, iff_true]
        exact (hseg k.val k.isLt).exists
      rw [← hcov, Finset.prod_biUnion hdisj]
      have heach_u : ∀ u : Fin p,
          (∏ k ∈ segSet u, step2 q (decide (moveC n a0 k.val ∈ S)) (decide (nextC n (moveC n a0 k.val) ∈ S))) =
          q * ∏ j : Fin (ℓ u), step2 q (toPhi S u ⟨j.val, by omega⟩) (toPhi S u ⟨j.val + 1, by omega⟩) := by
        intro u
        rw [← Finset.prod_filter_mul_prod_filter_not (segSet u) (fun k => k.val < offF g p ℓ u + g + 1)]
        have huA : moveC n a0 (offF g p ℓ u) ∈ mkAF n g p a0 ℓ :=
          Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
        have hspec := (gapS_iff n S (Finset.mem_filter.mp (hall _ huA).1).1 g).mp (hall _ huA).2
        congr 1
        · let lastK : Fin n := ⟨offF g p ℓ u + g, by have := offF_step_le_total g p ℓ u; omega⟩
          have hlast_mem : lastK ∈ (segSet u).filter (fun k => k.val < offF g p ℓ u + g + 1) := by
            simp only [Finset.mem_filter, segSet, Finset.mem_univ, true_and, lastK]; omega
          rw [← Finset.mul_prod_erase _ _ hlast_mem]
          have hlast_val : step2 q (decide (moveC n a0 lastK.val ∈ S)) (decide (nextC n (moveC n a0 lastK.val) ∈ S)) = q := by
            have h1 : moveC n a0 lastK.val ∉ S := by
              have hnm := hspec.2.1 (g - 1) (by omega)
              rw [moveC_add, Nat.sub_add_cancel hg1] at hnm
              exact hnm
            have h2 : nextC n (moveC n a0 lastK.val) ∈ S := by
              have hm := hspec.2.2
              rw [moveC_add] at hm
              rw [← moveC_one, moveC_add]
              simpa [lastK, add_assoc] using hm
            simp [step2, h1, h2]
          have hrest_one : ∏ k ∈ ((segSet u).filter (fun k => k.val < offF g p ℓ u + g + 1)).erase lastK,
              step2 q (decide (moveC n a0 k.val ∈ S)) (decide (nextC n (moveC n a0 k.val) ∈ S)) = 1 :=
            Finset.prod_eq_one fun k hk => by
              have hne_l : k ≠ lastK := (Finset.mem_erase.mp hk).1
              have hfilt := Finset.mem_filter.mp (Finset.mem_erase.mp hk).2
              have hseg_k := (Finset.mem_filter.mp hfilt.1).2
              have hk_lt_g : k.val < offF g p ℓ u + g := by
                have : k.val ≠ offF g p ℓ u + g := fun h => hne_l (Fin.ext h)
                omega
              have hnm := hspec.2.1 (k.val - offF g p ℓ u) (by omega)
              rw [moveC_add, show offF g p ℓ u + (k.val - offF g p ℓ u + 1) = k.val + 1 by omega] at hnm
              have hnx : nextC n (moveC n a0 k.val) ∉ S := by
                rw [← moveC_one, moveC_add]; exact hnm
              simp [step2, hnx]
          rw [hlast_val, hrest_one, mul_one]
        · refine Finset.prod_bij
            (fun k hk => (⟨k.val - (offF g p ℓ u + g + 1), by
              have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
              have h2 := (Finset.mem_filter.mp hk).2
              omega⟩ : Fin (ℓ u)))
            (fun _ _ => Finset.mem_univ _)
            (fun k1 hk1 k2 hk2 heq => by
              have h1 := (Finset.mem_filter.mp hk1).2
              have h2 := (Finset.mem_filter.mp hk2).2
              have hv := congrArg Fin.val heq; dsimp only at hv; exact Fin.ext (by omega))
            (fun j _ => ⟨⟨offF g p ℓ u + g + 1 + j.val, by have := offF_step_le_total g p ℓ u; have := j.isLt; omega⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega, by dsimp only; have := j.isLt; omega⟩, by dsimp only; omega⟩,
              Fin.ext (by dsimp only; omega)⟩)
            (fun k hk => by
              have hge : offF g p ℓ u + g + 1 ≤ k.val := not_lt.mp (Finset.mem_filter.mp hk).2
              dsimp only [toPhi]
              rw [← moveC_one, moveC_add,
                show offF g p ℓ u + g + 1 + (k.val - (offF g p ℓ u + g + 1)) = k.val by omega,
                show offF g p ℓ u + g + 1 + (k.val - (offF g p ℓ u + g + 1) + 1) = k.val + 1 by omega])
      rw [Finset.prod_congr rfl fun u _ => heach_u u, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
  have hmaps_mk : ∀ x ∈ (Finset.univ : Finset (Fin n)) ×ˢ compFin p N, mkAF n g p x.1 x.2 ∈ validA := by
    rintro ⟨a0, ℓ⟩ hx
    have hℓ := (Finset.mem_product.mp hx).2
    have hsum_ℓ : ∑ v : Fin p, ℓ v = N := (Finset.mem_filter.mp hℓ).2
    have hsum_tot : ∑ v : Fin p, (g + 1 + ℓ v) = n := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hsum_ℓ, hN_eq]
    have hoff_lt : ∀ u : Fin p, offF g p ℓ u < n := fun u => by
      have := offF_step_le_total g p ℓ u; omega
    have hinj_off : Function.Injective (fun u : Fin p => moveC n a0 (offF g p ℓ u)) := by
      intro u1 u2 heq
      have hv := moveC_injective_lt n a0 (hoff_lt u1) (hoff_lt u2) heq
      by_contra hne
      have hne_v : u1.val ≠ u2.val := fun h => hne (Fin.ext h)
      rcases lt_or_gt_of_ne hne_v with hlt | hgt
      · have := offF_step_le_of_lt g p ℓ hlt; omega
      · have := offF_step_le_of_lt g p ℓ hgt; omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩, ?_⟩
    · dsimp only [mkAF]; rw [Finset.card_image_of_injective _ hinj_off, Finset.card_univ, Fintype.card_fin]
    · intro a ha v hv1 hvg hm
      rcases Finset.mem_image.mp ha with ⟨u1, _, rfl⟩
      rcases Finset.mem_image.mp hm with ⟨u2, _, heq⟩
      rw [moveC_add] at heq
      have hlt1 : offF g p ℓ u1 + v < n := by have := offF_step_le_total g p ℓ u1; omega
      have hveq := moveC_injective_lt n a0 (hoff_lt u2) hlt1 heq
      by_cases h12 : u2.val ≤ u1.val
      · rcases eq_or_lt_of_le h12 with he | hlt
        · have : u2 = u1 := Fin.ext he; rw [this] at hveq; omega
        · have := offF_step_le_of_lt g p ℓ hlt; omega
      · have := offF_step_le_of_lt g p ℓ (show u1.val < u2.val by omega); omega
  have hfiber_p : ∀ A ∈ validA,
      (((Finset.univ : Finset (Fin n)) ×ˢ compFin p N).filter (fun x => mkAF n g p x.1 x.2 = A)).card = p := by
    intro A hA
    have hA_card : A.card = p := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hA).1).2
    have hA_sep := (Finset.mem_filter.mp hA).2
    conv_rhs => rw [← hA_card]
    refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
    · rintro ⟨a0, ℓ⟩ hx
      have hmk := (Finset.mem_filter.mp hx).2
      rw [← hmk]
      exact Finset.mem_image.mpr ⟨⟨0, hp⟩, Finset.mem_univ _, by rw [offF_zero, moveC_zero]⟩
    · rintro ⟨a1, ℓ1⟩ hx1 ⟨a2, ℓ2⟩ hx2 haeq
      dsimp only at haeq; subst haeq
      have hℓ1 := (Finset.mem_product.mp (Finset.mem_filter.mp hx1).1).2
      have hℓ2 := (Finset.mem_product.mp (Finset.mem_filter.mp hx2).1).2
      have hmk1 := (Finset.mem_filter.mp hx1).2
      have hmk2 := (Finset.mem_filter.mp hx2).2
      have htot1 : ∑ v : Fin p, (g + 1 + ℓ1 v) = n := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
          (Finset.mem_filter.mp hℓ1).2, hN_eq]
      have htot2 : ∑ v : Fin p, (g + 1 + ℓ2 v) = n := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
          (Finset.mem_filter.mp hℓ2).2, hN_eq]
      have hlt1 : ∀ u : Fin p, offF g p ℓ1 u < n := fun u => by have := offF_step_le_total g p ℓ1 u; omega
      have hlt2 : ∀ u : Fin p, offF g p ℓ2 u < n := fun u => by have := offF_step_le_total g p ℓ2 u; omega
      let dist : Fin n → ℕ := fun x => (x.val + n - a1.val) % n
      have hdist_move : ∀ k < n, dist (moveC n a1 k) = k := fun k hk => mod_sub_moveC n a1 hk
      have himg_eq : (Finset.univ : Finset (Fin p)).image (offF g p ℓ1) =
          (Finset.univ : Finset (Fin p)).image (offF g p ℓ2) := by
        have h1 : A.image dist = Finset.univ.image (offF g p ℓ1) := by
          rw [← hmk1]; dsimp only [mkAF]; rw [Finset.image_image]
          refine Finset.image_congr fun u _ => hdist_move _ (hlt1 u)
        have h2 : A.image dist = Finset.univ.image (offF g p ℓ2) := by
          rw [← hmk2]; dsimp only [mkAF]; rw [Finset.image_image]
          refine Finset.image_congr fun u _ => hdist_move _ (hlt2 u)
        exact h1.symm.trans h2
      have hstrict1 : StrictMono (offF g p ℓ1) := fun u1 u2 h => by
        have := offF_step_le_of_lt g p ℓ1 h; omega
      have hstrict2 : StrictMono (offF g p ℓ2) := fun u1 u2 h => by
        have := offF_step_le_of_lt g p ℓ2 h; omega
      have hoff_eq : offF g p ℓ1 = offF g p ℓ2 := by
        have hc1 : ((Finset.univ : Finset (Fin p)).image (offF g p ℓ1)).card = p := by
          rw [Finset.card_image_of_injective _ hstrict1.injective, Finset.card_univ, Fintype.card_fin]
        let e1 : Fin p ↪o ℕ := OrderEmbedding.ofStrictMono (offF g p ℓ1) hstrict1
        let e2 : Fin p ↪o ℕ := OrderEmbedding.ofStrictMono (offF g p ℓ2) hstrict2
        have hr1 : Set.range e1 = ((Finset.univ : Finset (Fin p)).image (offF g p ℓ1) : Set ℕ) := by
          ext k; simp [e1]
        have hr2 : Set.range e2 = ((Finset.univ : Finset (Fin p)).image (offF g p ℓ1) : Set ℕ) := by
          rw [himg_eq]; ext k; simp [e2]
        have he1 := Finset.orderEmbOfFin_unique hc1 (fun u => by
          have : e1 u ∈ Set.range e1 := ⟨u, rfl⟩; rw [hr1] at this; exact this) hstrict1
        have he2 := Finset.orderEmbOfFin_unique hc1 (fun u => by
          have : e2 u ∈ Set.range e2 := ⟨u, rfl⟩; rw [hr2] at this; exact this) hstrict2
        funext u
        rw [he1, he2]
      congr 1; funext u
      by_cases hlast : u.val + 1 < p
      · have hs1 := offF_succ g p ℓ1 u hlast
        have hs2 := offF_succ g p ℓ2 u hlast
        have ha := congrFun hoff_eq u
        have hb := congrFun hoff_eq ⟨u.val + 1, hlast⟩
        omega
      · have hu_eq : u = ⟨p - 1, by omega⟩ := Fin.ext (by dsimp only; have := u.isLt; omega)
        rw [hu_eq]
        have hl1 := offF_last g p hp ℓ1
        have hl2 := offF_last g p hp ℓ2
        have ha := congrFun hoff_eq ⟨p - 1, by omega⟩
        omega
    · intro a0 ha0
      let dist : Fin n → ℕ := fun x => (x.val + n - a0.val) % n
      have hdist_lt : ∀ x : Fin n, dist x < n := fun x => Nat.mod_lt _ hn_pos
      have hmove_dist : ∀ x : Fin n, moveC n a0 (dist x) = x := fun x => moveC_mod_sub n a0 x
      have hdist_inj : Function.Injective dist := fun x1 x2 h => by
        rw [← hmove_dist x1, ← hmove_dist x2, h]
      let D := A.image dist
      have hD_card : D.card = p := by rw [Finset.card_image_of_injective _ hdist_inj, hA_card]
      let s : Fin p → ℕ := fun u => D.orderEmbOfFin hD_card u
      have hs_mem : ∀ u : Fin p, s u ∈ D := fun u => Finset.orderEmbOfFin_mem D hD_card u
      have hs_lt : ∀ u : Fin p, s u < n := fun u => by
        rcases Finset.mem_image.mp (hs_mem u) with ⟨x, _, hdx⟩; rw [← hdx]; exact hdist_lt x
      have hs_move_mem : ∀ u : Fin p, moveC n a0 (s u) ∈ A := fun u => by
        rcases Finset.mem_image.mp (hs_mem u) with ⟨x, hx, hdx⟩
        rwa [← hdx, hmove_dist x]
      have h0_mem : 0 ∈ D := by
        refine Finset.mem_image.mpr ⟨a0, ha0, ?_⟩
        dsimp only [dist]; rw [show a0.val + n - a0.val = n by omega, Nat.mod_self]
      have hs0 : s ⟨0, hp⟩ = 0 := by
        rcases (Finset.range_orderEmbOfFin D hD_card).symm.subset h0_mem with ⟨u0, hu0⟩
        have hle : D.orderEmbOfFin hD_card ⟨0, hp⟩ ≤ D.orderEmbOfFin hD_card u0 :=
          (D.orderEmbOfFin hD_card).monotone (show (⟨0, hp⟩ : Fin p) ≤ u0 from Nat.zero_le _)
        rw [hu0] at hle
        exact Nat.eq_zero_of_le_zero hle
      have hs_gap : ∀ (u : Fin p) (hu : u.val + 1 < p), g + 1 ≤ s ⟨u.val + 1, hu⟩ - s u := by
        intro u hu
        have hlt : s u < s ⟨u.val + 1, hu⟩ := (D.orderEmbOfFin hD_card).strictMono (show u < ⟨u.val + 1, hu⟩ from by simp [Fin.lt_def])
        by_contra hlt_g; push_neg at hlt_g
        let v := s ⟨u.val + 1, hu⟩ - s u
        have hnm := hA_sep (moveC n a0 (s u)) (hs_move_mem u) v (by omega) (by omega)
        rw [moveC_add, show s u + v = s ⟨u.val + 1, hu⟩ by omega] at hnm
        exact hnm (hs_move_mem ⟨u.val + 1, hu⟩)
      have hs_last_gap : g + 1 ≤ n - s ⟨p - 1, by omega⟩ := by
        have hlt := hs_lt ⟨p - 1, by omega⟩
        by_contra hlt_g; push_neg at hlt_g
        let v := n - s ⟨p - 1, by omega⟩
        have hnm := hA_sep (moveC n a0 (s ⟨p - 1, by omega⟩)) (hs_move_mem _) v (by omega) (by omega)
        rw [moveC_add, show s ⟨p - 1, by omega⟩ + v = n by omega, moveC_self] at hnm
        exact hnm ha0
      let nextS (u : Fin p) : ℕ := if h : u.val + 1 < p then s ⟨u.val + 1, h⟩ else n
      let ℓ : Fin p → ℕ := fun u => nextS u - s u - (g + 1)
      have hstep_eq : ∀ u : Fin p, g + 1 + ℓ u = nextS u - s u := fun u => by
        dsimp only [ℓ, nextS]
        split_ifs with h
        · have := hs_gap u h; omega
        · have hu_eq : u = ⟨p - 1, by omega⟩ := Fin.ext (by dsimp only; have := u.isLt; omega)
          rw [hu_eq]; omega
      have hoff_eq_s : ∀ u : Fin p, offF g p ℓ u = s u := by
        intro u
        rcases u with ⟨k, hk⟩
        induction k with
        | zero => rw [offF_zero g p hp ℓ, hs0]
        | succ k ih =>
          have hk' : k < p := by omega
          rw [offF_succ g p ℓ ⟨k, hk'⟩ hk, ih hk', hstep_eq ⟨k, hk'⟩]
          dsimp only [nextS]; rw [dif_pos hk]
          have hlt : s ⟨k, hk'⟩ < s ⟨k + 1, hk⟩ := (D.orderEmbOfFin hD_card).strictMono (show (⟨k, hk'⟩ : Fin p) < ⟨k + 1, hk⟩ from by simp [Fin.lt_def])
          omega
      have hsum_ℓ : ∑ u : Fin p, ℓ u = N := by
        have htot : ∑ u : Fin p, (g + 1 + ℓ u) = n := by
          rw [← offF_last g p hp ℓ, hoff_eq_s ⟨p - 1, by omega⟩, hstep_eq ⟨p - 1, by omega⟩]
          dsimp only [nextS]; rw [dif_neg (by omega)]
          have := hs_lt ⟨p - 1, by omega⟩; omega
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← hN_eq] at htot
        omega
      have hℓ_mem : ℓ ∈ compFin p N := by
        refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun u => Finset.mem_range.mpr ?_, hsum_ℓ⟩
        have hle := Finset.single_le_sum (f := ℓ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)
        omega
      have hmk_eq : mkAF n g p a0 ℓ = A := by
        ext x
        simp only [mkAF, Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨u, rfl⟩; rw [hoff_eq_s u]; exact hs_move_mem u
        · intro hx
          have hdx : dist x ∈ D := Finset.mem_image.mpr ⟨x, hx, rfl⟩
          rcases (Finset.range_orderEmbOfFin D hD_card).symm.subset hdx with ⟨u, hu⟩
          refine ⟨u, ?_⟩
          rw [hoff_eq_s u]; dsimp only [s]; rw [hu, hmove_dist x]
      exact ⟨(a0, ℓ), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, hℓ_mem⟩, hmk_eq⟩, rfl⟩
  rw [hsum_A, Finset.mul_sum]
  have hfib := (Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin n)) ×ˢ compFin p N)
    (t := validA)
    (g := fun x => mkAF n g p x.1 x.2)
    (f := fun x => ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun S => ∀ a ∈ mkAF n g p x.1 x.2, a ∈ exitsS n S ∧ gapS n S a = g), q ^ (exitsS n S).card)
    hmaps_mk)
  have hlhs_eq : ∑ A ∈ validA, (p : ℝ) * ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
        (fun S => ∀ a ∈ A, a ∈ exitsS n S ∧ gapS n S a = g), q ^ (exitsS n S).card =
      ∑ x ∈ (Finset.univ : Finset (Fin n)) ×ˢ compFin p N,
        ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
          (fun S => ∀ a ∈ mkAF n g p x.1 x.2, a ∈ exitsS n S ∧ gapS n S a = g), q ^ (exitsS n S).card := by
    rw [← hfib]
    refine Finset.sum_congr rfl fun A hA => ?_
    have hconst : ∑ x ∈ ((Finset.univ : Finset (Fin n)) ×ˢ compFin p N).filter (fun x => mkAF n g p x.1 x.2 = A),
        (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
          (fun S => ∀ a ∈ mkAF n g p x.1 x.2, a ∈ exitsS n S ∧ gapS n S a = g), q ^ (exitsS n S).card) =
        ∑ _x ∈ ((Finset.univ : Finset (Fin n)) ×ˢ compFin p N).filter (fun x => mkAF n g p x.1 x.2 = A),
          (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
            (fun S => ∀ a ∈ A, a ∈ exitsS n S ∧ gapS n S a = g), q ^ (exitsS n S).card) :=
      Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.mp hx).2]
    rw [hconst, Finset.sum_const, nsmul_eq_mul, hfiber_p A hA]
  rw [hlhs_eq, Finset.sum_product]
  have heach_pair : ∀ a0 : Fin n,
      (∑ ℓ ∈ compFin p N, ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
        (fun S => ∀ a ∈ mkAF n g p a0 ℓ, a ∈ exitsS n S ∧ gapS n S a = g), q ^ (exitsS n S).card) =
      q ^ p * ∑ ℓ ∈ compFin p N, ∏ u : Fin p, mat2Pow q (ℓ u) true true := by
    intro a0
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ℓ hℓ => hinner a0 ℓ hℓ
  rw [Finset.sum_congr rfl fun a0 _ => heach_pair a0, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_assoc]

private lemma sum_prod_mat2Pow_approx (p N : ℕ) (hp : 1 ≤ p) (q : ℝ) (hq : 4 ≤ q) :
    let L := 1 + Real.sqrt q
    |(∑ ℓ ∈ compFin p N, ∏ u : Fin p, mat2Pow q (ℓ u) true true) -
        ((Nat.choose (N + p - 1) (p - 1) : ℝ) * L ^ N / (2 : ℝ) ^ p)| ≤
      (L ^ N / (2 : ℝ) ^ p) *
        ((Nat.choose (N + p - 1) (p - 1) : ℝ) * (1 - 2 / L) ^ N +
         ∑ B ∈ (Finset.univ : Finset (Finset (Fin p))).filter (fun B => B ≠ ∅ ∧ B ≠ Finset.univ),
           (L / 2) ^ B.card * ((N + 1 : ℝ)) ^ (p - 1 - B.card)) := by
  classical
  intro L
  have hsq2 : 2 ≤ Real.sqrt q := by
    calc (2 : ℝ) = Real.sqrt (2 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt q := Real.sqrt_le_sqrt (by linarith)
  have hL3 : 3 ≤ L := by dsimp only [L]; linarith
  have hL_pos : 0 < L := by linarith
  have hL_ne : L ≠ 0 := ne_of_gt hL_pos
  let δ : ℝ := (1 - Real.sqrt q) / L
  have habs_δ : |δ| = 1 - 2 / L := by
    dsimp only [δ]
    rw [abs_div, abs_of_pos hL_pos, abs_of_nonpos (by linarith)]
    field_simp [hL_ne]; dsimp only [L]; ring
  have hδ_nn : 0 ≤ 1 - 2 / L := by rw [sub_nonneg, div_le_one hL_pos]; linarith
  have hδ_lt1 : 1 - 2 / L < 1 := by linarith [show 0 < 2 / L by positivity]
  have hmat_eq : ∀ k : ℕ, mat2Pow q k true true = (L ^ k / 2) * (1 + δ ^ k) := fun k => by
    dsimp only [mat2Pow, δ, L]
    rw [div_pow]; field_simp [hL_ne]
  have hprod_eq : ∀ ℓ ∈ compFin p N,
      ∏ u : Fin p, mat2Pow q (ℓ u) true true =
        (L ^ N / (2 : ℝ) ^ p) * ∑ B : Finset (Fin p), ∏ u ∈ B, δ ^ ℓ u := by
    intro ℓ hℓ
    have hsum_ℓ : ∑ u : Fin p, ℓ u = N := (Finset.mem_filter.mp hℓ).2
    rw [Finset.prod_congr rfl fun u _ => hmat_eq (ℓ u), Finset.prod_mul_distrib]
    congr 1
    · rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hsum_ℓ, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
    · have hexp := Finset.prod_add (s := (Finset.univ : Finset (Fin p)))
        (f := fun u => δ ^ ℓ u) (g := fun _ => (1 : ℝ))
      have hcomm : ∏ u : Fin p, (1 + δ ^ ℓ u) = ∏ u : Fin p, (δ ^ ℓ u + 1) :=
        Finset.prod_congr rfl fun _ _ => add_comm _ _
      rw [hcomm, hexp]
      have hpow_univ : (Finset.univ : Finset (Fin p)).powerset = Finset.univ := by ext B; simp
      rw [hpow_univ]
      refine Finset.sum_congr rfl fun B _ => by simp
  rw [Finset.sum_congr rfl hprod_eq, ← Finset.mul_sum, Finset.sum_comm]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (∅ : Finset (Fin p)))]
  have hempty : ∑ _ℓ ∈ compFin p N, ∏ u ∈ (∅ : Finset (Fin p)), δ ^ _ℓ u =
      (Nat.choose (N + p - 1) (p - 1) : ℝ) := by
    simp [card_compFin p N hp]
  rw [hempty, mul_add]
  have hmain_eq : L ^ N / (2 : ℝ) ^ p * (Nat.choose (N + p - 1) (p - 1) : ℝ) =
      (Nat.choose (N + p - 1) (p - 1) : ℝ) * L ^ N / (2 : ℝ) ^ p := by ring
  rw [hmain_eq, add_sub_cancel_left, abs_mul, abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have huniv_mem : (Finset.univ : Finset (Fin p)) ∈ (Finset.univ : Finset (Finset (Fin p))).erase ∅ := by
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro h
    have : (⟨0, hp⟩ : Fin p) ∈ (∅ : Finset (Fin p)) := h ▸ Finset.mem_univ _
    exact Finset.notMem_empty _ this
  rw [← Finset.add_sum_erase _ _ huniv_mem]
  have hfeq : ((Finset.univ : Finset (Finset (Fin p))).erase ∅).erase Finset.univ =
      (Finset.univ : Finset (Finset (Fin p))).filter (fun B => B ≠ ∅ ∧ B ≠ Finset.univ) := by
    ext B; simp [and_comm]
  rw [hfeq]
  have huniv_le : |∑ ℓ ∈ compFin p N, ∏ u : Fin p, δ ^ ℓ u| ≤
      (Nat.choose (N + p - 1) (p - 1) : ℝ) * (1 - 2 / L) ^ N := by
    calc |∑ ℓ ∈ compFin p N, ∏ u : Fin p, δ ^ ℓ u|
        ≤ ∑ ℓ ∈ compFin p N, |∏ u : Fin p, δ ^ ℓ u| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ _ℓ ∈ compFin p N, (1 - 2 / L) ^ N := Finset.sum_congr rfl fun ℓ hℓ => by
          rw [Finset.prod_pow_eq_pow_sum, (Finset.mem_filter.mp hℓ).2, abs_pow, habs_δ]
      _ = (Nat.choose (N + p - 1) (p - 1) : ℝ) * (1 - 2 / L) ^ N := by
          rw [Finset.sum_const, nsmul_eq_mul, card_compFin p N hp]
  have hmid_le : ∀ B ∈ (Finset.univ : Finset (Finset (Fin p))).filter (fun B => B ≠ ∅ ∧ B ≠ Finset.univ),
      |∑ ℓ ∈ compFin p N, ∏ u ∈ B, δ ^ ℓ u| ≤ (L / 2) ^ B.card * ((N + 1 : ℝ)) ^ (p - 1 - B.card) := by
    intro B hB
    have hB_ne_u : B ≠ Finset.univ := (Finset.mem_filter.mp hB).2.2
    have hex_out : ∃ u0 : Fin p, u0 ∉ B := by
      by_contra hall; push_neg at hall; exact hB_ne_u (Finset.eq_univ_iff_forall.mpr hall)
    rcases hex_out with ⟨u0, hu0⟩
    let rest : Finset (Fin p) := (Finset.univ \ B).erase u0
    have hcard_rest : rest.card = p - 1 - B.card := by
      have hmem_u0 : u0 ∈ Finset.univ \ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hu0⟩
      rw [Finset.card_erase_of_mem hmem_u0, Finset.card_sdiff, Finset.inter_univ,
        Finset.card_univ, Fintype.card_fin]
      omega
    let domB := Fintype.piFinset (fun _ : B => Finset.range (N + 1))
    let domR := Fintype.piFinset (fun _ : rest => Finset.range (N + 1))
    let proj : (Fin p → ℕ) → (B → ℕ) × (rest → ℕ) := fun ℓ => (fun u => ℓ u.1, fun u => ℓ u.1)
    have hproj_maps : ∀ ℓ ∈ compFin p N, proj ℓ ∈ domB ×ˢ domR := by
      intro ℓ hℓ
      have hmem := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hℓ).1
      exact Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun u => hmem u.1,
        Fintype.mem_piFinset.mpr fun u => hmem u.1⟩
    have hproj_inj : Set.InjOn proj (compFin p N : Set (Fin p → ℕ)) := by
      intro ℓ1 hℓ1 ℓ2 hℓ2 heq
      have hB_eq : ∀ u ∈ B, ℓ1 u = ℓ2 u := fun u hu => congrFun (congrArg Prod.fst heq) ⟨u, hu⟩
      have hR_eq : ∀ u ∈ rest, ℓ1 u = ℓ2 u := fun u hu => congrFun (congrArg Prod.snd heq) ⟨u, hu⟩
      have hs1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hℓ1)).2
      have hs2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hℓ2)).2
      have hpart : (Finset.univ : Finset (Fin p)).erase u0 = B ∪ rest := by
        ext u; simp only [Finset.mem_erase, Finset.mem_univ, and_true, true_and, Finset.mem_union, rest, Finset.mem_sdiff]
        constructor
        · intro hne
          by_cases hm : u ∈ B
          · exact Or.inl hm
          · exact Or.inr ⟨hne, hm⟩
        · rintro (hm | ⟨hne, _⟩)
          · intro he; exact hu0 (he ▸ hm)
          · exact hne
      have hother_eq : ∑ u ∈ (Finset.univ : Finset (Fin p)).erase u0, ℓ1 u =
          ∑ u ∈ (Finset.univ : Finset (Fin p)).erase u0, ℓ2 u := by
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [hpart, Finset.mem_union] at hu
        rcases hu with hb | hr
        · exact hB_eq u hb
        · exact hR_eq u hr
      have hu0_eq : ℓ1 u0 = ℓ2 u0 := by
        have e1 := Finset.add_sum_erase Finset.univ ℓ1 (Finset.mem_univ u0)
        have e2 := Finset.add_sum_erase Finset.univ ℓ2 (Finset.mem_univ u0)
        omega
      funext u
      by_cases hu : u = u0
      · rw [hu, hu0_eq]
      · have hm : u ∈ B ∪ rest := hpart ▸ Finset.mem_erase.mpr ⟨hu, Finset.mem_univ _⟩
        rcases Finset.mem_union.mp hm with hb | hr
        · exact hB_eq u hb
        · exact hR_eq u hr
    have hgeom : ∑ k ∈ Finset.range (N + 1), (1 - 2 / L) ^ k ≤ L / 2 := by
      have h1 : (∑ k ∈ Finset.range (N + 1), (1 - 2 / L) ^ k) * (1 - (1 - 2 / L)) =
          1 - (1 - 2 / L) ^ (N + 1) := by
        rw [mul_comm]; exact mul_neg_geom_sum (1 - 2 / L) (N + 1)
      have hpos : 0 < 1 - (1 - 2 / L) := by linarith
      have hle1 : (∑ k ∈ Finset.range (N + 1), (1 - 2 / L) ^ k) * (2 / L) ≤ 1 := by
        have hsub : 1 - (1 - 2 / L) = 2 / L := by ring
        rw [hsub] at h1
        have hnn : 0 ≤ (1 - 2 / L) ^ (N + 1) := pow_nonneg hδ_nn _
        linarith
      have h2L : 0 < 2 / L := by positivity
      calc ∑ k ∈ Finset.range (N + 1), (1 - 2 / L) ^ k
          ≤ 1 / (2 / L) := (le_div_iff₀ h2L).mpr hle1
        _ = L / 2 := by field_simp [hL_ne]
    calc |∑ ℓ ∈ compFin p N, ∏ u ∈ B, δ ^ ℓ u|
        ≤ ∑ ℓ ∈ compFin p N, |∏ u ∈ B, δ ^ ℓ u| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ ℓ ∈ compFin p N, ∏ u : B, (1 - 2 / L) ^ (proj ℓ).1 u := Finset.sum_congr rfl fun ℓ _ => by
          rw [Finset.abs_prod, ← Finset.prod_coe_sort B]
          refine Finset.prod_congr rfl fun u _ => by rw [abs_pow, habs_δ]
      _ = ∑ z ∈ (compFin p N).image proj, ∏ u : B, (1 - 2 / L) ^ z.1 u :=
          (Finset.sum_image (f := fun z : (B → ℕ) × (rest → ℕ) => ∏ u : B, (1 - 2 / L) ^ z.1 u) hproj_inj).symm
      _ ≤ ∑ z ∈ domB ×ˢ domR, ∏ u : B, (1 - 2 / L) ^ z.1 u :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun z hz => by rcases Finset.mem_image.mp hz with ⟨ℓ, hℓ, rfl⟩; exact hproj_maps ℓ hℓ)
            (fun _ _ _ => Finset.prod_nonneg fun _ _ => pow_nonneg hδ_nn _)
      _ = (∑ f ∈ domB, ∏ u : B, (1 - 2 / L) ^ f u) * (domR.card : ℝ) := by
          rw [Finset.sum_product]
          simp_rw [Finset.sum_const, nsmul_eq_mul]
          rw [← Finset.mul_sum, mul_comm]
      _ = (∏ _u : B, ∑ k ∈ Finset.range (N + 1), (1 - 2 / L) ^ k) * ((N + 1 : ℝ) ^ (p - 1 - B.card)) := by
          congr 1
          · exact (Finset.prod_univ_sum (t := fun _ : B => Finset.range (N + 1))
              (f := fun (_ : B) (k : ℕ) => (1 - 2 / L) ^ k)).symm
          · dsimp only [domR]
            rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_coe,
              Finset.card_range, hcard_rest]; push_cast; rfl
      _ ≤ (∏ _u : B, (L / 2)) * ((N + 1 : ℝ) ^ (p - 1 - B.card)) :=
          mul_le_mul_of_nonneg_right
            (prod_le_prod_nonneg (fun _ _ => Finset.sum_nonneg fun _ _ => pow_nonneg hδ_nn _) (fun _ _ => hgeom))
            (by positivity)
      _ = (L / 2) ^ B.card * ((N + 1 : ℝ)) ^ (p - 1 - B.card) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  calc |∑ ℓ ∈ compFin p N, ∏ u : Fin p, δ ^ ℓ u +
        ∑ B ∈ (Finset.univ : Finset (Finset (Fin p))).filter (fun B => B ≠ ∅ ∧ B ≠ Finset.univ),
          ∑ ℓ ∈ compFin p N, ∏ u ∈ B, δ ^ ℓ u|
      ≤ |∑ ℓ ∈ compFin p N, ∏ u : Fin p, δ ^ ℓ u| +
        |∑ B ∈ (Finset.univ : Finset (Finset (Fin p))).filter (fun B => B ≠ ∅ ∧ B ≠ Finset.univ),
          ∑ ℓ ∈ compFin p N, ∏ u ∈ B, δ ^ ℓ u| := abs_add_le _ _
    _ ≤ (Nat.choose (N + p - 1) (p - 1) : ℝ) * (1 - 2 / L) ^ N +
        ∑ B ∈ (Finset.univ : Finset (Finset (Fin p))).filter (fun B => B ≠ ∅ ∧ B ≠ Finset.univ),
          |∑ ℓ ∈ compFin p N, ∏ u ∈ B, δ ^ ℓ u| := add_le_add huniv_le (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ _ := add_le_add le_rfl (Finset.sum_le_sum hmid_le)

private lemma alternating_choose_sum (s K : ℕ) (hs : 1 ≤ s) :
    ∑ m ∈ Finset.range (K + 1), (-1 : ℝ) ^ m * (Nat.choose s m : ℝ) =
      (-1 : ℝ) ^ K * (Nat.choose (s - 1) K : ℝ) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    have hch : Nat.choose s (K + 1) = Nat.choose (s - 1) K + Nat.choose (s - 1) (K + 1) := by
      have hs1 : s = (s - 1) + 1 := by omega
      conv_lhs => rw [hs1]
      exact Nat.choose_succ_succ (s - 1) K
    rw [hch, Nat.cast_add, pow_succ]
    ring

private lemma choose_mul_choose_eq (X j m : ℕ) :
    Nat.choose (j + m) j * Nat.choose X (j + m) = Nat.choose X j * Nat.choose (X - j) m := by
  have h := Nat.choose_mul (n := X) (k := j + m) (s := j) (show j ≤ j + m by omega)
  rw [show j + m - j = m by omega, mul_comm] at h
  exact h

private lemma bonferroni_bounds (X j M : ℕ) :
    ∑ m ∈ Finset.range (2 * M + 2), (-1 : ℝ) ^ m * (Nat.choose (j + m) j : ℝ) * (Nat.choose X (j + m) : ℝ) ≤
      (if X = j then (1 : ℝ) else 0) ∧
    (if X = j then (1 : ℝ) else 0) ≤
      ∑ m ∈ Finset.range (2 * M + 1), (-1 : ℝ) ^ m * (Nat.choose (j + m) j : ℝ) * (Nat.choose X (j + m) : ℝ) := by
  by_cases hlt : X < j
  · have hne : X ≠ j := by omega
    rw [if_neg hne]
    have hz : ∀ K : ℕ, ∑ m ∈ Finset.range K,
        (-1 : ℝ) ^ m * (Nat.choose (j + m) j : ℝ) * (Nat.choose X (j + m) : ℝ) = 0 := fun K =>
      Finset.sum_eq_zero fun m _ => by rw [Nat.choose_eq_zero_of_lt (show X < j + m by omega)]; simp
    rw [hz, hz]; exact ⟨le_rfl, le_rfl⟩
  · by_cases heq : X = j
    · subst heq
      rw [if_pos rfl]
      have hone : ∀ K : ℕ, 1 ≤ K → ∑ m ∈ Finset.range K,
          (-1 : ℝ) ^ m * (Nat.choose (X + m) X : ℝ) * (Nat.choose X (X + m) : ℝ) = 1 := by
        intro K hK
        rw [show K = (K - 1) + 1 by omega, Finset.sum_range_succ']
        have hz : ∑ m ∈ Finset.range (K - 1),
            (-1 : ℝ) ^ (m + 1) * (Nat.choose (X + (m + 1)) X : ℝ) * (Nat.choose X (X + (m + 1)) : ℝ) = 0 :=
          Finset.sum_eq_zero fun m _ => by rw [Nat.choose_eq_zero_of_lt (show X < X + (m + 1) by omega)]; simp
        rw [hz]; simp
      rw [hone _ (by omega), hone _ (by omega)]; exact ⟨le_rfl, le_rfl⟩
    · have hgt : j < X := by omega
      rw [if_neg heq]
      have hrew : ∀ K : ℕ,
          ∑ m ∈ Finset.range (K + 1), (-1 : ℝ) ^ m * (Nat.choose (j + m) j : ℝ) * (Nat.choose X (j + m) : ℝ) =
          (Nat.choose X j : ℝ) * ((-1 : ℝ) ^ K * (Nat.choose (X - j - 1) K : ℝ)) := by
        intro K
        rw [← alternating_choose_sum (X - j) K (by omega), Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        have hm : ((Nat.choose (j + m) j : ℝ) * (Nat.choose X (j + m) : ℝ)) =
            (Nat.choose X j : ℝ) * (Nat.choose (X - j) m : ℝ) := by
          exact_mod_cast choose_mul_choose_eq X j m
        calc (-1 : ℝ) ^ m * (Nat.choose (j + m) j : ℝ) * (Nat.choose X (j + m) : ℝ)
            = (-1 : ℝ) ^ m * ((Nat.choose (j + m) j : ℝ) * (Nat.choose X (j + m) : ℝ)) := by ring
          _ = (-1 : ℝ) ^ m * ((Nat.choose X j : ℝ) * (Nat.choose (X - j) m : ℝ)) := by rw [hm]
          _ = _ := by ring
      rw [hrew (2 * M + 1), hrew (2 * M)]
      have hodd : (-1 : ℝ) ^ (2 * M + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
      have heven : (-1 : ℝ) ^ (2 * M) = 1 := by rw [pow_mul]; norm_num
      rw [hodd, heven]
      constructor
      · have hnn : 0 ≤ (Nat.choose X j : ℝ) * (Nat.choose (X - j - 1) (2 * M + 1) : ℝ) := by positivity
        linarith
      · positivity

private lemma exp_neg_le_pow_div (x : ℝ) (hx : 0 < x) (M : ℕ) (hM : 1 ≤ M) :
    Real.exp (-x) ≤ ((M : ℝ) / x) ^ M := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have h1 : x / (M : ℝ) ≤ Real.exp (x / (M : ℝ)) := by
    have := Real.add_one_le_exp (x / (M : ℝ))
    linarith
  have h2 : (x / (M : ℝ)) ^ M ≤ Real.exp x := by
    calc (x / (M : ℝ)) ^ M ≤ (Real.exp (x / (M : ℝ))) ^ M := pow_le_pow_left₀ (by positivity) h1 M
      _ = Real.exp ((M : ℝ) * (x / (M : ℝ))) := (Real.exp_nat_mul _ M).symm
      _ = Real.exp x := by congr 1; field_simp [ne_of_gt hM_pos]
  rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos x)]
  have h3 : ((M : ℝ) / x) ^ M * (x / (M : ℝ)) ^ M = 1 := by
    rw [← mul_pow]
    have : ((M : ℝ) / x) * (x / (M : ℝ)) = 1 := by field_simp [ne_of_gt hx, ne_of_gt hM_pos]
    rw [this, one_pow]
  calc (1 : ℝ) = ((M : ℝ) / x) ^ M * (x / (M : ℝ)) ^ M := h3.symm
    _ ≤ ((M : ℝ) / x) ^ M * Real.exp x := mul_le_mul_of_nonneg_left h2 (by positivity)

set_option maxHeartbeats 800000 in
private lemma per_k_transfer (r t d j : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hd : 2 ≤ d)
    (hL6 : 6 ≤ 1 + Real.sqrt ((2 : ℝ) ^ d - 1)) (hgn : 2 * r + 4 < 6 * t) :
    let n := 6 * t
    let q : ℝ := (2 : ℝ) ^ d - 1
    let L := 1 + Real.sqrt q
    let proper := (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S ≠ ∅ ∧ S ≠ Finset.univ)
    let Z := ∑ S ∈ proper, q ^ (exitsS n S).card
    let E_W := ∑ S ∈ proper, if gapCount n r S = j then q ^ (exitsS n S).card else 0
    let eps_d := 1024 / (2 : ℝ) ^ (6 * d) + 1 / (2 : ℝ) ^ d
    let tailPhi :=
      2 * (2 : ℝ) ^ (4 * d) * (4 : ℝ) ^ (6 * d) * ((3 / 4 : ℝ) * L) ^ n +
      15 * (2 : ℝ) ^ (4 * d) * L ^ 11 * (1 - 1 / (2 * L)) ^ t * L ^ n +
      4 * (n : ℝ) * Real.sqrt q * L ^ (n - (2 * r + 4))
    let tailW :=
      2 * (4 : ℝ) ^ (6 * d) * ((3 / 4 : ℝ) * L) ^ n +
      15 * L ^ 11 * (1 - 1 / (2 * L)) ^ t * L ^ n +
      (n : ℝ) * Real.sqrt q * L ^ (n - (2 * r + 4))
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    letI : Fintype (Submodule (ZMod 2) (Fin n → ZMod 2)) := Fintype.ofFinite _
    let spaces := (Finset.univ : Finset (Submodule (ZMod 2) (Fin n → ZMod 2))).filter (goodSub n)
    let layer := spaces.filter (fun U : Submodule (ZMod 2) (Fin n → ZMod 2) => Module.finrank (ZMod 2) U = d)
    let mixed := layer.filter (fun U => ∀ b : Fin 2, ∃ i ∈ suppSub n U, i.val % 2 = b.val)
    let hosts := fun U : Submodule (ZMod 2) (Fin n → ZMod 2) => spaces.filter (fun E => U ≤ E)
    let topDim := fun U : Submodule (ZMod 2) (Fin n → ZMod 2) => (hosts U).sup (fun E : Submodule (ZMod 2) (Fin n → ZMod 2) => Module.finrank (ZMod 2) E)
    let countTop := fun U : Submodule (ZMod 2) (Fin n → ZMod 2) =>
      ((hosts U).filter (fun E : Submodule (ZMod 2) (Fin n → ZMod 2) => Module.finrank (ZMod 2) E = topDim U)).card
    let small := fun S : Finset (Fin n) =>
      ∏ i ∈ exitsS n S, if gapS n S i < 2 * r + 2 then factorG (gapS n S i) else 1
    let event := mixed.filter (fun U => countTop U = small (suppSub n U) * (2 * r + 1) ^ j)
    |(2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * (mixed.card : ℝ) - Z| ≤ eps_d * Z + tailPhi + tailW ∧
    |(2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * (event.card : ℝ) - E_W| ≤ eps_d * Z + tailPhi + tailW := by
  classical
  intro n q L proper Z E_W eps_d tailPhi tailW spaces layer mixed hosts topDim countTop small event
  have hmem_proper : ∀ S : Finset (Fin n), S ∈ proper ↔ S ≠ ∅ ∧ S ≠ Finset.univ := fun S => by simp [proper]
  have hmem_spaces : ∀ U, U ∈ spaces ↔ goodSub n U := fun U => by simp [spaces]
  have hmem_layer : ∀ U, U ∈ layer ↔ U ∈ spaces ∧ Module.finrank (ZMod 2) U = d := fun U => by simp [layer]
  have hmem_mixed : ∀ U, U ∈ mixed ↔ U ∈ layer ∧ ∀ b : Fin 2, ∃ i ∈ suppSub n U, i.val % 2 = b.val := fun U => by simp [mixed]
  have hmem_event : ∀ U, U ∈ event ↔ U ∈ mixed ∧ countTop U = small (suppSub n U) * (2 * r + 1) ^ j := fun U => by simp [event]
  have hsmall_eq : ∀ S, small S = ∏ i ∈ exitsS n S, if gapS n S i < 2 * r + 2 then factorG (gapS n S i) else 1 := fun S => by
    dsimp only [small]; refine Finset.prod_congr rfl fun i _ => by split_ifs <;> rfl
  have hEW_def : E_W = ∑ S ∈ proper, if gapCount n r S = j then q ^ (exitsS n S).card else 0 := rfl
  have hn_pos : 1 ≤ n := by dsimp only [n]; omega
  have hsq5 : 5 ≤ Real.sqrt q := by dsimp only [L, q] at hL6 ⊢; linarith
  have hq_ge4 : 4 ≤ q := by
    have hq_nn : 0 ≤ q := by
      dsimp only [q]
      have : (4 : ℝ) ≤ (2 : ℝ) ^ d := by
        calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
          _ ≤ (2 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) hd
      linarith
    have hsq := Real.mul_self_sqrt hq_nn
    nlinarith
  have hq_pos : 0 < q := by linarith
  have hq_nat : (q : ℝ) = ((2 ^ d - 1 : ℕ) : ℝ) := by
    dsimp only [q]
    have h1 : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by omega)
    rw [Nat.cast_sub h1]; push_cast; rfl
  let GoodS := proper.filter fun S =>
    6 * d ≤ (exitsS n S).card ∧
    (∃ hne : S ≠ Finset.univ, ∀ α : Fin 4 → ZMod 2, α ≠ 0 → 10 ≤ badRuns n S hne α) ∧
    (∀ a ∈ exitsS n S, gapS n S a < 2 * r + 4)
  let BadS := proper \ GoodS
  let fiber (S : Finset (Fin n)) := layer.filter (fun U => suppSub n U = S)
  let mfiber (S : Finset (Fin n)) := mixed.filter (fun U => suppSub n U = S)
  let efiber (S : Finset (Fin n)) := event.filter (fun U => suppSub n U = S)
  have hsupp_proper : ∀ U ∈ layer, suppSub n U ∈ proper := by
    intro U hU
    have hgood := (hmem_spaces U).mp ((hmem_layer U).mp hU).1
    have hdim := ((hmem_layer U).mp hU).2
    refine (hmem_proper _).mpr ⟨?_, ?_⟩
    · exact Finset.nonempty_iff_ne_empty.mp (suppSub_nonempty_of_finrank n U (by omega))
    · exact suppSub_ne_univ_of_finrank n U hgood (by omega)
  have hmixed_sum : (mixed.card : ℝ) = ∑ S ∈ proper, ((mfiber S).card : ℝ) := by
    have hc := Finset.card_eq_sum_card_fiberwise (f := suppSub n) (s := mixed) (t := proper)
      (fun U hU => hsupp_proper U ((hmem_mixed U).mp hU).1)
    exact_mod_cast hc
  have hevent_sum : (event.card : ℝ) = ∑ S ∈ proper, ((efiber S).card : ℝ) := by
    have hc := Finset.card_eq_sum_card_fiberwise (f := suppSub n) (s := event) (t := proper)
      (fun U hU => hsupp_proper U ((hmem_mixed U).mp ((hmem_event U).mp hU).1).1)
    exact_mod_cast hc
  have hfiber_phi : ∀ (S : Finset (Fin n)) (hne : S ≠ Finset.univ),
      (fiber S).card * glCard d = (phiSet n d S hne).card := by
    intro S hne
    have hfeq : fiber S = (Finset.univ : Finset (Submodule (ZMod 2) (Fin n → ZMod 2))).filter
        (fun U => goodSub n U ∧ Module.finrank (ZMod 2) U = d ∧ suppSub n U = S) := by
      ext U; simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and, hmem_layer, hmem_spaces]; tauto
    rw [hfeq]
    convert card_spaces_supp_mul_gl n d S hne
  have hgood_props : ∀ S ∈ GoodS,
      (mfiber S).card = (fiber S).card ∧
      (efiber S).card = (if gapCount n r S = j then (fiber S).card else 0) ∧
      |(2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((fiber S).card : ℝ) - q ^ (exitsS n S).card| ≤
        eps_d * q ^ (exitsS n S).card := by
    intro S hS
    have hS_prop := (Finset.mem_filter.mp hS).1
    rcases (Finset.mem_filter.mp hS).2 with ⟨hm6, ⟨hne, hbad10⟩, hgap_lt⟩
    have hbad1 : ∀ α : Fin 4 → ZMod 2, α ≠ 0 → 1 ≤ badRuns n S hne α := fun α hα => le_trans (by omega) (hbad10 α hα)
    have hmixS : ∀ b : Fin 2, ∃ i ∈ S, i.val % 2 = b.val := mixed_of_badRuns_pos n S hne hbad1
    have hsurjS : Function.Surjective ((parityMap n).comp (embedRuns n S hne)) := surj_of_badRuns_pos n S hne hbad1
    have hmf : mfiber S = fiber S := by
      ext U; simp only [mfiber, fiber, Finset.mem_filter, hmem_mixed]
      constructor
      · rintro ⟨⟨hU, _⟩, hsup⟩; exact ⟨hU, hsup⟩
      · rintro ⟨hU, hsup⟩; exact ⟨⟨hU, by rw [hsup]; exact hmixS⟩, hsup⟩
    have hef : efiber S = if gapCount n r S = j then fiber S else ∅ := by
      have hct : ∀ U ∈ fiber S, countTop U = small S * (2 * r + 1) ^ (gapCount n r S) := by
        intro U hU
        have hUl := (Finset.mem_filter.mp hU).1
        have hsup := (Finset.mem_filter.mp hU).2
        have hUg := (hmem_spaces U).mp ((hmem_layer U).mp hUl).1
        have hUd := ((hmem_layer U).mp hUl).2
        have hsurjU : Function.Surjective ((parityMap n).comp
            (embedRuns n (suppSub n U) (suppSub_ne_univ_of_finrank n U hUg (by omega)))) := by
          subst hsup; exact hsurjS
        have hprod : countTop U = ∏ a ∈ exitsS n S, factorG (gapS n S a) := by
          have h0 := countTop_eq_prod_factor n U hUg (by omega) hsurjU
          rw [hsup] at h0
          convert h0
        rw [hprod]
        rw [← Finset.prod_filter_mul_prod_filter_not (exitsS n S) (fun a => gapS n S a < 2 * r + 2)]
        congr 1
        · rw [hsmall_eq S]
          rw [← Finset.prod_filter_mul_prod_filter_not (exitsS n S) (fun a => gapS n S a < 2 * r + 2)]
          have h1 : ∏ a ∈ (exitsS n S).filter (fun a => gapS n S a < 2 * r + 2),
              (if gapS n S a < 2 * r + 2 then factorG (gapS n S a) else 1) =
              ∏ a ∈ (exitsS n S).filter (fun a => gapS n S a < 2 * r + 2), factorG (gapS n S a) :=
            Finset.prod_congr rfl fun a ha => if_pos (Finset.mem_filter.mp ha).2
          have h2 : ∏ a ∈ (exitsS n S).filter (fun a => ¬ gapS n S a < 2 * r + 2),
              (if gapS n S a < 2 * r + 2 then factorG (gapS n S a) else 1) = 1 :=
            Finset.prod_eq_one fun a ha => if_neg (Finset.mem_filter.mp ha).2
          rw [h1, h2, mul_one]
        · rw [← Finset.prod_filter_mul_prod_filter_not
            ((exitsS n S).filter (fun a => ¬ gapS n S a < 2 * r + 2)) (fun a => gapS n S a = 2 * r + 2)]
          have hfeq1 : ((exitsS n S).filter (fun a => ¬ gapS n S a < 2 * r + 2)).filter
              (fun a => gapS n S a = 2 * r + 2) = (exitsS n S).filter (fun a => gapS n S a = 2 * r + 2) := by
            ext a; simp only [Finset.mem_filter]; constructor
            · rintro ⟨⟨ha, _⟩, he⟩; exact ⟨ha, he⟩
            · rintro ⟨ha, he⟩; exact ⟨⟨ha, by omega⟩, he⟩
          have h1 : ∏ a ∈ ((exitsS n S).filter (fun a => ¬ gapS n S a < 2 * r + 2)).filter
              (fun a => gapS n S a = 2 * r + 2), factorG (gapS n S a) = (2 * r + 1) ^ gapCount n r S := by
            rw [hfeq1]
            have hval : ∀ a ∈ (exitsS n S).filter (fun a => gapS n S a = 2 * r + 2),
                factorG (gapS n S a) = 2 * r + 1 := fun a ha => by
              rw [(Finset.mem_filter.mp ha).2]; dsimp only [factorG]
              have : (2 * r + 2 - 2) % 2 = 0 := by omega
              rw [if_pos this]; omega
            rw [Finset.prod_congr rfl hval, Finset.prod_const]; rfl
          have h2 : ∏ a ∈ ((exitsS n S).filter (fun a => ¬ gapS n S a < 2 * r + 2)).filter
              (fun a => ¬ gapS n S a = 2 * r + 2), factorG (gapS n S a) = 1 :=
            Finset.prod_eq_one fun a ha => by
              have hha := Finset.mem_filter.mp ha
              have hha1 := Finset.mem_filter.mp hha.1
              have hlt := hgap_lt a hha1.1
              have heq3 : gapS n S a = 2 * r + 3 := by omega
              rw [heq3]; dsimp only [factorG]
              have : (2 * r + 3 - 2) % 2 ≠ 0 := by omega
              rw [if_neg this]
          rw [h1, h2, mul_one]
      have hsmall_pos : 0 < small S := by
        rw [hsmall_eq S]
        exact Finset.prod_pos fun a _ => by
          split_ifs
          · dsimp only [factorG]; split_ifs <;> omega
          · omega
      split_ifs with hX
      · ext U
        simp only [efiber, Finset.mem_filter, hmem_event]
        constructor
        · rintro ⟨⟨hUm, _⟩, hsup⟩; exact Finset.mem_filter.mpr ⟨((hmem_mixed U).mp hUm).1, hsup⟩
        · intro hUf
          have hUm : U ∈ mixed := by
            have : U ∈ mfiber S := hmf.symm ▸ hUf
            exact (Finset.mem_filter.mp this).1
          have hsup := (Finset.mem_filter.mp hUf).2
          refine ⟨⟨hUm, ?_⟩, hsup⟩
          rw [hct U hUf, hsup, hX]
      · ext U
        simp only [efiber, Finset.mem_filter, hmem_event, Finset.notMem_empty, iff_false]
        rintro ⟨⟨hUm, hev⟩, hsup⟩
        have hUf : U ∈ fiber S := Finset.mem_filter.mpr ⟨((hmem_mixed U).mp hUm).1, hsup⟩
        rw [hct U hUf, hsup] at hev
        have hpow := Nat.eq_of_mul_eq_mul_left hsmall_pos hev
        exact hX (Nat.pow_right_injective (by omega : 2 ≤ 2 * r + 1) hpow)
    have hfour : |(2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((fiber S).card : ℝ) - q ^ (exitsS n S).card| ≤
        eps_d * q ^ (exitsS n S).card := by
      have hmul : (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((fiber S).card : ℝ) =
          (2 : ℝ) ^ (4 * d) * ((phiSet n d S hne).card : ℝ) := by
        have hnat := hfiber_phi S hne
        have hr : ((fiber S).card : ℝ) * (glCard d : ℝ) = ((phiSet n d S hne).card : ℝ) := by exact_mod_cast hnat
        rw [mul_assoc, mul_comm (glCard d : ℝ), hr]
      rw [hmul]
      exact phiCount_fourier_approx n d hd S hne hm6 hbad10
    refine ⟨by rw [hmf], ?_, hfour⟩
    rw [hef]; split_ifs <;> simp
  let Bad1 := proper.filter (fun S => (exitsS n S).card < 6 * d)
  let Bad2 := proper.filter (fun S => ∃ hne : S ≠ Finset.univ, ∃ α : Fin 4 → ZMod 2, α ≠ 0 ∧ badRuns n S hne α < 10)
  let Bad3 := proper.filter (fun S =>
    (∃ hne : S ≠ Finset.univ, ∀ α : Fin 4 → ZMod 2, α ≠ 0 → 10 ≤ badRuns n S hne α) ∧
    (∃ a ∈ exitsS n S, 2 * r + 4 ≤ gapS n S a))
  have hBad_cover : BadS ⊆ Bad1 ∪ Bad2 ∪ Bad3 := by
    intro S hS
    have hSp := (Finset.mem_sdiff.mp hS).1
    have hnot := (Finset.mem_sdiff.mp hS).2
    have hne : S ≠ Finset.univ := ((hmem_proper S).mp hSp).2
    by_cases hm : (exitsS n S).card < 6 * d
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hSp, hm⟩))
    · by_cases hba : ∀ α : Fin 4 → ZMod 2, α ≠ 0 → 10 ≤ badRuns n S hne α
      · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hSp, ⟨hne, hba⟩, ?_⟩)
        by_contra hall; push_neg at hall
        exact hnot (Finset.mem_filter.mpr ⟨hSp, by omega, ⟨hne, hba⟩, hall⟩)
      · push_neg at hba
        rcases hba with ⟨α, hα, hlt⟩
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hSp, hne, α, hα, hlt⟩))
  have hW_Bad1 : ∑ S ∈ Bad1, q ^ (exitsS n S).card ≤ 2 * (4 : ℝ) ^ (6 * d) * ((3 / 4 : ℝ) * L) ^ n := by
    calc ∑ S ∈ Bad1, q ^ (exitsS n S).card
        ≤ ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => (exitsS n S).card < 6 * d),
            q ^ (exitsS n S).card :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun S hS => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hS).2⟩)
            (fun _ _ _ => by positivity)
      _ ≤ 2 * (4 : ℝ) ^ (6 * d) * ((3 / 4 : ℝ) * L) ^ n := sum_W_small_m_le n hn_pos q hq_ge4 (6 * d)
  have hW_Bad2 : ∑ S ∈ Bad2, q ^ (exitsS n S).card ≤ 15 * L ^ 11 * (1 - 1 / (2 * L)) ^ t * L ^ n := by
    let nz4 := (Finset.univ : Finset (Fin 4 → ZMod 2)).erase 0
    have hnz4_card : nz4.card = 15 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]; norm_num
    have hsub2 : Bad2 ⊆ nz4.biUnion (fun α => (Finset.univ : Finset (Finset (Fin n))).filter
        (fun S => ∃ hne : S ≠ Finset.univ, S ≠ ∅ ∧ badRuns n S hne α < 10)) := by
      intro S hS
      have hSp := (Finset.mem_filter.mp hS).1
      rcases (Finset.mem_filter.mp hS).2 with ⟨hne, α, hα, hlt⟩
      exact Finset.mem_biUnion.mpr ⟨α, Finset.mem_erase.mpr ⟨hα, Finset.mem_univ _⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, ((hmem_proper S).mp hSp).1, hlt⟩⟩
    calc ∑ S ∈ Bad2, q ^ (exitsS n S).card
        ≤ ∑ S ∈ nz4.biUnion (fun α => (Finset.univ : Finset (Finset (Fin n))).filter
            (fun S => ∃ hne : S ≠ Finset.univ, S ≠ ∅ ∧ badRuns n S hne α < 10)), q ^ (exitsS n S).card :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun _ _ _ => by positivity)
      _ ≤ ∑ α ∈ nz4, ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
            (fun S => ∃ hne : S ≠ Finset.univ, S ≠ ∅ ∧ badRuns n S hne α < 10), q ^ (exitsS n S).card :=
          sum_biUnion_le_sum_nonneg fun _ => by positivity
      _ ≤ ∑ _α ∈ nz4, L ^ 11 * (1 - 1 / (2 * L)) ^ t * L ^ n :=
          Finset.sum_le_sum fun α hα => sum_W_bad_alpha_le t ht q hL6 α (Finset.mem_erase.mp hα).1
      _ = 15 * L ^ 11 * (1 - 1 / (2 * L)) ^ t * L ^ n := by
          rw [Finset.sum_const, nsmul_eq_mul, hnz4_card]; push_cast; ring
  have hW_Bad3 : ∑ S ∈ Bad3, q ^ (exitsS n S).card ≤ (n : ℝ) * Real.sqrt q * L ^ (n - (2 * r + 4)) := by
    calc ∑ S ∈ Bad3, q ^ (exitsS n S).card
        ≤ ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => ∃ a ∈ exitsS n S, 2 * r + 4 ≤ gapS n S a),
            q ^ (exitsS n S).card :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun S hS => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hS).2.2⟩)
            (fun _ _ _ => by positivity)
      _ ≤ (n : ℝ) * Real.sqrt q * L ^ (n - (2 * r + 4)) := sum_W_big_gap_le n (2 * r + 4) (by omega) hgn q (by linarith)
  have hBad_W : ∑ S ∈ BadS, q ^ (exitsS n S).card ≤ tailW := by
    calc ∑ S ∈ BadS, q ^ (exitsS n S).card
        ≤ ∑ S ∈ Bad1 ∪ Bad2 ∪ Bad3, q ^ (exitsS n S).card :=
          Finset.sum_le_sum_of_subset_of_nonneg hBad_cover (fun _ _ _ => by positivity)
      _ ≤ ∑ S ∈ Bad1 ∪ Bad2, q ^ (exitsS n S).card + ∑ S ∈ Bad3, q ^ (exitsS n S).card :=
          sum_union_le_nonneg (fun _ => by positivity)
      _ ≤ (∑ S ∈ Bad1, q ^ (exitsS n S).card + ∑ S ∈ Bad2, q ^ (exitsS n S).card) + ∑ S ∈ Bad3, q ^ (exitsS n S).card :=
          (add_le_add (sum_union_le_nonneg (fun _ => by positivity)) le_rfl)
      _ ≤ tailW := by dsimp only [tailW]; linarith
  have hBad_Phi : ∑ S ∈ BadS, (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((fiber S).card : ℝ) ≤ tailPhi := by
    have hphi_le_q : ∀ S ∈ proper,
        (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((fiber S).card : ℝ) ≤ (2 : ℝ) ^ (4 * d) * q ^ (exitsS n S).card := by
      intro S hS
      have hne := ((hmem_proper S).mp hS).2
      have h1 : (glCard d : ℝ) * ((fiber S).card : ℝ) = ((phiSet n d S hne).card : ℝ) := by
        have := hfiber_phi S hne; rw [mul_comm] at this; exact_mod_cast this
      rw [mul_assoc, h1]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [hq_nat]; exact_mod_cast phiCount_le_pow n d S hne
    have hphi_le_4 : ∀ S ∈ Bad3,
        (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((fiber S).card : ℝ) ≤ 4 * q ^ (exitsS n S).card := by
      intro S hS
      rcases (Finset.mem_filter.mp hS).2.1 with ⟨hne, hbad10⟩
      have hsurj := surj_of_badRuns_pos n S hne (fun α hα => le_trans (by omega) (hbad10 α hα))
      have h1 : (glCard d : ℝ) * ((fiber S).card : ℝ) = ((phiSet n d S hne).card : ℝ) := by
        have := hfiber_phi S hne; rw [mul_comm] at this; exact_mod_cast this
      rw [mul_assoc, h1, hq_nat]
      exact_mod_cast phiCount_le_rank4 n d hd S hne hsurj
    calc ∑ S ∈ BadS, (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((fiber S).card : ℝ)
        ≤ ∑ S ∈ Bad1 ∪ Bad2 ∪ Bad3, (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((fiber S).card : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hBad_cover (fun _ _ _ => by positivity)
      _ ≤ (∑ S ∈ Bad1, (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((fiber S).card : ℝ) +
           ∑ S ∈ Bad2, (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((fiber S).card : ℝ)) +
          ∑ S ∈ Bad3, (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((fiber S).card : ℝ) :=
          (sum_union_le_nonneg (fun _ => by positivity)).trans
            (add_le_add (sum_union_le_nonneg (fun _ => by positivity)) le_rfl)
      _ ≤ ((2 : ℝ) ^ (4 * d) * ∑ S ∈ Bad1, q ^ (exitsS n S).card +
           (2 : ℝ) ^ (4 * d) * ∑ S ∈ Bad2, q ^ (exitsS n S).card) +
          4 * ∑ S ∈ Bad3, q ^ (exitsS n S).card := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine add_le_add (add_le_add ?_ ?_) ?_
          · exact Finset.sum_le_sum fun S hS => hphi_le_q S (Finset.mem_filter.mp hS).1
          · exact Finset.sum_le_sum fun S hS => hphi_le_q S (Finset.mem_filter.mp hS).1
          · exact Finset.sum_le_sum hphi_le_4
      _ ≤ tailPhi := by
          dsimp only [tailPhi]
          have h1 := mul_le_mul_of_nonneg_left hW_Bad1 (show (0 : ℝ) ≤ (2 : ℝ) ^ (4 * d) by positivity)
          have h2 := mul_le_mul_of_nonneg_left hW_Bad2 (show (0 : ℝ) ≤ (2 : ℝ) ^ (4 * d) by positivity)
          have h3 := mul_le_mul_of_nonneg_left hW_Bad3 (by norm_num : (0 : ℝ) ≤ 4)
          linarith
  have hpart : proper = GoodS ∪ BadS := by
    ext S; simp only [BadS, GoodS, Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter]; tauto
  have hdisj : Disjoint GoodS BadS := disjoint_sdiff_self_right
  have hgood_W_le_Z : ∑ S ∈ GoodS, q ^ (exitsS n S).card ≤ Z := by
    dsimp only [Z]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
  constructor
  · rw [hmixed_sum, Finset.mul_sum]
    conv_lhs => dsimp only [Z]
    rw [hpart, Finset.sum_union hdisj, Finset.sum_union hdisj]
    have hdiff : (∑ S ∈ GoodS, (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((mfiber S).card : ℝ) +
        ∑ S ∈ BadS, (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((mfiber S).card : ℝ)) -
        (∑ S ∈ GoodS, q ^ (exitsS n S).card + ∑ S ∈ BadS, q ^ (exitsS n S).card) =
        (∑ S ∈ GoodS, ((2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((fiber S).card : ℝ) - q ^ (exitsS n S).card)) +
        ∑ S ∈ BadS, (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((mfiber S).card : ℝ) -
        ∑ S ∈ BadS, q ^ (exitsS n S).card := by
      have hg : ∑ S ∈ GoodS, (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((mfiber S).card : ℝ) =
          ∑ S ∈ GoodS, (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((fiber S).card : ℝ) :=
        Finset.sum_congr rfl fun S hS => by rw [(hgood_props S hS).1]
      rw [hg, Finset.sum_sub_distrib]; ring
    rw [hdiff]
    have hmf_le : ∑ S ∈ BadS, (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((mfiber S).card : ℝ) ≤ tailPhi := by
      refine (Finset.sum_le_sum fun S _ => ?_).trans hBad_Phi
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact_mod_cast Finset.card_le_card (fun U hU => Finset.mem_filter.mpr
        ⟨((hmem_mixed U).mp (Finset.mem_filter.mp hU).1).1, (Finset.mem_filter.mp hU).2⟩)
    have htri1 : |(∑ S ∈ GoodS, ((2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((fiber S).card : ℝ) - q ^ (exitsS n S).card)) +
        ∑ S ∈ BadS, (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((mfiber S).card : ℝ) -
        ∑ S ∈ BadS, q ^ (exitsS n S).card| ≤
        |∑ S ∈ GoodS, ((2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((fiber S).card : ℝ) - q ^ (exitsS n S).card)| +
        |∑ S ∈ BadS, (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((mfiber S).card : ℝ)| +
        |∑ S ∈ BadS, q ^ (exitsS n S).card| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    have hgd : |∑ S ∈ GoodS, ((2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((fiber S).card : ℝ) - q ^ (exitsS n S).card)| ≤
        eps_d * Z := by
      calc _ ≤ ∑ S ∈ GoodS, |(2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((fiber S).card : ℝ) - q ^ (exitsS n S).card| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ S ∈ GoodS, eps_d * q ^ (exitsS n S).card := Finset.sum_le_sum fun S hS => (hgood_props S hS).2.2
        _ = eps_d * ∑ S ∈ GoodS, q ^ (exitsS n S).card := (Finset.mul_sum _ _ _).symm
        _ ≤ eps_d * Z := mul_le_mul_of_nonneg_left hgood_W_le_Z (by positivity)
    have hnn1 : 0 ≤ ∑ S ∈ BadS, (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((mfiber S).card : ℝ) :=
      Finset.sum_nonneg fun _ _ => mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    have hnn2 : 0 ≤ ∑ S ∈ BadS, q ^ (exitsS n S).card :=
      Finset.sum_nonneg fun _ _ => pow_nonneg (le_of_lt hq_pos) _
    rw [abs_of_nonneg hnn1, abs_of_nonneg hnn2] at htri1
    linarith
  · rw [hevent_sum, Finset.mul_sum]
    rw [hEW_def, hpart, Finset.sum_union hdisj, Finset.sum_union hdisj]
    have hdiff : (∑ S ∈ GoodS, (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((efiber S).card : ℝ) +
        ∑ S ∈ BadS, (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((efiber S).card : ℝ)) -
        (∑ S ∈ GoodS, (if gapCount n r S = j then q ^ (exitsS n S).card else 0) +
         ∑ S ∈ BadS, (if gapCount n r S = j then q ^ (exitsS n S).card else 0)) =
        (∑ S ∈ GoodS, (if gapCount n r S = j then
          (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((fiber S).card : ℝ) - q ^ (exitsS n S).card else 0)) +
        ∑ S ∈ BadS, (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((efiber S).card : ℝ) -
        ∑ S ∈ BadS, (if gapCount n r S = j then q ^ (exitsS n S).card else 0) := by
      have hg : ∑ S ∈ GoodS, (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((efiber S).card : ℝ) -
          ∑ S ∈ GoodS, (if gapCount n r S = j then q ^ (exitsS n S).card else 0) =
          ∑ S ∈ GoodS, (if gapCount n r S = j then
            (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((fiber S).card : ℝ) - q ^ (exitsS n S).card else 0) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun S hS => ?_
        rw [(hgood_props S hS).2.1]
        split_ifs <;> simp
      linarith
    rw [hdiff]
    have hef_le : ∑ S ∈ BadS, (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((efiber S).card : ℝ) ≤ tailPhi := by
      refine (Finset.sum_le_sum fun S _ => ?_).trans hBad_Phi
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact_mod_cast Finset.card_le_card (fun U hU => Finset.mem_filter.mpr
        ⟨((hmem_mixed U).mp ((hmem_event U).mp (Finset.mem_filter.mp hU).1).1).1, (Finset.mem_filter.mp hU).2⟩)
    have hbw_le : ∑ S ∈ BadS, (if gapCount n r S = j then q ^ (exitsS n S).card else 0) ≤ tailW := by
      refine (Finset.sum_le_sum fun S _ => ?_).trans hBad_W
      split_ifs
      · exact le_rfl
      · positivity
    have htri1 : |(∑ S ∈ GoodS, (if gapCount n r S = j then
          (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((fiber S).card : ℝ) - q ^ (exitsS n S).card else 0)) +
        ∑ S ∈ BadS, (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((efiber S).card : ℝ) -
        ∑ S ∈ BadS, (if gapCount n r S = j then q ^ (exitsS n S).card else 0)| ≤
        |∑ S ∈ GoodS, (if gapCount n r S = j then
          (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((fiber S).card : ℝ) - q ^ (exitsS n S).card else 0)| +
        |∑ S ∈ BadS, (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((efiber S).card : ℝ)| +
        |∑ S ∈ BadS, (if gapCount n r S = j then q ^ (exitsS n S).card else 0)| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    have hgd : |∑ S ∈ GoodS, (if gapCount n r S = j then
          (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((fiber S).card : ℝ) - q ^ (exitsS n S).card else 0)| ≤
        eps_d * Z := by
      calc _ ≤ ∑ S ∈ GoodS, |if gapCount n r S = j then
              (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((fiber S).card : ℝ) - q ^ (exitsS n S).card else 0| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ S ∈ GoodS, eps_d * q ^ (exitsS n S).card := Finset.sum_le_sum fun S hS => by
            split_ifs
            · exact (hgood_props S hS).2.2
            · simp only [abs_zero]; positivity
        _ = eps_d * ∑ S ∈ GoodS, q ^ (exitsS n S).card := (Finset.mul_sum _ _ _).symm
        _ ≤ eps_d * Z := mul_le_mul_of_nonneg_left hgood_W_le_Z (by positivity)
    have hnn1 : 0 ≤ ∑ S ∈ BadS, (2 : ℝ) ^ (4 * d) * (glCard d : ℝ) * ((efiber S).card : ℝ) :=
      Finset.sum_nonneg fun _ _ => mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    have hnn2 : 0 ≤ ∑ S ∈ BadS, (if gapCount n r S = j then q ^ (exitsS n S).card else 0) :=
      Finset.sum_nonneg fun _ _ => by
        split_ifs
        · exact pow_nonneg (le_of_lt hq_pos) _
        · exact le_rfl
    rw [abs_of_nonneg hnn1, abs_of_nonneg hnn2] at htri1
    linarith

private lemma tendsto_finset_sum' {ι : Type*} (s : Finset ι) {f : ι → ℕ → ℝ} {a : ι → ℝ}
    (h : ∀ i ∈ s, Filter.Tendsto (f i) Filter.atTop (nhds (a i))) :
    Filter.Tendsto (fun k => ∑ i ∈ s, f i k) Filter.atTop (nhds (∑ i ∈ s, a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tendsto_const_nhds
  | @insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact ((h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))).congr (fun _ => rfl)

private lemma tendsto_finset_prod' {ι : Type*} (s : Finset ι) {f : ι → ℕ → ℝ} {a : ι → ℝ}
    (h : ∀ i ∈ s, Filter.Tendsto (f i) Filter.atTop (nhds (a i))) :
    Filter.Tendsto (fun k => ∏ i ∈ s, f i k) Filter.atTop (nhds (∏ i ∈ s, a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tendsto_const_nhds
  | @insert i s hi ih =>
    simp_rw [Finset.prod_insert hi]
    exact ((h i (Finset.mem_insert_self i s)).mul
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))).congr (fun _ => rfl)

private lemma tendsto_pow_atTop' {m : ℕ} (hm : m ≠ 0) :
    Filter.Tendsto (fun x : ℝ => x ^ m) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro B
  refine ⟨max B 1, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hxB : B ≤ x := le_trans (le_max_left _ _) hx
  exact le_trans hxB (le_self_pow₀ hx1 hm)

private lemma tendsto_choose_div_pow (m : ℕ) (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun k => (Nat.choose (f k + m) m : ℝ) / ((f k : ℝ) ^ m)) Filter.atTop
      (nhds (1 / (Nat.factorial m : ℝ))) := by
  have hrew : ∀ᶠ k in Filter.atTop,
      (Nat.choose (f k + m) m : ℝ) / ((f k : ℝ) ^ m) =
      (1 / (Nat.factorial m : ℝ)) * ∏ i ∈ Finset.range m, ((1 : ℝ) + ((m - i : ℕ) : ℝ) / (f k : ℝ)) := by
    filter_upwards [hf.eventually_ge_atTop 1] with k hk
    have hfk_pos : (0 : ℝ) < (f k : ℝ) := by exact_mod_cast hk
    have hfk_ne : (f k : ℝ) ≠ 0 := ne_of_gt hfk_pos
    have hch : (Nat.choose (f k + m) m : ℝ) * (Nat.factorial m : ℝ) =
        ∏ i ∈ Finset.range m, ((f k + m - i : ℕ) : ℝ) := by
      have hnat := Nat.choose_mul_factorial_mul_factorial (show m ≤ f k + m by omega)
      have hdesc : Nat.choose (f k + m) m * Nat.factorial m = Nat.descFactorial (f k + m) m :=
        (mul_comm _ _).trans (Nat.descFactorial_eq_factorial_mul_choose (f k + m) m).symm
      rw [Nat.descFactorial_eq_prod_range] at hdesc
      exact_mod_cast hdesc
    have hfac_ne : (Nat.factorial m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    have hprod_div : (∏ i ∈ Finset.range m, ((f k + m - i : ℕ) : ℝ)) / (f k : ℝ) ^ m =
        ∏ i ∈ Finset.range m, ((1 : ℝ) + ((m - i : ℕ) : ℝ) / (f k : ℝ)) := by
      have hpow : (f k : ℝ) ^ m = ∏ _i ∈ Finset.range m, (f k : ℝ) := by
        rw [Finset.prod_const, Finset.card_range]
      rw [hpow, ← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun i hi => ?_
      have hi_lt : i < m := Finset.mem_range.mp hi
      have hsub : f k + m - i = f k + (m - i) := by omega
      rw [hsub, Nat.cast_add, add_div, div_self hfk_ne]
    rw [← hprod_div, ← hch]
    field_simp [hfac_ne, hfk_ne]
  rw [Filter.tendsto_congr' hrew]
  have hprod_lim : Filter.Tendsto (fun k => ∏ i ∈ Finset.range m, ((1 : ℝ) + ((m - i : ℕ) : ℝ) / (f k : ℝ)))
      Filter.atTop (nhds (∏ _i ∈ Finset.range m, (1 : ℝ))) := by
    refine tendsto_finset_prod' _ fun i _ => ?_
    have hinv : Filter.Tendsto (fun k => ((m - i : ℕ) : ℝ) / (f k : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hf)
    simpa using tendsto_const_nhds.add hinv
  have hlim := (tendsto_const_nhds (x := 1 / (Nat.factorial m : ℝ))).mul hprod_lim
  simpa using hlim

set_option maxHeartbeats 800000 in
private lemma main :
    ∀ (r : ℕ), 1 ≤ r → ∀ T D : ℕ → ℕ, Filter.Tendsto T Filter.atTop Filter.atTop →
      (∀ k, 2 ≤ D k) → ∀ τ : ℝ, 0 < τ →
      Filter.Tendsto (fun k => 6*(T k : ℝ)/
        (1+Real.sqrt ((2 : ℝ)^(D k)-1))^(2*r+1)) Filter.atTop (nhds τ) →
      ∀ j : ℕ, Filter.Tendsto (fun k : ℕ =>
      letI : ∀ p : Prop, Decidable p := Classical.propDecidable
      let t := T k
      let d := D k
      let F := ZMod 2
      let n := 6*t
      let W := Fin n → F
      letI : Fintype (Submodule F W) := Fintype.ofFinite _
      let next := fun i : Fin n =>
        (⟨(i.val+1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
      let h := fun (i : Fin n) (b : Fin 4) =>
        if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2)
        then (1:F) else 0
      let good := fun U : Submodule F W =>
        (∀ x ∈ U, ∀ b : Fin 4, (∑ i, h i b * x i) = 0) ∧
        (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
      let supp := fun U : Submodule F W =>
        Finset.univ.filter (fun i : Fin n => ∃ x ∈ U, x i ≠ 0)
      let spaces := (Finset.univ : Finset (Submodule F W)).filter good
      let layer := spaces.filter (fun U : Submodule F W => Module.finrank F U = d)
      let mixed := layer.filter (fun U => ∀ b : Fin 2, ∃ i ∈ supp U, i.val % 2 = b.val)
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
      let small := fun S : Finset (Fin n) =>
        ∏ i ∈ exits S, if gap S i < 2*r+2 then factor (gap S i) else 1
      let event := mixed.filter (fun U => countTop U = small (supp U) * (2*r+1)^j)
      (event.card : ℝ)/(mixed.card : ℝ)) Filter.atTop
        (nhds (Real.exp (-(τ/2)) * (τ/2)^j / (Nat.factorial j : ℝ))) := by
  intro r hr T D hT hD τ hτ hlim j
  let qf : ℕ → ℝ := fun k => (2 : ℝ) ^ (D k) - 1
  let Lf : ℕ → ℝ := fun k => 1 + Real.sqrt (qf k)
  let nf : ℕ → ℕ := fun k => 6 * T k
  have hqf_ge3 : ∀ k, 3 ≤ qf k := fun k => by
    dsimp only [qf]
    have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ (D k) := by
      calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
        _ ≤ (2 : ℝ) ^ (D k) := pow_le_pow_right₀ (by norm_num) (hD k)
    linarith
  have hLf_gt1 : ∀ k, 2 ≤ Lf k := fun k => by
    dsimp only [Lf]
    have hsq1 : 1 ≤ Real.sqrt (qf k) := by
      calc (1 : ℝ) = Real.sqrt (1 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
        _ ≤ Real.sqrt (qf k) := Real.sqrt_le_sqrt (by linarith [hqf_ge3 k])
    linarith
  have hLf_atTop : Filter.Tendsto Lf Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro B
    have hB' : ∃ M : ℝ, 0 < M ∧ B ≤ M := ⟨max B 1, by positivity, le_max_left _ _⟩
    rcases hB' with ⟨M, hM_pos, hBM⟩
    have hup : ∀ᶠ k in Filter.atTop, 6 * (T k : ℝ) / (Lf k) ^ (2 * r + 1) ≤ τ + 1 :=
      hlim.eventually (ge_mem_nhds (by linarith))
    have hT_big : ∀ᶠ k in Filter.atTop, (τ + 1) * M ^ (2 * r + 1) ≤ 6 * (T k : ℝ) := by
      have h1 : Filter.Tendsto (fun k => 6 * (T k : ℝ)) Filter.atTop Filter.atTop :=
        Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 6) (tendsto_natCast_atTop_atTop.comp hT)
      exact h1.eventually_ge_atTop _
    rcases (hup.and hT_big).exists_forall_of_atTop with ⟨K, hK⟩
    refine ⟨K, fun k hk => ?_⟩
    rcases hK k hk with ⟨h1, h2⟩
    have hL_pos : 0 < Lf k := by linarith [hLf_gt1 k]
    have hpow : M ^ (2 * r + 1) ≤ (Lf k) ^ (2 * r + 1) := by
      have hmul : 6 * (T k : ℝ) ≤ (τ + 1) * (Lf k) ^ (2 * r + 1) :=
        (div_le_iff₀ (pow_pos hL_pos _)).mp h1
      have hτ1 : 0 < τ + 1 := by linarith
      nlinarith
    have hML : M ≤ Lf k := by
      by_contra hlt; push_neg at hlt
      have := pow_lt_pow_left₀ hlt (le_of_lt hL_pos) (by omega : 2 * r + 1 ≠ 0)
      linarith
    linarith
  have hD_atTop : Filter.Tendsto D Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro B
    rcases (hLf_atTop.eventually_ge_atTop (1 + (2 : ℝ) ^ B)).exists_forall_of_atTop with ⟨K, hK⟩
    refine ⟨K, fun k hk => ?_⟩
    have h1 := hK k hk
    have hsq : (2 : ℝ) ^ B ≤ Real.sqrt (qf k) := by dsimp only [Lf] at h1; linarith
    have hq_ge : ((2 : ℝ) ^ B) ^ 2 ≤ qf k := by
      calc ((2 : ℝ) ^ B) ^ 2 ≤ (Real.sqrt (qf k)) ^ 2 := pow_le_pow_left₀ (by positivity) hsq 2
        _ = qf k := Real.sq_sqrt (by linarith [hqf_ge3 k])
    have h2ge : (2 : ℝ) ^ B ≤ (2 : ℝ) ^ (D k) := by
      have h1' : (2 : ℝ) ^ B ≤ ((2 : ℝ) ^ B) ^ 2 := by
        have hge1 : (1 : ℝ) ≤ (2 : ℝ) ^ B := one_le_pow₀ (by norm_num)
        nlinarith
      dsimp only [qf] at hq_ge; linarith
    by_contra hlt; push_neg at hlt
    have hlt2 : (2 : ℝ) ^ (D k) < (2 : ℝ) ^ B := pow_lt_pow_right₀ (by norm_num) hlt
    linarith
  have hnf_atTop : Filter.Tendsto nf Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro B
    rcases (hT.eventually_ge_atTop B).exists_forall_of_atTop with ⟨K, hK⟩
    exact ⟨K, fun k hk => by dsimp only [nf]; have := hK k hk; omega⟩
  have hnf_div_L : Filter.Tendsto (fun k => (nf k : ℝ) / Lf k) Filter.atTop Filter.atTop := by
    have hrew : ∀ k, (nf k : ℝ) / Lf k = (6 * (T k : ℝ) / (Lf k) ^ (2 * r + 1)) * (Lf k) ^ (2 * r) := fun k => by
      have hL_ne : Lf k ≠ 0 := by linarith [hLf_gt1 k]
      dsimp only [nf]; push_cast
      rw [show 2 * r + 1 = 2 * r + 1 from rfl, pow_succ]
      field_simp [hL_ne]
    simp_rw [hrew]
    have hpow_atTop : Filter.Tendsto (fun k => (Lf k) ^ (2 * r)) Filter.atTop Filter.atTop :=
      (tendsto_pow_atTop' (by omega : 2 * r ≠ 0)).comp hLf_atTop
    exact Filter.Tendsto.pos_mul_atTop hτ hlim hpow_atTop
  have hZ_lim : Filter.Tendsto (fun k =>
      (∑ S ∈ (Finset.univ : Finset (Finset (Fin (nf k)))).filter (fun S => S ≠ ∅ ∧ S ≠ Finset.univ),
        (qf k) ^ (exitsS (nf k) S).card) / (Lf k) ^ (nf k)) Filter.atTop (nhds 1) := by
    have hrew : ∀ᶠ k in Filter.atTop,
        (∑ S ∈ (Finset.univ : Finset (Finset (Fin (nf k)))).filter (fun S => S ≠ ∅ ∧ S ≠ Finset.univ),
          (qf k) ^ (exitsS (nf k) S).card) / (Lf k) ^ (nf k) =
        1 + ((1 - Real.sqrt (qf k)) / Lf k) ^ (nf k) - 2 / (Lf k) ^ (nf k) := by
      filter_upwards [hT.eventually_ge_atTop 1] with k hk
      have hn1 : 1 ≤ nf k := by dsimp only [nf]; omega
      rw [sum_W_proper (nf k) hn1 (qf k) (by linarith [hqf_ge3 k])]
      have hL_ne : (Lf k) ^ (nf k) ≠ 0 := pow_ne_zero _ (by linarith [hLf_gt1 k])
      rw [div_pow]; dsimp only [Lf] at hL_ne ⊢; field_simp [hL_ne]
    rw [Filter.tendsto_congr' hrew]
    have hterm1 : Filter.Tendsto (fun k => ((1 - Real.sqrt (qf k)) / Lf k) ^ (nf k)) Filter.atTop (nhds 0) := by
      refine squeeze_zero_norm' ?_ (tendsto_const_nhds.div_atTop hnf_div_L : Filter.Tendsto (fun k => (1 : ℝ) / ((nf k : ℝ) / Lf k)) _ _)
      filter_upwards [hLf_atTop.eventually_ge_atTop 6, hT.eventually_ge_atTop 1] with k hL6 hk1
      have hL_pos : 0 < Lf k := by linarith
      have hL_ne : Lf k ≠ 0 := ne_of_gt hL_pos
      have hsq5 : 5 ≤ Real.sqrt (qf k) := by dsimp only [Lf] at hL6; linarith
      have habs : |(1 - Real.sqrt (qf k)) / Lf k| = 1 - 2 / Lf k := by
        rw [abs_div, abs_of_pos hL_pos, abs_of_nonpos (by linarith)]
        field_simp [hL_ne]; dsimp only [Lf]; ring
      rw [Real.norm_eq_abs, abs_pow, habs]
      have hle_exp : (1 - 2 / Lf k) ^ (nf k) ≤ Real.exp (-(2 * (nf k : ℝ) / Lf k)) := by
        have h1 : 1 - 2 / Lf k ≤ Real.exp (-(2 / Lf k)) := by
          have := Real.add_one_le_exp (-(2 / Lf k)); linarith
        have hnn : 0 ≤ 1 - 2 / Lf k := by rw [sub_nonneg, div_le_one hL_pos]; linarith
        calc (1 - 2 / Lf k) ^ (nf k) ≤ (Real.exp (-(2 / Lf k))) ^ (nf k) := pow_le_pow_left₀ hnn h1 _
          _ = Real.exp ((nf k : ℝ) * (-(2 / Lf k))) := (Real.exp_nat_mul _ _).symm
          _ = Real.exp (-(2 * (nf k : ℝ) / Lf k)) := by congr 1; ring
      have hnf_pos : (0 : ℝ) < (nf k : ℝ) := by dsimp only [nf]; exact_mod_cast (show 0 < 6 * T k by omega)
      have hpos_x : 0 < 2 * (nf k : ℝ) / Lf k := by positivity
      have hexp := exp_neg_le_pow_div (2 * (nf k : ℝ) / Lf k) hpos_x 1 le_rfl
      rw [pow_one] at hexp
      have hhalf : (1 : ℝ) / (2 * (nf k : ℝ) / Lf k) ≤ 1 / ((nf k : ℝ) / Lf k) := by
        refine one_div_le_one_div_of_le (by positivity) ?_
        rw [mul_div_assoc]; linarith [show (0 : ℝ) < (nf k : ℝ) / Lf k by positivity]
      exact hle_exp.trans (hexp.trans hhalf)
    have hterm2 : Filter.Tendsto (fun k => 2 / (Lf k) ^ (nf k)) Filter.atTop (nhds 0) := by
      refine squeeze_zero' (Filter.Eventually.of_forall fun k => by have := hLf_gt1 k; positivity) ?_
        (tendsto_const_nhds.div_atTop hLf_atTop : Filter.Tendsto (fun k => (2 : ℝ) / Lf k) _ _)
      filter_upwards [hT.eventually_ge_atTop 1] with k hk
      have hne0 : nf k ≠ 0 := by dsimp only [nf]; omega
      exact div_le_div_of_nonneg_left (by norm_num) (by linarith [hLf_gt1 k])
        (le_self_pow₀ (by linarith [hLf_gt1 k]) hne0)
    simpa using (tendsto_const_nhds.add hterm1).sub hterm2
  have hmoment_lim : ∀ p : ℕ, 1 ≤ p →
      Filter.Tendsto (fun k =>
        (∑ S ∈ (Finset.univ : Finset (Finset (Fin (nf k)))).filter (fun S => S ≠ ∅ ∧ S ≠ Finset.univ),
          (Nat.choose (gapCount (nf k) r S) p : ℝ) * (qf k) ^ (exitsS (nf k) S).card) /
        (Lf k) ^ (nf k)) Filter.atTop (nhds ((τ / 2) ^ p / (Nat.factorial p : ℝ))) := by
    intro p hp
    let g := 2 * r + 2
    let Nf : ℕ → ℕ := fun k => nf k - p * (g + 1)
    have hNf_atTop : Filter.Tendsto Nf Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro B
      rcases (hnf_atTop.eventually_ge_atTop (B + p * (g + 1))).exists_forall_of_atTop with ⟨K, hK⟩
      exact ⟨K, fun k hk => by dsimp only [Nf]; have := hK k hk; omega⟩
    have hq_div_L2 : Filter.Tendsto (fun k => qf k / (2 * (Lf k) ^ 2)) Filter.atTop (nhds (1 / 2)) := by
      have hrew : ∀ k, qf k / (2 * (Lf k) ^ 2) = ((1 : ℝ) - 1 / Lf k) ^ 2 / 2 := fun k => by
        have hL_ne : Lf k ≠ 0 := by linarith [hLf_gt1 k]
        have hsq := Real.sq_sqrt (show 0 ≤ qf k by linarith [hqf_ge3 k])
        have hdiff : Real.sqrt (qf k) = Lf k - 1 := by dsimp only [Lf]; ring
        have hqeq : qf k = (Lf k - 1) ^ 2 := by rw [← hdiff, hsq]
        rw [hqeq]; field_simp [hL_ne]
      simp_rw [hrew]
      have hinv : Filter.Tendsto (fun k => 1 / Lf k) Filter.atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop hLf_atTop
      have h1 := (((tendsto_const_nhds (x := (1 : ℝ))).sub hinv).pow 2).div_const 2
      simpa using h1
    have hbase_lim : Filter.Tendsto (fun k =>
        (nf k : ℝ) * qf k / (2 * (Lf k) ^ (g + 1))) Filter.atTop (nhds (τ / 2)) := by
      have hrew : ∀ k, (nf k : ℝ) * qf k / (2 * (Lf k) ^ (g + 1)) =
          (6 * (T k : ℝ) / (Lf k) ^ (2 * r + 1)) * (qf k / (2 * (Lf k) ^ 2)) := fun k => by
        have hL_ne : Lf k ≠ 0 := by linarith [hLf_gt1 k]
        dsimp only [nf, g]; push_cast
        rw [show 2 * r + 2 + 1 = (2 * r + 1) + 2 by omega, pow_add]
        field_simp [hL_ne]
      simp_rw [hrew]
      have h1 := (hlim.mul hq_div_L2).congr (fun _ => rfl)
      rw [show τ * (1 / 2) = τ / 2 by ring] at h1
      exact h1
    have hNf_ratio : Filter.Tendsto (fun k => (Nf k : ℝ) / (nf k : ℝ)) Filter.atTop (nhds 1) := by
      have hrew : ∀ᶠ k in Filter.atTop, (Nf k : ℝ) / (nf k : ℝ) = 1 - ((p * (g + 1) : ℕ) : ℝ) / (nf k : ℝ) := by
        filter_upwards [hnf_atTop.eventually_ge_atTop (p * (g + 1) + 1)] with k hk
        have hpos : (0 : ℝ) < (nf k : ℝ) := by exact_mod_cast (show 0 < nf k by omega)
        dsimp only [Nf]
        rw [Nat.cast_sub (by omega), sub_div, div_self (ne_of_gt hpos)]
      rw [Filter.tendsto_congr' hrew]
      have h0 : Filter.Tendsto (fun k => ((p * (g + 1) : ℕ) : ℝ) / (nf k : ℝ)) Filter.atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hnf_atTop)
      simpa using tendsto_const_nhds.sub h0
    let mainTerm : ℕ → ℝ := fun k =>
      ((nf k : ℝ) / (p : ℝ)) * (qf k / (2 * (Lf k) ^ (g + 1))) ^ p *
        (Nat.choose (Nf k + p - 1) (p - 1) : ℝ)
    have hmain_lim : Filter.Tendsto mainTerm Filter.atTop (nhds ((τ / 2) ^ p / (Nat.factorial p : ℝ))) := by
      have hrew : ∀ᶠ k in Filter.atTop, mainTerm k =
          (1 / (p : ℝ)) * ((nf k : ℝ) * qf k / (2 * (Lf k) ^ (g + 1))) ^ p *
          ((Nf k : ℝ) / (nf k : ℝ)) ^ (p - 1) *
          ((Nat.choose (Nf k + (p - 1)) (p - 1) : ℝ) / ((Nf k : ℝ) ^ (p - 1))) := by
        filter_upwards [hNf_atTop.eventually_ge_atTop 1, hnf_atTop.eventually_ge_atTop 1] with k hN1 hn1
        have hN_ne : (Nf k : ℝ) ≠ 0 := by exact_mod_cast (show Nf k ≠ 0 by omega)
        have hn_ne : (nf k : ℝ) ≠ 0 := by exact_mod_cast (show nf k ≠ 0 by omega)
        have hL_ne : (Lf k) ^ (g + 1) ≠ 0 := pow_ne_zero _ (by linarith [hLf_gt1 k])
        have hp_ne : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
        dsimp only [mainTerm]
        rw [show Nf k + p - 1 = Nf k + (p - 1) by omega]
        simp only [div_pow, mul_pow]
        have hn_pow : (nf k : ℝ) ^ p = (nf k : ℝ) * (nf k : ℝ) ^ (p - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel hp]
        rw [hn_pow]
        field_simp [hN_ne, hn_ne, hL_ne, hp_ne]
      rw [Filter.tendsto_congr' hrew]
      have h1 := (((tendsto_const_nhds (x := 1 / (p : ℝ))).mul (hbase_lim.pow p)).mul (hNf_ratio.pow (p - 1))).mul
        (tendsto_choose_div_pow (p - 1) Nf hNf_atTop)
      have hlim_eq : (1 / (p : ℝ)) * (τ / 2) ^ p * (1 : ℝ) ^ (p - 1) * (1 / ((p - 1).factorial : ℝ)) =
          (τ / 2) ^ p / (Nat.factorial p : ℝ) := by
        have hfac : (Nat.factorial p : ℝ) = (p : ℝ) * ((p - 1).factorial : ℝ) := by
          have : Nat.factorial p = p * Nat.factorial (p - 1) := by
            conv_lhs => rw [← Nat.sub_add_cancel hp]
            rw [Nat.factorial_succ, Nat.sub_add_cancel hp]
          exact_mod_cast this
        rw [hfac, one_pow, mul_one]; ring
      rwa [hlim_eq] at h1
    have hdiff_zero : Filter.Tendsto (fun k =>
        (∑ S ∈ (Finset.univ : Finset (Finset (Fin (nf k)))).filter (fun S => S ≠ ∅ ∧ S ≠ Finset.univ),
          (Nat.choose (gapCount (nf k) r S) p : ℝ) * (qf k) ^ (exitsS (nf k) S).card) /
        (Lf k) ^ (nf k) - mainTerm k) Filter.atTop (nhds 0) := by
      let errB : ℕ → ℝ := fun k =>
        mainTerm k * (1 - 2 / Lf k) ^ (Nf k) +
        ∑ B ∈ (Finset.univ : Finset (Finset (Fin p))).filter (fun B => B ≠ ∅ ∧ B ≠ Finset.univ),
          (1 / (p : ℝ)) * ((nf k : ℝ) * qf k / (2 * (Lf k) ^ (g + 1))) ^ p *
            (((Nf k + 1 : ℕ) : ℝ) / (nf k : ℝ)) ^ (p - 1 - B.card) *
            (Lf k / (2 * (nf k : ℝ))) ^ B.card
      have herr_lim : Filter.Tendsto errB Filter.atTop (nhds 0) := by
        have hNf_div_L : Filter.Tendsto (fun k => (Nf k : ℝ) / Lf k) Filter.atTop Filter.atTop := by
          have hrew : ∀ k, (Nf k : ℝ) / Lf k = ((Nf k : ℝ) / (nf k : ℝ)) * ((nf k : ℝ) / Lf k) := fun k => by
            by_cases hn0 : nf k = 0
            · have : Nf k = 0 := by dsimp only [Nf]; omega
              simp [hn0, this]
            · have hn_ne : (nf k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
              field_simp [hn_ne]
          simp_rw [hrew]
          exact Filter.Tendsto.pos_mul_atTop zero_lt_one hNf_ratio hnf_div_L
        have hdelta_lim : Filter.Tendsto (fun k => (1 - 2 / Lf k) ^ (Nf k)) Filter.atTop (nhds 0) := by
          refine squeeze_zero' ?_ ?_ (tendsto_const_nhds.div_atTop hNf_div_L : Filter.Tendsto (fun k => (1 : ℝ) / ((Nf k : ℝ) / Lf k)) _ _)
          · filter_upwards [hLf_atTop.eventually_ge_atTop 6] with k hL6
            have hL_pos : 0 < Lf k := by linarith
            exact pow_nonneg (by rw [sub_nonneg, div_le_one hL_pos]; linarith) _
          · filter_upwards [hLf_atTop.eventually_ge_atTop 6, hNf_atTop.eventually_ge_atTop 1] with k hL6 hN1
            have hL_pos : 0 < Lf k := by linarith
            have hnn : 0 ≤ 1 - 2 / Lf k := by rw [sub_nonneg, div_le_one hL_pos]; linarith
            have h1 : (1 - 2 / Lf k) ^ (Nf k) ≤ Real.exp (-(2 * (Nf k : ℝ) / Lf k)) := by
              have h2 : 1 - 2 / Lf k ≤ Real.exp (-(2 / Lf k)) := by linarith [Real.add_one_le_exp (-(2 / Lf k))]
              calc _ ≤ (Real.exp (-(2 / Lf k))) ^ (Nf k) := pow_le_pow_left₀ hnn h2 _
                _ = Real.exp ((Nf k : ℝ) * (-(2 / Lf k))) := (Real.exp_nat_mul _ _).symm
                _ = Real.exp (-(2 * (Nf k : ℝ) / Lf k)) := by congr 1; ring
            have hN_pos : (0 : ℝ) < (Nf k : ℝ) := by exact_mod_cast hN1
            have hx_pos : 0 < 2 * (Nf k : ℝ) / Lf k := by positivity
            have hexp := exp_neg_le_pow_div (2 * (Nf k : ℝ) / Lf k) hx_pos 1 le_rfl
            rw [pow_one] at hexp
            have hle2 : (Nf k : ℝ) / Lf k ≤ 2 * (Nf k : ℝ) / Lf k := by
              have : 0 < (Nf k : ℝ) / Lf k := by positivity
              rw [mul_div_assoc]; linarith
            exact h1.trans (hexp.trans (one_div_le_one_div_of_le (by positivity) hle2))
        have hterm1 : Filter.Tendsto (fun k => mainTerm k * (1 - 2 / Lf k) ^ (Nf k)) Filter.atTop (nhds 0) := by
          simpa using hmain_lim.mul hdelta_lim
        have hterm2 : Filter.Tendsto (fun k =>
            ∑ B ∈ (Finset.univ : Finset (Finset (Fin p))).filter (fun B => B ≠ ∅ ∧ B ≠ Finset.univ),
              (1 / (p : ℝ)) * ((nf k : ℝ) * qf k / (2 * (Lf k) ^ (g + 1))) ^ p *
                (((Nf k + 1 : ℕ) : ℝ) / (nf k : ℝ)) ^ (p - 1 - B.card) *
                (Lf k / (2 * (nf k : ℝ))) ^ B.card) Filter.atTop (nhds 0) := by
          have hz : (0 : ℝ) = ∑ _B ∈ (Finset.univ : Finset (Finset (Fin p))).filter (fun B => B ≠ ∅ ∧ B ≠ Finset.univ), (0 : ℝ) := by simp
          rw [hz]
          refine tendsto_finset_sum' _ fun B hB => ?_
          have hB_pos : 1 ≤ B.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_filter.mp hB).2.1)
          have hN1_rat : Filter.Tendsto (fun k => ((Nf k + 1 : ℕ) : ℝ) / (nf k : ℝ)) Filter.atTop (nhds 1) := by
            have hrew : ∀ k, ((Nf k + 1 : ℕ) : ℝ) / (nf k : ℝ) = (Nf k : ℝ) / (nf k : ℝ) + 1 / (nf k : ℝ) := fun k => by
              push_cast; rw [add_div]
            simp_rw [hrew]
            have h1 := (hNf_ratio.add ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop (tendsto_natCast_atTop_atTop.comp hnf_atTop))).congr (fun _ => rfl)
            rw [add_zero] at h1; exact h1
          have hL2n : Filter.Tendsto (fun k => Lf k / (2 * (nf k : ℝ))) Filter.atTop (nhds 0) := by
            have hrew : ∀ k, Lf k / (2 * (nf k : ℝ)) = (1 / 2) / ((nf k : ℝ) / Lf k) := fun k => by
              by_cases hn0 : nf k = 0
              · simp [hn0]
              · have hn_ne : (nf k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
                have hL_ne : Lf k ≠ 0 := by linarith [hLf_gt1 k]
                field_simp [hn_ne, hL_ne]
            simp_rw [hrew]
            exact tendsto_const_nhds.div_atTop hnf_div_L
          have hpow0 : Filter.Tendsto (fun k => (Lf k / (2 * (nf k : ℝ))) ^ B.card) Filter.atTop (nhds 0) := by
            simpa [zero_pow (show B.card ≠ 0 by omega)] using hL2n.pow B.card
          simpa using ((tendsto_const_nhds.mul (hbase_lim.pow p)).mul (hN1_rat.pow (p - 1 - B.card))).mul hpow0
        have hsum := (hterm1.add hterm2).congr (fun _ => rfl)
        rw [add_zero] at hsum
        exact hsum
      refine squeeze_zero_norm' ?_ herr_lim
      filter_upwards [hLf_atTop.eventually_ge_atTop 6, hnf_atTop.eventually_ge_atTop (p * (g + 1) + 1)] with k hL6 hnbig
      have hq4 : 4 ≤ qf k := by
        have hsq5 : 5 ≤ Real.sqrt (qf k) := by dsimp only [Lf] at hL6; linarith
        have := Real.mul_self_sqrt (show 0 ≤ qf k by linarith [hqf_ge3 k])
        nlinarith
      have hsum_prop_eq : ∑ S ∈ (Finset.univ : Finset (Finset (Fin (nf k)))).filter (fun S => S ≠ ∅ ∧ S ≠ Finset.univ),
            (Nat.choose (gapCount (nf k) r S) p : ℝ) * (qf k) ^ (exitsS (nf k) S).card =
          ∑ S : Finset (Fin (nf k)), (Nat.choose (gapCount (nf k) r S) p : ℝ) * (qf k) ^ (exitsS (nf k) S).card := by
        refine (Finset.sum_subset (Finset.filter_subset _ _) fun S _ hnot => ?_)
        have h0 : gapCount (nf k) r S = 0 := by
          have hor : S = ∅ ∨ S = Finset.univ := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_not] at hnot; exact hnot
          have hex0 : exitsS (nf k) S = ∅ := by
            rcases hor with rfl | rfl <;> (ext a; simp [exitsS])
          dsimp only [gapCount]; rw [hex0]; simp
        rw [h0, Nat.choose_eq_zero_of_lt (by omega)]; simp
      have hpg_eq : p * (g + 1) = p * (2 * r + 3) := by dsimp only [g]
      have hNf_eq : Nf k = nf k - p * (2 * r + 3) := by dsimp only [Nf, g]
      have hexact := sum_choose_gapCount_exact (nf k) r p hr hp (by omega) (qf k) (by linarith)
      rw [← hsum_prop_eq, ← hNf_eq] at hexact
      have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
      have hL_pos : 0 < Lf k := by linarith
      have hLn_pos : 0 < (Lf k) ^ (nf k) := pow_pos hL_pos _
      have hLHS_eq : (∑ S ∈ (Finset.univ : Finset (Finset (Fin (nf k)))).filter (fun S => S ≠ ∅ ∧ S ≠ Finset.univ),
            (Nat.choose (gapCount (nf k) r S) p : ℝ) * (qf k) ^ (exitsS (nf k) S).card) / (Lf k) ^ (nf k) =
          ((nf k : ℝ) * (qf k) ^ p / ((p : ℝ) * (Lf k) ^ (nf k))) *
            ∑ ℓ ∈ compFin p (Nf k), ∏ u : Fin p, mat2Pow (qf k) (ℓ u) true true := by
        have h1 : ∑ S ∈ (Finset.univ : Finset (Finset (Fin (nf k)))).filter (fun S => S ≠ ∅ ∧ S ≠ Finset.univ),
              (Nat.choose (gapCount (nf k) r S) p : ℝ) * (qf k) ^ (exitsS (nf k) S).card =
            ((nf k : ℝ) * (qf k) ^ p / (p : ℝ)) *
              ∑ ℓ ∈ compFin p (Nf k), ∏ u : Fin p, mat2Pow (qf k) (ℓ u) true true := by
          rw [div_mul_eq_mul_div, eq_div_iff (ne_of_gt hp_pos), mul_comm _ (p : ℝ)]; exact hexact
        rw [h1]; ring
      have hmain_rew : mainTerm k =
          ((nf k : ℝ) * (qf k) ^ p / ((p : ℝ) * (Lf k) ^ (nf k))) *
            ((Nat.choose (Nf k + p - 1) (p - 1) : ℝ) * (Lf k) ^ (Nf k) / (2 : ℝ) ^ p) := by
        dsimp only [mainTerm]
        have hpow_n : (Lf k) ^ (nf k) = (Lf k) ^ (Nf k) * ((Lf k) ^ (g + 1)) ^ p := by
          rw [← pow_mul, ← pow_add, show Nf k + (g + 1) * p = nf k by rw [mul_comm (g + 1) p]; dsimp only [Nf]; omega]
        rw [hpow_n, div_pow, mul_pow]
        have h1 : (Lf k) ^ (Nf k) ≠ 0 := pow_ne_zero _ (ne_of_gt hL_pos)
        have h2 : ((Lf k) ^ (g + 1)) ^ p ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (ne_of_gt hL_pos))
        field_simp [ne_of_gt hp_pos, h1, h2]
      rw [Real.norm_eq_abs, hLHS_eq, hmain_rew, ← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
      have happ := sum_prod_mat2Pow_approx p (Nf k) hp (qf k) hq4
      refine (mul_le_mul_of_nonneg_left happ (by positivity)).trans (le_of_eq ?_)
      have hfactor : ((nf k : ℝ) * (qf k) ^ p / ((p : ℝ) * (Lf k) ^ (nf k))) * ((Lf k) ^ (Nf k) / (2 : ℝ) ^ p) =
          ((nf k : ℝ) / (p : ℝ)) * (qf k / (2 * (Lf k) ^ (g + 1))) ^ p := by
        have hpow_n : (Lf k) ^ (nf k) = (Lf k) ^ (Nf k) * ((Lf k) ^ (g + 1)) ^ p := by
          rw [← pow_mul, ← pow_add, show Nf k + (g + 1) * p = nf k by rw [mul_comm (g + 1) p]; dsimp only [Nf]; omega]
        rw [hpow_n, div_pow, mul_pow]
        have h1 : (Lf k) ^ (Nf k) ≠ 0 := pow_ne_zero _ (ne_of_gt hL_pos)
        have h2 : ((Lf k) ^ (g + 1)) ^ p ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (ne_of_gt hL_pos))
        field_simp [ne_of_gt hp_pos, h1, h2]
      rw [← mul_assoc, hfactor, mul_add, Finset.mul_sum]
      dsimp only [errB]
      congr 1
      · dsimp only [mainTerm]; ring
      · refine Finset.sum_congr rfl fun B hB => ?_
        have hB_le : B.card ≤ p - 1 := by
          have hlt : B.card < p := by
            have := Finset.card_lt_card (ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ B, (Finset.mem_filter.mp hB).2.2⟩)
            rwa [Finset.card_univ, Fintype.card_fin] at this
          omega
        have hn_ne : (nf k : ℝ) ≠ 0 := by exact_mod_cast (show nf k ≠ 0 by omega)
        have hL_ne : (Lf k) ^ (g + 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hL_pos)
        push_cast
        have hpow_n : (nf k : ℝ) ^ p = (nf k : ℝ) * (nf k : ℝ) ^ (p - 1 - B.card) * (nf k : ℝ) ^ B.card := by
          rw [← pow_succ', ← pow_add, show p - 1 - B.card + 1 + B.card = p by omega]
        dsimp only [Lf] at hL_ne ⊢
        simp only [div_pow, mul_pow]
        rw [hpow_n]
        field_simp [ne_of_gt hp_pos, hn_ne, hL_ne]
        try ring
    have hsum := hmain_lim.add hdiff_zero
    simpa [add_sub_cancel] using hsum
  have hEW_lim : Filter.Tendsto (fun k =>
      (∑ S ∈ (Finset.univ : Finset (Finset (Fin (nf k)))).filter (fun S => S ≠ ∅ ∧ S ≠ Finset.univ),
        if gapCount (nf k) r S = j then (qf k) ^ (exitsS (nf k) S).card else 0) / (Lf k) ^ (nf k))
      Filter.atTop (nhds (Real.exp (-(τ / 2)) * (τ / 2) ^ j / (Nat.factorial j : ℝ))) := by
    have hseries : Filter.Tendsto (fun K : ℕ =>
        (τ / 2) ^ j / (Nat.factorial j : ℝ) * ∑ m ∈ Finset.range K, (-(τ / 2)) ^ m / (Nat.factorial m : ℝ))
        Filter.atTop (nhds (Real.exp (-(τ / 2)) * (τ / 2) ^ j / (Nat.factorial j : ℝ))) := by
      have hhas : HasSum (fun m : ℕ => (-(τ / 2)) ^ m / (Nat.factorial m : ℝ)) (Real.exp (-(τ / 2))) := by
        rw [Real.exp_eq_exp_ℝ]
        simpa using NormedSpace.expSeries_div_hasSum_exp (-(τ / 2))
      have hlim_s := ((tendsto_const_nhds (x := (τ / 2) ^ j / (Nat.factorial j : ℝ))).mul hhas.tendsto_sum_nat).congr (fun _ => rfl)
      rw [show (τ / 2) ^ j / (Nat.factorial j : ℝ) * Real.exp (-(τ / 2)) =
        Real.exp (-(τ / 2)) * (τ / 2) ^ j / (Nat.factorial j : ℝ) by ring] at hlim_s
      exact hlim_s
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hhalf_pos : 0 < ε / 2 := half_pos hε
    rcases (Metric.tendsto_atTop.mp hseries (ε / 2) hhalf_pos) with ⟨K0, hK0⟩
    let M := K0
    let loLim := (τ / 2) ^ j / (Nat.factorial j : ℝ) *
      ∑ m ∈ Finset.range (2 * M + 2), (-(τ / 2)) ^ m / (Nat.factorial m : ℝ)
    let hiLim := (τ / 2) ^ j / (Nat.factorial j : ℝ) *
      ∑ m ∈ Finset.range (2 * M + 1), (-(τ / 2)) ^ m / (Nat.factorial m : ℝ)
    have hlo_close : |loLim - Real.exp (-(τ / 2)) * (τ / 2) ^ j / (Nat.factorial j : ℝ)| < ε / 2 := by
      simpa [Real.dist_eq, loLim] using hK0 (2 * M + 2) (by omega)
    have hhi_close : |hiLim - Real.exp (-(τ / 2)) * (τ / 2) ^ j / (Nat.factorial j : ℝ)| < ε / 2 := by
      simpa [Real.dist_eq, hiLim] using hK0 (2 * M + 1) (by omega)
    have hbonf_lim : ∀ K : ℕ,
        Filter.Tendsto (fun k =>
          ∑ m ∈ Finset.range K, (-1 : ℝ) ^ m * (Nat.choose (j + m) j : ℝ) *
            ((∑ S ∈ (Finset.univ : Finset (Finset (Fin (nf k)))).filter (fun S => S ≠ ∅ ∧ S ≠ Finset.univ),
              (Nat.choose (gapCount (nf k) r S) (j + m) : ℝ) * (qf k) ^ (exitsS (nf k) S).card) /
             (Lf k) ^ (nf k)))
        Filter.atTop (nhds ((τ / 2) ^ j / (Nat.factorial j : ℝ) *
          ∑ m ∈ Finset.range K, (-(τ / 2)) ^ m / (Nat.factorial m : ℝ))) := by
      intro K
      rw [Finset.mul_sum]
      refine tendsto_finset_sum' _ fun m _ => ?_
      have hterm_lim : Filter.Tendsto (fun k =>
          (∑ S ∈ (Finset.univ : Finset (Finset (Fin (nf k)))).filter (fun S => S ≠ ∅ ∧ S ≠ Finset.univ),
            (Nat.choose (gapCount (nf k) r S) (j + m) : ℝ) * (qf k) ^ (exitsS (nf k) S).card) /
          (Lf k) ^ (nf k)) Filter.atTop (nhds ((τ / 2) ^ (j + m) / (Nat.factorial (j + m) : ℝ))) := by
        by_cases hjm : j + m = 0
        · rw [hjm]; simp [hZ_lim]
        · exact hmoment_lim (j + m) (by omega)
      have h1 := ((tendsto_const_nhds (x := (-1 : ℝ) ^ m * (Nat.choose (j + m) j : ℝ))).mul hterm_lim).congr (fun _ => rfl)
      have heq_val : (-1 : ℝ) ^ m * (Nat.choose (j + m) j : ℝ) *
            ((τ / 2) ^ (j + m) / (Nat.factorial (j + m) : ℝ)) =
          (τ / 2) ^ j / (Nat.factorial j : ℝ) * ((-(τ / 2)) ^ m / (Nat.factorial m : ℝ)) := by
        have hch_nat := Nat.choose_mul_factorial_mul_factorial (show j ≤ j + m by omega)
        rw [show j + m - j = m by omega] at hch_nat
        have hch_r : (Nat.choose (j + m) j : ℝ) * (Nat.factorial j : ℝ) * (Nat.factorial m : ℝ) =
            (Nat.factorial (j + m) : ℝ) := by exact_mod_cast hch_nat
        have hf1 : (Nat.factorial j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
        have hf2 : (Nat.factorial m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
        have hch_ne : (Nat.choose (j + m) j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (Nat.choose_pos (by omega)))
        rw [← hch_r, pow_add, show (-(τ / 2)) ^ m = (-1 : ℝ) ^ m * (τ / 2) ^ m by rw [← mul_pow]; ring]
        field_simp [hf1, hf2, hch_ne]
        try ring
      rwa [heq_val] at h1
    have hlo_ev := (Metric.tendsto_atTop.mp (hbonf_lim (2 * M + 2)) (ε / 2) hhalf_pos)
    have hhi_ev := (Metric.tendsto_atTop.mp (hbonf_lim (2 * M + 1)) (ε / 2) hhalf_pos)
    rcases hlo_ev with ⟨K1, hK1⟩
    rcases hhi_ev with ⟨K2, hK2⟩
    refine ⟨max K1 K2, fun k hk => ?_⟩
    have h1 := hK1 k (le_trans (le_max_left _ _) hk)
    have h2 := hK2 k (le_trans (le_max_right _ _) hk)
    rw [Real.dist_eq] at h1 h2 ⊢
    have hLn_pos : 0 < (Lf k) ^ (nf k) := pow_pos (by linarith [hLf_gt1 k]) _
    have hsand_lo : (∑ m ∈ Finset.range (2 * M + 2), (-1 : ℝ) ^ m * (Nat.choose (j + m) j : ℝ) *
        ((∑ S ∈ (Finset.univ : Finset (Finset (Fin (nf k)))).filter (fun S => S ≠ ∅ ∧ S ≠ Finset.univ),
          (Nat.choose (gapCount (nf k) r S) (j + m) : ℝ) * (qf k) ^ (exitsS (nf k) S).card) /
         (Lf k) ^ (nf k))) ≤
        (∑ S ∈ (Finset.univ : Finset (Finset (Fin (nf k)))).filter (fun S => S ≠ ∅ ∧ S ≠ Finset.univ),
          if gapCount (nf k) r S = j then (qf k) ^ (exitsS (nf k) S).card else 0) / (Lf k) ^ (nf k) := by
      have hrew : ∑ m ∈ Finset.range (2 * M + 2), (-1 : ℝ) ^ m * (Nat.choose (j + m) j : ℝ) *
          ((∑ S ∈ (Finset.univ : Finset (Finset (Fin (nf k)))).filter (fun S => S ≠ ∅ ∧ S ≠ Finset.univ),
            (Nat.choose (gapCount (nf k) r S) (j + m) : ℝ) * (qf k) ^ (exitsS (nf k) S).card) /
           (Lf k) ^ (nf k)) =
          (∑ S ∈ (Finset.univ : Finset (Finset (Fin (nf k)))).filter (fun S => S ≠ ∅ ∧ S ≠ Finset.univ),
            (∑ m ∈ Finset.range (2 * M + 2), (-1 : ℝ) ^ m * (Nat.choose (j + m) j : ℝ) *
              (Nat.choose (gapCount (nf k) r S) (j + m) : ℝ)) * (qf k) ^ (exitsS (nf k) S).card) /
           (Lf k) ^ (nf k) := by
        rw [Finset.sum_div]
        simp_rw [Finset.sum_div, Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun S _ => by ring
      rw [hrew]
      refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun S _ => ?_) (le_of_lt hLn_pos)
      have hb := (bonferroni_bounds (gapCount (nf k) r S) j M).1
      have hq_nn : 0 ≤ (qf k) ^ (exitsS (nf k) S).card := pow_nonneg (by linarith [hqf_ge3 k]) _
      have hm := mul_le_mul_of_nonneg_right hb hq_nn
      split_ifs at hm ⊢ <;> simpa using hm
    have hsand_hi : (∑ S ∈ (Finset.univ : Finset (Finset (Fin (nf k)))).filter (fun S => S ≠ ∅ ∧ S ≠ Finset.univ),
          if gapCount (nf k) r S = j then (qf k) ^ (exitsS (nf k) S).card else 0) / (Lf k) ^ (nf k) ≤
        ∑ m ∈ Finset.range (2 * M + 1), (-1 : ℝ) ^ m * (Nat.choose (j + m) j : ℝ) *
          ((∑ S ∈ (Finset.univ : Finset (Finset (Fin (nf k)))).filter (fun S => S ≠ ∅ ∧ S ≠ Finset.univ),
            (Nat.choose (gapCount (nf k) r S) (j + m) : ℝ) * (qf k) ^ (exitsS (nf k) S).card) /
           (Lf k) ^ (nf k)) := by
      have hrew : ∑ m ∈ Finset.range (2 * M + 1), (-1 : ℝ) ^ m * (Nat.choose (j + m) j : ℝ) *
          ((∑ S ∈ (Finset.univ : Finset (Finset (Fin (nf k)))).filter (fun S => S ≠ ∅ ∧ S ≠ Finset.univ),
            (Nat.choose (gapCount (nf k) r S) (j + m) : ℝ) * (qf k) ^ (exitsS (nf k) S).card) /
           (Lf k) ^ (nf k)) =
          (∑ S ∈ (Finset.univ : Finset (Finset (Fin (nf k)))).filter (fun S => S ≠ ∅ ∧ S ≠ Finset.univ),
            (∑ m ∈ Finset.range (2 * M + 1), (-1 : ℝ) ^ m * (Nat.choose (j + m) j : ℝ) *
              (Nat.choose (gapCount (nf k) r S) (j + m) : ℝ)) * (qf k) ^ (exitsS (nf k) S).card) /
           (Lf k) ^ (nf k) := by
        rw [Finset.sum_div]
        simp_rw [Finset.sum_div, Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun S _ => by ring
      rw [hrew]
      refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun S _ => ?_) (le_of_lt hLn_pos)
      have hb := (bonferroni_bounds (gapCount (nf k) r S) j M).2
      have hq_nn : 0 ≤ (qf k) ^ (exitsS (nf k) S).card := pow_nonneg (by linarith [hqf_ge3 k]) _
      have hm := mul_le_mul_of_nonneg_right hb hq_nn
      split_ifs at hm ⊢ <;> simpa using hm
    rw [abs_lt] at h1 h2 hlo_close hhi_close ⊢
    constructor <;> linarith
  have htail_zero : Filter.Tendsto (fun k =>
      ((1024 / (2 : ℝ) ^ (6 * D k) + 1 / (2 : ℝ) ^ (D k)) *
        (∑ S ∈ (Finset.univ : Finset (Finset (Fin (nf k)))).filter (fun S => S ≠ ∅ ∧ S ≠ Finset.univ),
          (qf k) ^ (exitsS (nf k) S).card) +
       (2 * (2 : ℝ) ^ (4 * D k) * (4 : ℝ) ^ (6 * D k) * ((3 / 4 : ℝ) * Lf k) ^ (nf k) +
        15 * (2 : ℝ) ^ (4 * D k) * (Lf k) ^ 11 * (1 - 1 / (2 * Lf k)) ^ (T k) * (Lf k) ^ (nf k) +
        4 * (nf k : ℝ) * Real.sqrt (qf k) * (Lf k) ^ (nf k - (2 * r + 4))) +
       (2 * (4 : ℝ) ^ (6 * D k) * ((3 / 4 : ℝ) * Lf k) ^ (nf k) +
        15 * (Lf k) ^ 11 * (1 - 1 / (2 * Lf k)) ^ (T k) * (Lf k) ^ (nf k) +
        (nf k : ℝ) * Real.sqrt (qf k) * (Lf k) ^ (nf k - (2 * r + 4)))) /
      (Lf k) ^ (nf k)) Filter.atTop (nhds 0) := by
    have h2d_le : ∀ k, (2 : ℝ) ^ (D k) ≤ 2 * (Lf k) ^ 2 := fun k => by
      have hq3 := hqf_ge3 k
      have hsq := Real.sq_sqrt (show 0 ≤ qf k by linarith)
      have hL_ge : Real.sqrt (qf k) ≤ Lf k := by dsimp only [Lf]; linarith
      have hq_le : qf k ≤ (Lf k) ^ 2 := by
        calc qf k = (Real.sqrt (qf k)) ^ 2 := hsq.symm
          _ ≤ (Lf k) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hL_ge 2
      dsimp only [qf] at hq3 hq_le; linarith
    have heps_lim : Filter.Tendsto (fun k => 1024 / (2 : ℝ) ^ (6 * D k) + 1 / (2 : ℝ) ^ (D k)) Filter.atTop (nhds 0) := by
      have h2_atTop : Filter.Tendsto (fun k => (2 : ℝ) ^ (D k)) Filter.atTop Filter.atTop :=
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp hD_atTop
      have h26_atTop : Filter.Tendsto (fun k => (2 : ℝ) ^ (6 * D k)) Filter.atTop Filter.atTop :=
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
          (Filter.tendsto_atTop_atTop.mpr fun B => by rcases (hD_atTop.eventually_ge_atTop B).exists_forall_of_atTop with ⟨K, hK⟩; exact ⟨K, fun k hk => by have := hK k hk; omega⟩)
      have h1 := (tendsto_const_nhds (x := (1024 : ℝ))).div_atTop h26_atTop
      have h2 := (tendsto_const_nhds (x := (1 : ℝ))).div_atTop h2_atTop
      have h12 := (h1.add h2).congr (fun _ => rfl)
      rw [add_zero] at h12
      exact h12
    have h1_lim : Filter.Tendsto (fun k =>
        4 * (2 : ℝ) ^ (16 * D k) * ((3 / 4 : ℝ) ^ (nf k))) Filter.atTop (nhds 0) := by
      have hbound : Filter.Tendsto (fun k => (4 * (2 : ℝ) ^ 16 * (48 : ℝ) ^ 12) / ((τ / 2) ^ 12 * (Lf k) ^ 4))
          Filter.atTop (nhds 0) := by
        refine tendsto_const_nhds.div_atTop ?_
        exact Filter.Tendsto.const_mul_atTop (by positivity) ((tendsto_pow_atTop' (by omega : 4 ≠ 0)).comp hLf_atTop)
      refine squeeze_zero' (Filter.Eventually.of_forall fun _ => by positivity) ?_ hbound
      filter_upwards [hlim.eventually (le_mem_nhds (show τ / 2 < τ by linarith)), hLf_atTop.eventually_ge_atTop 2] with k hkτ hL2
      have hL_pos : 0 < Lf k := by linarith
      have h16 : (2 : ℝ) ^ (16 * D k) ≤ (2 : ℝ) ^ 16 * (Lf k) ^ 32 := by
        calc (2 : ℝ) ^ (16 * D k) = ((2 : ℝ) ^ (D k)) ^ 16 := by rw [mul_comm, pow_mul]
          _ ≤ (2 * (Lf k) ^ 2) ^ 16 := pow_le_pow_left₀ (by positivity) (h2d_le k) 16
          _ = (2 : ℝ) ^ 16 * (Lf k) ^ 32 := by rw [mul_pow, ← pow_mul]
      have hn_ge : (τ / 2) * (Lf k) ^ 3 ≤ (nf k : ℝ) := by
        have h1 : (τ / 2) * (Lf k) ^ (2 * r + 1) ≤ 6 * (T k : ℝ) :=
          (le_div_iff₀ (pow_pos hL_pos _)).mp hkτ
        have h2 : (Lf k) ^ 3 ≤ (Lf k) ^ (2 * r + 1) := pow_le_pow_right₀ (by linarith) (by omega)
        dsimp only [nf]; push_cast; nlinarith
      have hn_pos : 0 < (nf k : ℝ) := by nlinarith [pow_pos hL_pos 3]
      have h34 : (3 / 4 : ℝ) ^ (nf k) ≤ (48 / (nf k : ℝ)) ^ 12 := by
        have hle1 : (3 / 4 : ℝ) ^ (nf k) ≤ Real.exp (-((nf k : ℝ) / 4)) := by
          have h0 : (3 / 4 : ℝ) ≤ Real.exp (-(1 / 4 : ℝ)) := by linarith [Real.add_one_le_exp (-(1 / 4 : ℝ))]
          calc _ ≤ (Real.exp (-(1 / 4 : ℝ))) ^ (nf k) := pow_le_pow_left₀ (by norm_num) h0 _
            _ = Real.exp ((nf k : ℝ) * (-(1 / 4 : ℝ))) := (Real.exp_nat_mul _ _).symm
            _ = Real.exp (-((nf k : ℝ) / 4)) := by congr 1; ring
        have hexp := exp_neg_le_pow_div ((nf k : ℝ) / 4) (by positivity) 12 (by omega)
        push_cast at hexp
        have heq : (12 : ℝ) / ((nf k : ℝ) / 4) = 48 / (nf k : ℝ) := by field_simp [ne_of_gt hn_pos]; ring
        rw [heq] at hexp
        exact hle1.trans hexp
      have hdiv : (48 / (nf k : ℝ)) ^ 12 ≤ (48 : ℝ) ^ 12 / ((τ / 2) ^ 12 * (Lf k) ^ 36) := by
        rw [div_pow]
        refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
        calc (τ / 2) ^ 12 * (Lf k) ^ 36 = ((τ / 2) * (Lf k) ^ 3) ^ 12 := by rw [mul_pow, ← pow_mul]
          _ ≤ (nf k : ℝ) ^ 12 := pow_le_pow_left₀ (by positivity) hn_ge 12
      calc 4 * (2 : ℝ) ^ (16 * D k) * (3 / 4 : ℝ) ^ (nf k)
          ≤ 4 * ((2 : ℝ) ^ 16 * (Lf k) ^ 32) * ((48 : ℝ) ^ 12 / ((τ / 2) ^ 12 * (Lf k) ^ 36)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h16 (by norm_num)) (h34.trans hdiv) (by positivity) (by positivity)
        _ = (4 * (2 : ℝ) ^ 16 * (48 : ℝ) ^ 12) / ((τ / 2) ^ 12 * (Lf k) ^ 4) := by
            have hL_ne : Lf k ≠ 0 := ne_of_gt hL_pos
            have hτ_ne : (τ / 2) ^ 12 ≠ 0 := pow_ne_zero _ (by linarith)
            rw [show (Lf k) ^ 36 = (Lf k) ^ 32 * (Lf k) ^ 4 by rw [← pow_add]]
            field_simp [hL_ne, hτ_ne]
    have h2_lim : Filter.Tendsto (fun k =>
        30 * (2 : ℝ) ^ (4 * D k) * (Lf k) ^ 11 * (1 - 1 / (2 * Lf k)) ^ (T k)) Filter.atTop (nhds 0) := by
      have hbound : Filter.Tendsto (fun k => (30 * 16 * (240 : ℝ) ^ 10) / (τ ^ 10 * Lf k)) Filter.atTop (nhds 0) := by
        refine tendsto_const_nhds.div_atTop ?_
        exact Filter.Tendsto.const_mul_atTop (by positivity) hLf_atTop
      refine squeeze_zero' ?_ ?_ hbound
      · filter_upwards [hLf_atTop.eventually_ge_atTop 2] with k hL2
        have hnn : 0 ≤ 1 - 1 / (2 * Lf k) := by rw [sub_nonneg, div_le_one (by linarith)]; linarith
        positivity
      · filter_upwards [hlim.eventually (le_mem_nhds (show τ / 2 < τ by linarith)), hLf_atTop.eventually_ge_atTop 2] with k hkτ hL2
        have hL_pos : 0 < Lf k := by linarith
        have h4d : (2 : ℝ) ^ (4 * D k) ≤ 16 * (Lf k) ^ 8 := by
          calc (2 : ℝ) ^ (4 * D k) = ((2 : ℝ) ^ (D k)) ^ 4 := by rw [mul_comm, pow_mul]
            _ ≤ (2 * (Lf k) ^ 2) ^ 4 := pow_le_pow_left₀ (by positivity) (h2d_le k) 4
            _ = 16 * (Lf k) ^ 8 := by rw [mul_pow, ← pow_mul]; norm_num
        have ht_ge : (τ / 24) * (Lf k) ^ 2 ≤ (T k : ℝ) / (2 * Lf k) := by
          have h1 : (τ / 2) * (Lf k) ^ (2 * r + 1) ≤ 6 * (T k : ℝ) :=
            (le_div_iff₀ (pow_pos hL_pos _)).mp hkτ
          have h2 : (Lf k) ^ 3 ≤ (Lf k) ^ (2 * r + 1) := pow_le_pow_right₀ (by linarith) (by omega)
          have h3 : (τ / 2) * (Lf k) ^ 3 ≤ 6 * (T k : ℝ) := le_trans (mul_le_mul_of_nonneg_left h2 (by positivity)) h1
          rw [le_div_iff₀ (by positivity)]
          nlinarith
        have hx_pos : 0 < (T k : ℝ) / (2 * Lf k) := by
          have : 0 < (τ / 24) * (Lf k) ^ 2 := by positivity
          linarith
        have hnn : 0 ≤ 1 - 1 / (2 * Lf k) := by rw [sub_nonneg, div_le_one (by linarith)]; linarith
        have hexp1 : (1 - 1 / (2 * Lf k)) ^ (T k) ≤ Real.exp (-((T k : ℝ) / (2 * Lf k))) := by
          have h0 : 1 - 1 / (2 * Lf k) ≤ Real.exp (-(1 / (2 * Lf k))) := by linarith [Real.add_one_le_exp (-(1 / (2 * Lf k)))]
          calc _ ≤ (Real.exp (-(1 / (2 * Lf k)))) ^ (T k) := pow_le_pow_left₀ hnn h0 _
            _ = Real.exp ((T k : ℝ) * (-(1 / (2 * Lf k)))) := (Real.exp_nat_mul _ _).symm
            _ = Real.exp (-((T k : ℝ) / (2 * Lf k))) := by congr 1; ring
        have hexp2 := exp_neg_le_pow_div ((T k : ℝ) / (2 * Lf k)) hx_pos 10 (by omega)
        push_cast at hexp2
        have hdiv : ((10 : ℝ) / ((T k : ℝ) / (2 * Lf k))) ^ 10 ≤ (240 : ℝ) ^ 10 / (τ ^ 10 * (Lf k) ^ 20) := by
          rw [div_pow]
          have h10 : (10 : ℝ) / ((T k : ℝ) / (2 * Lf k)) ≤ 240 / (τ * (Lf k) ^ 2) := by
            have hrew : 240 / (τ * (Lf k) ^ 2) = 10 / ((τ / 24) * (Lf k) ^ 2) := by
              have hL_ne : Lf k ≠ 0 := ne_of_gt hL_pos
              have hτ_ne : τ ≠ 0 := ne_of_gt hτ
              field_simp [hL_ne, hτ_ne]; ring
            rw [hrew]
            exact div_le_div_of_nonneg_left (by norm_num) (by positivity) ht_ge
          have h10p := pow_le_pow_left₀ (by positivity) h10 10
          conv_lhs at h10p => rw [div_pow]
          conv_rhs at h10p => rw [div_pow, mul_pow, ← pow_mul]
          exact h10p
        calc 30 * (2 : ℝ) ^ (4 * D k) * (Lf k) ^ 11 * (1 - 1 / (2 * Lf k)) ^ (T k)
            ≤ 30 * (16 * (Lf k) ^ 8) * (Lf k) ^ 11 * ((240 : ℝ) ^ 10 / (τ ^ 10 * (Lf k) ^ 20)) := by
              refine mul_le_mul ?_ (hexp1.trans (hexp2.trans hdiv)) (by positivity) (by positivity)
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4d (by norm_num)) (by positivity)
          _ = (30 * 16 * (240 : ℝ) ^ 10) / (τ ^ 10 * Lf k) := by
              have hL_ne : Lf k ≠ 0 := ne_of_gt hL_pos
              have hτ_ne : τ ^ 10 ≠ 0 := pow_ne_zero _ (ne_of_gt hτ)
              rw [show (Lf k) ^ 20 = (Lf k) ^ 8 * (Lf k) ^ 11 * Lf k by rw [← pow_add, ← pow_succ]]
              field_simp [hL_ne, hτ_ne]
    have h3_lim : Filter.Tendsto (fun k =>
        5 * (nf k : ℝ) * Real.sqrt (qf k) / (Lf k) ^ (2 * r + 4)) Filter.atTop (nhds 0) := by
      have hbound : Filter.Tendsto (fun k => 5 * (6 * (T k : ℝ) / (Lf k) ^ (2 * r + 1)) * (1 / (Lf k) ^ 2))
          Filter.atTop (nhds 0) := by
        have hinv2 : Filter.Tendsto (fun k => 1 / (Lf k) ^ 2) Filter.atTop (nhds 0) :=
          tendsto_const_nhds.div_atTop ((tendsto_pow_atTop' (by omega : 2 ≠ 0)).comp hLf_atTop)
        simpa using ((tendsto_const_nhds.mul hlim).mul hinv2)
      refine squeeze_zero (fun k => by have := hLf_gt1 k; positivity) (fun k => ?_) hbound
      have hL_pos : 0 < Lf k := by linarith [hLf_gt1 k]
      have hL_ne : Lf k ≠ 0 := ne_of_gt hL_pos
      have hsq_le : Real.sqrt (qf k) ≤ Lf k := by dsimp only [Lf]; linarith
      have hrhs : 5 * (6 * (T k : ℝ) / (Lf k) ^ (2 * r + 1)) * (1 / (Lf k) ^ 2) =
          5 * (nf k : ℝ) * Lf k / (Lf k) ^ (2 * r + 4) := by
        dsimp only [nf]; push_cast
        rw [show 2 * r + 4 = (2 * r + 1) + 3 by omega, pow_add]
        field_simp [hL_ne]; ring
      rw [hrhs]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq_le (by positivity)) (by positivity)
    have htot_lim : Filter.Tendsto (fun k =>
        (1024 / (2 : ℝ) ^ (6 * D k) + 1 / (2 : ℝ) ^ (D k)) *
          ((∑ S ∈ (Finset.univ : Finset (Finset (Fin (nf k)))).filter (fun S => S ≠ ∅ ∧ S ≠ Finset.univ),
            (qf k) ^ (exitsS (nf k) S).card) / (Lf k) ^ (nf k)) +
        4 * (2 : ℝ) ^ (16 * D k) * ((3 / 4 : ℝ) ^ (nf k)) +
        30 * (2 : ℝ) ^ (4 * D k) * (Lf k) ^ 11 * (1 - 1 / (2 * Lf k)) ^ (T k) +
        5 * (nf k : ℝ) * Real.sqrt (qf k) / (Lf k) ^ (2 * r + 4)) Filter.atTop (nhds 0) := by
      simpa using (((heps_lim.mul hZ_lim).add h1_lim).add h2_lim).add h3_lim
    refine squeeze_zero' ?_ ?_ htot_lim
    · filter_upwards [hLf_atTop.eventually_ge_atTop 2] with k hL2
      have hnn : 0 ≤ 1 - 1 / (2 * Lf k) := by rw [sub_nonneg, div_le_one (by linarith)]; linarith
      have hZnn : 0 ≤ ∑ S ∈ (Finset.univ : Finset (Finset (Fin (nf k)))).filter (fun S => S ≠ ∅ ∧ S ≠ Finset.univ),
          (qf k) ^ (exitsS (nf k) S).card := Finset.sum_nonneg fun _ _ => pow_nonneg (by linarith [hqf_ge3 k]) _
      positivity
    · filter_upwards [hLf_atTop.eventually_ge_atTop 2, hnf_atTop.eventually_ge_atTop (2 * r + 5)] with k hL2 hnbig
      have hL_pos : 0 < Lf k := by linarith
      have hLn_pos : 0 < (Lf k) ^ (nf k) := pow_pos hL_pos _
      have hLn_ne : (Lf k) ^ (nf k) ≠ 0 := ne_of_gt hLn_pos
      have h2ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (4 * D k) := one_le_pow₀ (by norm_num)
      have hpow_16 : (2 : ℝ) ^ (4 * D k) * (4 : ℝ) ^ (6 * D k) = (2 : ℝ) ^ (16 * D k) := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul, ← pow_add]; congr 1; omega
      have hpow_4 : (4 : ℝ) ^ (6 * D k) ≤ (2 : ℝ) ^ (16 * D k) := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have hmul_34 : ((3 / 4 : ℝ) * Lf k) ^ (nf k) / (Lf k) ^ (nf k) = (3 / 4 : ℝ) ^ (nf k) := by
        rw [mul_pow, mul_div_cancel_right₀ _ hLn_ne]
      have hdiv_gap : (Lf k) ^ (nf k - (2 * r + 4)) / (Lf k) ^ (nf k) = 1 / (Lf k) ^ (2 * r + 4) := by
        have heq : (Lf k) ^ (nf k) = (Lf k) ^ (nf k - (2 * r + 4)) * (Lf k) ^ (2 * r + 4) := by
          rw [← pow_add, Nat.sub_add_cancel (by omega)]
        rw [heq]; field_simp [pow_ne_zero (nf k - (2 * r + 4)) (ne_of_gt hL_pos), pow_ne_zero (2 * r + 4) (ne_of_gt hL_pos)]
      have hnn : 0 ≤ 1 - 1 / (2 * Lf k) := by rw [sub_nonneg, div_le_one (by linarith)]; linarith
      have hterm_t1 : (2 * (2 : ℝ) ^ (4 * D k) * (4 : ℝ) ^ (6 * D k) * ((3 / 4 : ℝ) * Lf k) ^ (nf k) +
          2 * (4 : ℝ) ^ (6 * D k) * ((3 / 4 : ℝ) * Lf k) ^ (nf k)) / (Lf k) ^ (nf k) ≤
          4 * (2 : ℝ) ^ (16 * D k) * (3 / 4 : ℝ) ^ (nf k) := by
        rw [add_div, mul_div_assoc, mul_div_assoc, hmul_34, mul_assoc (2 : ℝ) ((2 : ℝ) ^ (4 * D k)), hpow_16]
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow_4 (by norm_num : (0 : ℝ) ≤ 2))
          (show (0 : ℝ) ≤ (3 / 4 : ℝ) ^ (nf k) by positivity)
        linarith
      have hterm_t2 : (15 * (2 : ℝ) ^ (4 * D k) * (Lf k) ^ 11 * (1 - 1 / (2 * Lf k)) ^ (T k) * (Lf k) ^ (nf k) +
          15 * (Lf k) ^ 11 * (1 - 1 / (2 * Lf k)) ^ (T k) * (Lf k) ^ (nf k)) / (Lf k) ^ (nf k) ≤
          30 * (2 : ℝ) ^ (4 * D k) * (Lf k) ^ 11 * (1 - 1 / (2 * Lf k)) ^ (T k) := by
        rw [add_div, mul_div_cancel_right₀ _ hLn_ne, mul_div_cancel_right₀ _ hLn_ne]
        have hge : 15 * (Lf k) ^ 11 * (1 - 1 / (2 * Lf k)) ^ (T k) ≤
            15 * (2 : ℝ) ^ (4 * D k) * (Lf k) ^ 11 * (1 - 1 / (2 * Lf k)) ^ (T k) := by
          have hnn2 : 0 ≤ (Lf k) ^ 11 * (1 - 1 / (2 * Lf k)) ^ (T k) := by positivity
          nlinarith
        linarith
      have hterm_t3 : (4 * (nf k : ℝ) * Real.sqrt (qf k) * (Lf k) ^ (nf k - (2 * r + 4)) +
          (nf k : ℝ) * Real.sqrt (qf k) * (Lf k) ^ (nf k - (2 * r + 4))) / (Lf k) ^ (nf k) =
          5 * (nf k : ℝ) * Real.sqrt (qf k) / (Lf k) ^ (2 * r + 4) := by
        have hcomb : 4 * (nf k : ℝ) * Real.sqrt (qf k) * (Lf k) ^ (nf k - (2 * r + 4)) +
            (nf k : ℝ) * Real.sqrt (qf k) * (Lf k) ^ (nf k - (2 * r + 4)) =
            (5 * (nf k : ℝ) * Real.sqrt (qf k)) * (Lf k) ^ (nf k - (2 * r + 4)) := by ring
        rw [hcomb, mul_div_assoc, hdiv_gap]; ring
      have hsplit_all :
          ((1024 / (2 : ℝ) ^ (6 * D k) + 1 / (2 : ℝ) ^ (D k)) *
            (∑ S ∈ (Finset.univ : Finset (Finset (Fin (nf k)))).filter (fun S => S ≠ ∅ ∧ S ≠ Finset.univ),
              (qf k) ^ (exitsS (nf k) S).card) +
           (2 * (2 : ℝ) ^ (4 * D k) * (4 : ℝ) ^ (6 * D k) * ((3 / 4 : ℝ) * Lf k) ^ (nf k) +
            15 * (2 : ℝ) ^ (4 * D k) * (Lf k) ^ 11 * (1 - 1 / (2 * Lf k)) ^ (T k) * (Lf k) ^ (nf k) +
            4 * (nf k : ℝ) * Real.sqrt (qf k) * (Lf k) ^ (nf k - (2 * r + 4))) +
           (2 * (4 : ℝ) ^ (6 * D k) * ((3 / 4 : ℝ) * Lf k) ^ (nf k) +
            15 * (Lf k) ^ 11 * (1 - 1 / (2 * Lf k)) ^ (T k) * (Lf k) ^ (nf k) +
            (nf k : ℝ) * Real.sqrt (qf k) * (Lf k) ^ (nf k - (2 * r + 4)))) / (Lf k) ^ (nf k) =
          (1024 / (2 : ℝ) ^ (6 * D k) + 1 / (2 : ℝ) ^ (D k)) *
            ((∑ S ∈ (Finset.univ : Finset (Finset (Fin (nf k)))).filter (fun S => S ≠ ∅ ∧ S ≠ Finset.univ),
              (qf k) ^ (exitsS (nf k) S).card) / (Lf k) ^ (nf k)) +
          (2 * (2 : ℝ) ^ (4 * D k) * (4 : ℝ) ^ (6 * D k) * ((3 / 4 : ℝ) * Lf k) ^ (nf k) +
            2 * (4 : ℝ) ^ (6 * D k) * ((3 / 4 : ℝ) * Lf k) ^ (nf k)) / (Lf k) ^ (nf k) +
          (15 * (2 : ℝ) ^ (4 * D k) * (Lf k) ^ 11 * (1 - 1 / (2 * Lf k)) ^ (T k) * (Lf k) ^ (nf k) +
            15 * (Lf k) ^ 11 * (1 - 1 / (2 * Lf k)) ^ (T k) * (Lf k) ^ (nf k)) / (Lf k) ^ (nf k) +
          (4 * (nf k : ℝ) * Real.sqrt (qf k) * (Lf k) ^ (nf k - (2 * r + 4)) +
            (nf k : ℝ) * Real.sqrt (qf k) * (Lf k) ^ (nf k - (2 * r + 4))) / (Lf k) ^ (nf k) := by ring
      rw [hsplit_all, hterm_t3]
      linarith
  let numF : ℕ → ℝ := fun k =>
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    let n := 6 * T k
    letI : Fintype (Submodule (ZMod 2) (Fin n → ZMod 2)) := Fintype.ofFinite _
    let spaces := (Finset.univ : Finset (Submodule (ZMod 2) (Fin n → ZMod 2))).filter (goodSub n)
    let layer := spaces.filter (fun U : Submodule (ZMod 2) (Fin n → ZMod 2) => Module.finrank (ZMod 2) U = D k)
    let mixed := layer.filter (fun U => ∀ b : Fin 2, ∃ i ∈ suppSub n U, i.val % 2 = b.val)
    let hosts := fun U : Submodule (ZMod 2) (Fin n → ZMod 2) => spaces.filter (fun E => U ≤ E)
    let topDim := fun U : Submodule (ZMod 2) (Fin n → ZMod 2) => (hosts U).sup (fun E : Submodule (ZMod 2) (Fin n → ZMod 2) => Module.finrank (ZMod 2) E)
    let countTop := fun U : Submodule (ZMod 2) (Fin n → ZMod 2) =>
      ((hosts U).filter (fun E : Submodule (ZMod 2) (Fin n → ZMod 2) => Module.finrank (ZMod 2) E = topDim U)).card
    let small := fun S : Finset (Fin n) =>
      ∏ i ∈ exitsS n S, if gapS n S i < 2 * r + 2 then factorG (gapS n S i) else 1
    let event := mixed.filter (fun U => countTop U = small (suppSub n U) * (2 * r + 1) ^ j)
    (2 : ℝ) ^ (4 * D k) * (glCard (D k) : ℝ) * (event.card : ℝ) / (Lf k) ^ (nf k)
  let denF : ℕ → ℝ := fun k =>
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    let n := 6 * T k
    letI : Fintype (Submodule (ZMod 2) (Fin n → ZMod 2)) := Fintype.ofFinite _
    let spaces := (Finset.univ : Finset (Submodule (ZMod 2) (Fin n → ZMod 2))).filter (goodSub n)
    let layer := spaces.filter (fun U : Submodule (ZMod 2) (Fin n → ZMod 2) => Module.finrank (ZMod 2) U = D k)
    let mixed := layer.filter (fun U => ∀ b : Fin 2, ∃ i ∈ suppSub n U, i.val % 2 = b.val)
    (2 : ℝ) ^ (4 * D k) * (glCard (D k) : ℝ) * (mixed.card : ℝ) / (Lf k) ^ (nf k)
  have hden_lim : Filter.Tendsto denF Filter.atTop (nhds 1) := by
    have hdiff : Filter.Tendsto (fun k => denF k -
        (∑ S ∈ (Finset.univ : Finset (Finset (Fin (nf k)))).filter (fun S => S ≠ ∅ ∧ S ≠ Finset.univ),
          (qf k) ^ (exitsS (nf k) S).card) / (Lf k) ^ (nf k)) Filter.atTop (nhds 0) := by
      refine squeeze_zero_norm' ?_ htail_zero
      filter_upwards [hT.eventually_ge_atTop 1, hLf_atTop.eventually_ge_atTop 6,
        hnf_atTop.eventually_ge_atTop (2 * r + 5)] with k ht1 hL6 hnbig
      have htr := (per_k_transfer r (T k) (D k) j hr ht1 (hD k) hL6 (by dsimp only [nf] at hnbig; omega)).1
      have hLn_pos : 0 < (Lf k) ^ (nf k) := pow_pos (by linarith) _
      rw [Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos hLn_pos]
      exact div_le_div_of_nonneg_right htr (le_of_lt hLn_pos)
    simpa [add_sub_cancel] using hZ_lim.add hdiff
  have hnum_lim : Filter.Tendsto numF Filter.atTop
      (nhds (Real.exp (-(τ / 2)) * (τ / 2) ^ j / (Nat.factorial j : ℝ))) := by
    have hdiff : Filter.Tendsto (fun k => numF k -
        (∑ S ∈ (Finset.univ : Finset (Finset (Fin (nf k)))).filter (fun S => S ≠ ∅ ∧ S ≠ Finset.univ),
          if gapCount (nf k) r S = j then (qf k) ^ (exitsS (nf k) S).card else 0) / (Lf k) ^ (nf k))
        Filter.atTop (nhds 0) := by
      refine squeeze_zero_norm' ?_ htail_zero
      filter_upwards [hT.eventually_ge_atTop 1, hLf_atTop.eventually_ge_atTop 6,
        hnf_atTop.eventually_ge_atTop (2 * r + 5)] with k ht1 hL6 hnbig
      have htr := (per_k_transfer r (T k) (D k) j hr ht1 (hD k) hL6 (by dsimp only [nf] at hnbig; omega)).2
      have hLn_pos : 0 < (Lf k) ^ (nf k) := pow_pos (by linarith) _
      rw [Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos hLn_pos]
      exact div_le_div_of_nonneg_right htr (le_of_lt hLn_pos)
    simpa [add_sub_cancel] using hEW_lim.add hdiff
  have hquot : Filter.Tendsto (fun k => numF k / denF k) Filter.atTop
      (nhds (Real.exp (-(τ / 2)) * (τ / 2) ^ j / (Nat.factorial j : ℝ))) := by
    have h := (hnum_lim.div hden_lim one_ne_zero).congr (fun _ => rfl)
    rw [div_one] at h
    exact h
  have hEq : ∀ k, numF k / denF k =
      letI : ∀ p : Prop, Decidable p := Classical.propDecidable
      let t := T k
      let d := D k
      let F := ZMod 2
      let n := 6*t
      let W := Fin n → F
      letI : Fintype (Submodule F W) := Fintype.ofFinite _
      let next := fun i : Fin n =>
        (⟨(i.val+1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
      let h := fun (i : Fin n) (b : Fin 4) =>
        if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2)
        then (1:F) else 0
      let good := fun U : Submodule F W =>
        (∀ x ∈ U, ∀ b : Fin 4, (∑ i, h i b * x i) = 0) ∧
        (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
      let supp := fun U : Submodule F W =>
        Finset.univ.filter (fun i : Fin n => ∃ x ∈ U, x i ≠ 0)
      let spaces := (Finset.univ : Finset (Submodule F W)).filter good
      let layer := spaces.filter (fun U : Submodule F W => Module.finrank F U = d)
      let mixed := layer.filter (fun U => ∀ b : Fin 2, ∃ i ∈ supp U, i.val % 2 = b.val)
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
      let small := fun S : Finset (Fin n) =>
        ∏ i ∈ exits S, if gap S i < 2*r+2 then factor (gap S i) else 1
      let event := mixed.filter (fun U => countTop U = small (supp U) * (2*r+1)^j)
      (event.card : ℝ)/(mixed.card : ℝ) := by
    intro k
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    letI : Fintype (Submodule (ZMod 2) (Fin (6 * T k) → ZMod 2)) := Fintype.ofFinite _
    dsimp only [numF, denF]
    have hc1 : (2 : ℝ) ^ (4 * D k) ≠ 0 := by positivity
    have hc2 : (glCard (D k) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (glCard_pos (D k)))
    have hc3 : (Lf k) ^ (nf k) ≠ 0 := pow_ne_zero _ (by linarith [hLf_gt1 k])
    have hmul : (2 : ℝ) ^ (4 * D k) * (glCard (D k) : ℝ) ≠ 0 := mul_ne_zero hc1 hc2
    rw [div_div_div_cancel_right₀ hc3, mul_div_mul_left _ _ hmul]
    have hh_eq : ∀ (i : Fin (6 * T k)) (b : Fin 4),
        hMat (6 * T k) i b =
          if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2)
          then (1 : ZMod 2) else 0 := fun i b => by
      dsimp only [hMat]; split_ifs <;> rfl
    have hgood_eq : ∀ U : Submodule (ZMod 2) (Fin (6 * T k) → ZMod 2),
        goodSub (6 * T k) U ↔
          (∀ x ∈ U, ∀ b : Fin 4, (∑ i, (if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2) then (1 : ZMod 2) else 0) * x i) = 0) ∧
          (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (nextC (6 * T k) i) = x (nextC (6 * T k) i) * y i) := fun U => by
      dsimp only [goodSub]; simp_rw [hh_eq]
    have hsp_eq : (Finset.univ : Finset (Submodule (ZMod 2) (Fin (6 * T k) → ZMod 2))).filter (goodSub (6 * T k)) =
        (Finset.univ : Finset (Submodule (ZMod 2) (Fin (6 * T k) → ZMod 2))).filter (fun U =>
          (∀ x ∈ U, ∀ b : Fin 4, (∑ i, (if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2) then (1 : ZMod 2) else 0) * x i) = 0) ∧
          (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (nextC (6 * T k) i) = x (nextC (6 * T k) i) * y i)) := by
      ext U; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hgood_eq]
    have hex_eq : ∀ S : Finset (Fin (6 * T k)),
        exitsS (6 * T k) S = S.filter (fun i => nextC (6 * T k) i ∉ S) := fun S => by
      ext i; simp [exitsS]
    have hgap_eq : ∀ (S : Finset (Fin (6 * T k))) (i : Fin (6 * T k)),
        gapS (6 * T k) S i =
          ((Finset.range (6 * T k)).filter (fun m => ∀ j : Fin (m + 1), moveC (6 * T k) i (j.val + 1) ∉ S)).card := fun S i => by
      dsimp only [gapS]; congr 1; ext m; simp
    have hfac_eq : ∀ g : ℕ, factorG g = if (g - 2) % 2 = 0 then (g - 2) + 1 else 1 := fun g => by
      dsimp only [factorG]; split_ifs <;> rfl
    have hsm_eq : ∀ (S : Finset (Fin (6 * T k))) (d : ∀ i, Decidable (gapS (6 * T k) S i < 2 * r + 2)),
        (∏ i ∈ exitsS (6 * T k) S, @ite ℕ (gapS (6 * T k) S i < 2 * r + 2) (d i) (factorG (gapS (6 * T k) S i)) 1) =
        ∏ i ∈ S.filter (fun i => nextC (6 * T k) i ∉ S),
          if ((Finset.range (6 * T k)).filter (fun m => ∀ j : Fin (m + 1), moveC (6 * T k) i (j.val + 1) ∉ S)).card < 2 * r + 2
          then (if (((Finset.range (6 * T k)).filter (fun m => ∀ j : Fin (m + 1), moveC (6 * T k) i (j.val + 1) ∉ S)).card - 2) % 2 = 0
                then ((Finset.range (6 * T k)).filter (fun m => ∀ j : Fin (m + 1), moveC (6 * T k) i (j.val + 1) ∉ S)).card - 2 + 1
                else 1)
          else 1 := fun S d => by
      rw [hex_eq S]
      refine Finset.prod_congr rfl fun i _ => ?_
      have hg := hgap_eq S i
      have h1 : @ite ℕ (gapS (6 * T k) S i < 2 * r + 2) (d i) (factorG (gapS (6 * T k) S i)) 1 =
          if ((Finset.range (6 * T k)).filter (fun m => ∀ j : Fin (m + 1), moveC (6 * T k) i (j.val + 1) ∉ S)).card < 2 * r + 2
          then factorG ((Finset.range (6 * T k)).filter (fun m => ∀ j : Fin (m + 1), moveC (6 * T k) i (j.val + 1) ∉ S)).card
          else 1 := by
        split_ifs with ha hb hc
        · rw [hg]
        · exact (hb (hg ▸ ha)).elim
        · exact (ha (hg.symm ▸ hc)).elim
        · rfl
      rw [h1, hfac_eq]
    congr 1
    · congr 1
      refine congrArg Finset.card ?_
      ext U
      simp only [Finset.mem_filter, hsp_eq]
      rw [hsm_eq (suppSub (6 * T k) U)]
      simp only [suppSub, Finset.mem_filter]
      rfl
    · congr 1
      refine congrArg Finset.card ?_
      ext U
      simp only [suppSub, Finset.mem_filter, hsp_eq]
      rfl
  simpa [hEq] using hquot

end PEqualNP.Outside.L_lib_952

theorem PEqualNP.Outside.L_lib_952 :
    ∀ (r : ℕ), 1 ≤ r → ∀ T D : ℕ → ℕ, Filter.Tendsto T Filter.atTop Filter.atTop →
      (∀ k, 2 ≤ D k) → ∀ τ : ℝ, 0 < τ →
      Filter.Tendsto (fun k => 6*(T k : ℝ)/
        (1+Real.sqrt ((2 : ℝ)^(D k)-1))^(2*r+1)) Filter.atTop (nhds τ) →
      ∀ j : ℕ, Filter.Tendsto (fun k : ℕ =>
      letI : ∀ p : Prop, Decidable p := Classical.propDecidable
      let t := T k
      let d := D k
      let F := ZMod 2
      let n := 6*t
      let W := Fin n → F
      letI : Fintype (Submodule F W) := Fintype.ofFinite _
      let next := fun i : Fin n =>
        (⟨(i.val+1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
      let h := fun (i : Fin n) (b : Fin 4) =>
        if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2)
        then (1:F) else 0
      let good := fun U : Submodule F W =>
        (∀ x ∈ U, ∀ b : Fin 4, (∑ i, h i b * x i) = 0) ∧
        (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
      let supp := fun U : Submodule F W =>
        Finset.univ.filter (fun i : Fin n => ∃ x ∈ U, x i ≠ 0)
      let spaces := (Finset.univ : Finset (Submodule F W)).filter good
      let layer := spaces.filter (fun U : Submodule F W => Module.finrank F U = d)
      let mixed := layer.filter (fun U => ∀ b : Fin 2, ∃ i ∈ supp U, i.val % 2 = b.val)
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
      let small := fun S : Finset (Fin n) =>
        ∏ i ∈ exits S, if gap S i < 2*r+2 then factor (gap S i) else 1
      let event := mixed.filter (fun U => countTop U = small (supp U) * (2*r+1)^j)
      (event.card : ℝ)/(mixed.card : ℝ)) Filter.atTop
        (nhds (Real.exp (-(τ/2)) * (τ/2)^j / (Nat.factorial j : ℝ))) :=
  PEqualNP.Outside.L_lib_952.main
