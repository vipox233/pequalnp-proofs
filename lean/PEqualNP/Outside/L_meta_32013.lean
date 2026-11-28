import PEqualNP.Defs
import Mathlib.Data.Nat.Log

namespace PEqualNP.Outside.L_meta_32013_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

private def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_stepW_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, stepW, List.length_append, List.length_cons, List.length_nil]
    omega

private lemma foldl_stepW_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (stepW w g).length := by
      simp only [stepW, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih _ hlt]
    simp only [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

private lemma stepW_getD_self (w : List Bool) (g : Gate) :
    (stepW w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) :=
  getD_append_self w _

private lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

private lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

private lemma eval_eq_of_eq_on_used {n : ℕ} (C : Circuit) (x₁ x₂ : List Bool)
    (hx1 : x₁.length = n) (hx2 : x₂.length = n)
    (hRB : ReadsBack n C)
    (hEq : ∀ i < n, (C.output = i ∨ ∃ g ∈ C.gates, i ∈ g.inputs) →
      x₁.getD i false = x₂.getD i false) :
    C.eval x₁ = C.eval x₂ := by
  have hprefix : ∀ k ≤ C.gates.length, ∀ j < k,
      ((C.gates.take k).foldl stepW x₁).getD (n + j) false =
      ((C.gates.take k).foldl stepW x₂).getD (n + j) false := by
    intro k hk
    induction k with
    | zero => intro j hj; omega
    | succ k ih =>
      have hklt : k < C.gates.length := by omega
      have htake : C.gates.take (k + 1) = C.gates.take k ++ [C.gates[k]] :=
        List.take_succ_eq_append_getElem hklt
      have hlen1 : ((C.gates.take k).foldl stepW x₁).length = n + k := by
        rw [foldl_stepW_len, hx1, List.length_take_of_le (by omega)]
      have hlen2 : ((C.gates.take k).foldl stepW x₂).length = n + k := by
        rw [foldl_stepW_len, hx2, List.length_take_of_le (by omega)]
      intro j hj
      simp only [htake, List.foldl_append, List.foldl_cons, List.foldl_nil]
      by_cases hjk : j < k
      · have hlt1 : n + j < ((C.gates.take k).foldl stepW x₁).length := by omega
        have hlt2 : n + j < ((C.gates.take k).foldl stepW x₂).length := by omega
        simp only [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt1,
          List.getElem?_append_left hlt2]
        simpa only [List.getD_eq_getElem?_getD] using ih (by omega) j hjk
      · have hjeq : j = k := by omega
        subst hjeq
        simp only [stepW]
        have h1 : (((C.gates.take j).foldl stepW x₁) ++
            [C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
              ((C.gates.take j).foldl stepW x₁).getD i false)]).getD (n + j) false =
            C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
              ((C.gates.take j).foldl stepW x₁).getD i false) := by
          rw [← hlen1]; exact getD_append_self _ _
        have h2 : (((C.gates.take j).foldl stepW x₂) ++
            [C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
              ((C.gates.take j).foldl stepW x₂).getD i false)]).getD (n + j) false =
            C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
              ((C.gates.take j).foldl stepW x₂).getD i false) := by
          rw [← hlen2]; exact getD_append_self _ _
        rw [h1, h2]
        congr 1
        apply List.map_congr_left
        intro i hi
        have hi_lt : i < n + j := by
          have := hRB j hklt i
          rw [gateAt_eq_getElem C j hklt] at this
          exact this hi
        by_cases hin : i < n
        · rw [foldl_stepW_getD_lt _ _ i (by omega), foldl_stepW_getD_lt _ _ i (by omega)]
          exact hEq i hin (Or.inr ⟨C.gates[j], List.getElem_mem hklt, hi⟩)
        · have hj' : i - n < j := by omega
          have heq := ih (by omega) (i - n) hj'
          have hrew : n + (i - n) = i := by omega
          rw [hrew] at heq
          exact heq
  change (C.gates.foldl stepW x₁).getD C.output false =
    (C.gates.foldl stepW x₂).getD C.output false
  by_cases hout : C.output < n
  · rw [foldl_stepW_getD_lt _ _ C.output (by omega), foldl_stepW_getD_lt _ _ C.output (by omega)]
    exact hEq C.output hout (Or.inl rfl)
  · by_cases hout2 : C.output < n + C.gates.length
    · have hfull := hprefix C.gates.length (le_refl _) (C.output - n) (by omega)
      rw [List.take_length] at hfull
      have hrew : n + (C.output - n) = C.output := by omega
      rw [hrew] at hfull
      exact hfull
    · rw [getD_ge_len _ _ (by rw [foldl_stepW_len, hx1]; omega),
          getD_ge_len _ _ (by rw [foldl_stepW_len, hx2]; omega)]

private lemma oneEach_append_len {N h : ℕ} (x y : Fin N) (w : Fin h → Bool) :
    (oneEach x y ++ List.ofFn w).length = N + N + h := by
  simp [oneEach]; omega

private lemma oneEach_append_getD {N h : ℕ} (x y : Fin N) (w : Fin h → Bool) (i : ℕ)
    (hi : i < N + N + h) :
    (oneEach x y ++ List.ofFn w).getD i false =
      if h1 : i < N then decide ((⟨i, h1⟩ : Fin N) = x)
      else if h2 : i < N + N then decide ((⟨i - N, by omega⟩ : Fin N) = y)
      else w ⟨i - (N + N), by omega⟩ := by
  simp only [oneEach, List.getD_eq_getElem?_getD]
  by_cases h1 : i < N
  · have hlt1 : i < (List.ofFn (fun j : Fin N => decide (j = x)) ++
        List.ofFn (fun j : Fin N => decide (j = y))).length := by simp; omega
    rw [List.getElem?_append_left hlt1, List.getElem?_append_left (by simp; omega)]
    simp [h1]
  · by_cases h2 : i < N + N
    · have hlt1 : i < (List.ofFn (fun j : Fin N => decide (j = x)) ++
          List.ofFn (fun j : Fin N => decide (j = y))).length := by simp; omega
      have hltN : i - N < N := by omega
      rw [List.getElem?_append_left hlt1, List.getElem?_append_right (by simp; omega)]
      simp [h1, h2, hltN]
    · have hlth : i - (N + N) < h := by omega
      rw [List.getElem?_append_right (by simp; omega)]
      simp [h1, h2, hlth]

private lemma table_supp_rect {N h E : ℕ} {R S : Finset (Fin N)}
    (hR : R.card + E < N) (hS : S.card + E < N)
    (C : Circuit) (w : Fin h → Bool)
    (hRB : ReadsBack (N + N + h) C)
    (hNameR : ∀ x : Fin N, (C.output = x.val ∨ ∃ g ∈ C.gates, x.val ∈ g.inputs) → x ∈ R)
    (hNameS : ∀ y : Fin N, (C.output = N + y.val ∨ ∃ g ∈ C.gates, N + y.val ∈ g.inputs) → y ∈ S)
    (hCard : (Finset.univ.filter (fun z : Fin N × Fin N =>
        C.eval (oneEach z.1 z.2 ++ List.ofFn w) = true)).card ≤ E)
    (x y : Fin N) (hxy : C.eval (oneEach x y ++ List.ofFn w) = true) :
    x ∈ R ∧ y ∈ S := by
  constructor
  · by_contra hxR
    have hconst : ∀ x' : Fin N, x' ∉ R →
        C.eval (oneEach x' y ++ List.ofFn w) = true := by
      intro x' hx'R
      rw [← hxy]
      apply eval_eq_of_eq_on_used C _ _ (oneEach_append_len x' y w) (oneEach_append_len x y w) hRB
      intro i hi huse
      rw [oneEach_append_getD x' y w i hi, oneEach_append_getD x y w i hi]
      split_ifs with h1 h2
      · have hiR : (⟨i, h1⟩ : Fin N) ∈ R := hNameR ⟨i, h1⟩ huse
        have hne1 : (⟨i, h1⟩ : Fin N) ≠ x' := fun h => hx'R (h ▸ hiR)
        have hne2 : (⟨i, h1⟩ : Fin N) ≠ x := fun h => hxR (h ▸ hiR)
        simp [hne1, hne2]
      · rfl
      · rfl
    have hsub : (Finset.univ.filter (fun x' : Fin N => x' ∉ R)).image (fun x' => (x', y)) ⊆
        Finset.univ.filter (fun z : Fin N × Fin N =>
          C.eval (oneEach z.1 z.2 ++ List.ofFn w) = true) := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨x', hx', rfl⟩
      rw [Finset.mem_filter] at hx' ⊢
      exact ⟨Finset.mem_univ _, hconst x' hx'.2⟩
    have hcard_le := Finset.card_le_card hsub
    have hinj : Function.Injective (fun x' : Fin N => (x', y)) := fun a b h => (Prod.mk.inj h).1
    rw [Finset.card_image_of_injective _ hinj] at hcard_le
    have hcomp : (Finset.univ.filter (fun x' : Fin N => x' ∉ R)).card + R.card = N := by
      have h1 : Finset.univ.filter (fun x' : Fin N => x' ∉ R) = Rᶜ := by ext a; simp
      rw [h1, Finset.card_compl, Fintype.card_fin]
      have hle : R.card ≤ N := by simpa using Finset.card_le_univ R
      omega
    omega
  · by_contra hyS
    have hconst : ∀ y' : Fin N, y' ∉ S →
        C.eval (oneEach x y' ++ List.ofFn w) = true := by
      intro y' hy'S
      rw [← hxy]
      apply eval_eq_of_eq_on_used C _ _ (oneEach_append_len x y' w) (oneEach_append_len x y w) hRB
      intro i hi huse
      rw [oneEach_append_getD x y' w i hi, oneEach_append_getD x y w i hi]
      split_ifs with h1 h2
      · rfl
      · have hrew : N + (i - N) = i := by omega
        have hiS : (⟨i - N, by omega⟩ : Fin N) ∈ S := hNameS ⟨i - N, by omega⟩ (by simpa [hrew] using huse)
        have hne1 : (⟨i - N, by omega⟩ : Fin N) ≠ y' := fun h => hy'S (h ▸ hiS)
        have hne2 : (⟨i - N, by omega⟩ : Fin N) ≠ y := fun h => hyS (h ▸ hiS)
        simp [hne1, hne2]
      · rfl
    have hsub : (Finset.univ.filter (fun y' : Fin N => y' ∉ S)).image (fun y' => (x, y')) ⊆
        Finset.univ.filter (fun z : Fin N × Fin N =>
          C.eval (oneEach z.1 z.2 ++ List.ofFn w) = true) := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨y', hy', rfl⟩
      rw [Finset.mem_filter] at hy' ⊢
      exact ⟨Finset.mem_univ _, hconst y' hy'.2⟩
    have hcard_le := Finset.card_le_card hsub
    have hinj : Function.Injective (fun y' : Fin N => (x, y')) := fun a b h => (Prod.mk.inj h).2
    rw [Finset.card_image_of_injective _ hinj] at hcard_le
    have hcomp : (Finset.univ.filter (fun y' : Fin N => y' ∉ S)).card + S.card = N := by
      have h1 : Finset.univ.filter (fun y' : Fin N => y' ∉ S) = Sᶜ := by ext a; simp
      rw [h1, Finset.card_compl, Fintype.card_fin]
      have hle : S.card ≤ N := by simpa using Finset.card_le_univ S
      omega
    omega

private def matchCount {N q : ℕ} (f : Fin q → Equiv.Perm (Fin N))
    (H : Fin N → Fin N → Bool) (j : Fin q) : ℕ :=
  (Finset.univ.filter (fun x : Fin N => H x (f j x) = true)).card

private def totalOnes {N : ℕ} (H : Fin N → Fin N → Bool) : ℕ :=
  (Finset.univ.filter (fun z : Fin N × Fin N => H z.1 z.2 = true)).card

private def lossFun {N q : ℕ} (f : Fin q → Equiv.Perm (Fin N))
    (H : Fin N → Fin N → Bool) (U : Finset (Fin q)) : ℕ :=
  (Finset.univ.filter (fun z : Fin N × Fin N =>
    H z.1 z.2 ≠ decide (z.2 ∈ U.image (fun j => f j z.1)))).card

private lemma lossFun_empty {N q : ℕ} (f : Fin q → Equiv.Perm (Fin N))
    (H : Fin N → Fin N → Bool) :
    lossFun f H ∅ = totalOnes H := by
  unfold lossFun totalOnes
  congr 1
  ext z
  simp

private lemma symmDiff_card_eq {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) :
    (Finset.univ.filter (fun z => decide (z ∈ A) ≠ decide (z ∈ B))).card + 2 * (A ∩ B).card =
      A.card + B.card := by
  have h1 : Finset.univ.filter (fun z => decide (z ∈ A) ≠ decide (z ∈ B)) = (A \ B) ∪ (B \ A) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_sdiff]
    by_cases hA : z ∈ A <;> by_cases hB : z ∈ B <;> simp [hA, hB]
  rw [h1, Finset.card_union_of_disjoint]
  · have hA : (A \ B).card + (A ∩ B).card = A.card := Finset.card_sdiff_add_card_inter A B
    have hB : (B \ A).card + (B ∩ A).card = B.card := Finset.card_sdiff_add_card_inter B A
    rw [Finset.inter_comm] at hB
    omega
  · rw [Finset.disjoint_left]
    intro z hz1 hz2
    exact (Finset.mem_sdiff.mp hz1).2 (Finset.mem_sdiff.mp hz2).1

private lemma lossFun_eq_real {N q : ℕ} (f : Fin q → Equiv.Perm (Fin N))
    (hf : ∀ x : Fin N, Function.Injective (fun j => f j x))
    (H : Fin N → Fin N → Bool) (U : Finset (Fin q)) :
    (lossFun f H U : ℝ) =
      ((N * U.card : ℕ) : ℝ) + (totalOnes H : ℝ) -
        2 * ∑ j ∈ U, (matchCount f H j : ℝ) := by
  let A : Finset (Fin N × Fin N) := Finset.univ.filter (fun z => H z.1 z.2 = true)
  let B : Finset (Fin N × Fin N) := Finset.univ.filter (fun z => z.2 ∈ U.image (fun j => f j z.1))
  have hloss : lossFun f H U =
      (Finset.univ.filter (fun z => decide (z ∈ A) ≠ decide (z ∈ B))).card := by
    unfold lossFun
    congr 1
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, A, B]
    cases H z.1 z.2 <;> by_cases hB : z.2 ∈ U.image (fun j => f j z.1) <;> simp [hB]
  have hB_eq : B = (U ×ˢ (Finset.univ : Finset (Fin N))).image (fun p => (p.2, f p.1 p.2)) := by
    ext ⟨x, y⟩
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_product,
      and_true]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨(j, x), hj, rfl⟩
    · rintro ⟨⟨j, x'⟩, hj, hpair⟩
      rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
      exact ⟨j, hj, rfl⟩
  have hinj_map : Function.Injective (fun p : Fin q × Fin N => (p.2, f p.1 p.2)) := by
    rintro ⟨j1, x1⟩ ⟨j2, x2⟩ h
    rcases Prod.mk.inj h with ⟨rfl, h2⟩
    exact Prod.ext (hf x1 h2) rfl
  have hB_card : B.card = N * U.card := by
    rw [hB_eq, Finset.card_image_of_injective _ hinj_map, Finset.card_product,
      Finset.card_univ, Fintype.card_fin, mul_comm]
  have hAB_eq : A ∩ B =
      ((U ×ˢ (Finset.univ : Finset (Fin N))).filter (fun p => H p.2 (f p.1 p.2) = true)).image
        (fun p => (p.2, f p.1 p.2)) := by
    ext ⟨x, y⟩
    simp only [A, B, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, Finset.mem_product, and_true]
    constructor
    · rintro ⟨hH, j, hj, rfl⟩
      exact ⟨(j, x), ⟨hj, hH⟩, rfl⟩
    · rintro ⟨⟨j, x'⟩, ⟨hj, hH⟩, hpair⟩
      rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
      exact ⟨hH, j, hj, rfl⟩
  have hAB_card : (A ∩ B).card = ∑ j ∈ U, matchCount f H j := by
    rw [hAB_eq, Finset.card_image_of_injective _ hinj_map]
    have hfilt : (U ×ˢ (Finset.univ : Finset (Fin N))).filter (fun p => H p.2 (f p.1 p.2) = true) =
        U.biUnion (fun j => (Finset.univ.filter (fun x : Fin N => H x (f j x) = true)).map
          ⟨fun x => (j, x), fun _ _ h => (Prod.mk.inj h).2⟩) := by
      ext ⟨j, x⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
        Finset.mem_biUnion, Finset.mem_map, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨hj, hH⟩; exact ⟨j, hj, x, ⟨trivial, hH⟩, rfl⟩
      · rintro ⟨j', hj', x', ⟨_, hH⟩, hpair⟩
        rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
        exact ⟨hj', hH⟩
    rw [hfilt, Finset.card_biUnion]
    · apply Finset.sum_congr rfl
      intro j _
      rw [Finset.card_map]
      rfl
    · intro j1 _ j2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hp1 hp2
      rcases hp1 with ⟨x1, _, rfl⟩
      rcases hp2 with ⟨x2, _, h⟩
      exact hne (Prod.mk.inj h).1.symm
  have hsym := symmDiff_card_eq A B
  rw [← hloss, hB_card, hAB_card] at hsym
  have hA_card : A.card = totalOnes H := rfl
  rw [hA_card] at hsym
  have hreal : (lossFun f H U : ℝ) + 2 * ∑ j ∈ U, (matchCount f H j : ℝ) =
      (totalOnes H : ℝ) + ((N * U.card : ℕ) : ℝ) := by
    exact_mod_cast hsym
  linarith

private lemma sum_matchCount_le_totalOnes {N q : ℕ} (f : Fin q → Equiv.Perm (Fin N))
    (hf : ∀ x : Fin N, Function.Injective (fun j => f j x))
    (H : Fin N → Fin N → Bool) :
    ∑ j : Fin q, matchCount f H j ≤ totalOnes H := by
  have hinj : Function.Injective (fun p : Fin q × Fin N => (p.2, f p.1 p.2)) := by
    rintro ⟨j1, x1⟩ ⟨j2, x2⟩ h
    rcases Prod.mk.inj h with ⟨rfl, h2⟩
    exact Prod.ext (hf x1 h2) rfl
  let S := (Finset.univ : Finset (Fin q)).biUnion
    (fun j => (Finset.univ.filter (fun x : Fin N => H x (f j x) = true)).map
      ⟨fun x => (j, x), fun _ _ h => (Prod.mk.inj h).2⟩)
  have hScard : S.card = ∑ j : Fin q, matchCount f H j := by
    rw [Finset.card_biUnion]
    · apply Finset.sum_congr rfl; intro j _; rw [Finset.card_map]; rfl
    · intro j1 _ j2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hp1 hp2
      rcases hp1 with ⟨x1, _, rfl⟩
      rcases hp2 with ⟨x2, _, h⟩
      exact hne (Prod.mk.inj h).1.symm
  have hsub : S.image (fun p => (p.2, f p.1 p.2)) ⊆
      Finset.univ.filter (fun z : Fin N × Fin N => H z.1 z.2 = true) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨⟨j, x⟩, hp, rfl⟩
    simp only [S, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_map,
      Finset.mem_filter] at hp
    rcases hp with ⟨j', x', hx', hpair⟩
    rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
    simp [hx']
  have hle := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, hScard] at hle
  exact hle

private lemma matchCount_le_cap {N q : ℕ} (f : Fin q → Equiv.Perm (Fin N))
    (R S : Finset (Fin N)) (H : Fin N → Fin N → Bool)
    (hsupp : ∀ x y : Fin N, H x y = true → x ∈ R ∧ y ∈ S) (j : Fin q) :
    matchCount f H j ≤ (R.filter (fun x => f j x ∈ S)).card := by
  unfold matchCount
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact hsupp x (f j x) hx.2

private def widthOf {q : ℕ} (cap : Fin q → ℕ) (l : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin q)).filter (fun j => l < cap j)).card

private def usedOf {q : ℕ} (cap : Fin q → ℕ) (l : ℕ) : ℕ :=
  ∑ j : Fin q, min (cap j) l

private noncomputable def gainOf {q : ℕ} (cap : Fin q → ℕ) (E t : ℕ) : ℝ :=
  ∑ l ∈ Finset.range E,
    ((min (widthOf cap l) (E - usedOf cap l) * (widthOf cap l - 2 * (q - t)) : ℕ) : ℝ) /
      (widthOf cap l : ℝ)

private lemma usedOf_zero {q : ℕ} (cap : Fin q → ℕ) : usedOf cap 0 = 0 := by
  simp [usedOf]

private lemma usedOf_succ {q : ℕ} (cap : Fin q → ℕ) (l : ℕ) :
    usedOf cap (l + 1) = usedOf cap l + widthOf cap l := by
  unfold usedOf widthOf
  have hstep : ∀ j : Fin q, min (cap j) (l + 1) = min (cap j) l + if l < cap j then 1 else 0 := by
    intro j; split_ifs <;> omega
  simp_rw [hstep, Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id]

private lemma sum_widthOf_eq_usedOf {q : ℕ} (cap : Fin q → ℕ) (L : ℕ) :
    ∑ l ∈ Finset.range L, widthOf cap l = usedOf cap L := by
  induction L with
  | zero => simp [usedOf_zero]
  | succ k ih => rw [Finset.sum_range_succ, ih, usedOf_succ]

private lemma usedOf_mono {q : ℕ} (cap : Fin q → ℕ) : Monotone (usedOf cap) := by
  apply monotone_nat_of_le_succ
  intro l
  rw [usedOf_succ]
  omega

private lemma widthOf_anti {q : ℕ} (cap : Fin q → ℕ) : Antitone (widthOf cap) := by
  intro a b hab
  unfold widthOf
  apply Finset.card_le_card
  intro j hj
  rw [Finset.mem_filter] at hj ⊢
  exact ⟨Finset.mem_univ _, by omega⟩

private lemma slice_sum_eq (E : ℕ) (u : ℝ) (hu0 : 0 ≤ u) (huE : u ≤ E) :
    ∑ l ∈ Finset.range E, max (0 : ℝ) (min 1 (u - (l : ℝ))) = u := by
  induction E generalizing u with
  | zero =>
    simp only [Nat.cast_zero] at huE
    simp only [Finset.range_zero, Finset.sum_empty]
    linarith
  | succ n ih =>
    rw [Finset.sum_range_succ]
    by_cases hun : u ≤ n
    · have h0 : max (0 : ℝ) (min 1 (u - (n : ℝ))) = 0 := by
        apply max_eq_left
        exact le_trans (min_le_right _ _) (by linarith)
      rw [h0, add_zero]
      exact ih u hu0 hun
    · push Not at hun
      have hmin : ∀ l ∈ Finset.range n, max (0 : ℝ) (min 1 (u - (l : ℝ))) = 1 := by
        intro l hl
        rw [Finset.mem_range] at hl
        have h1 : (l : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hl
        have hle : (1 : ℝ) ≤ u - (l : ℝ) := by linarith
        rw [min_eq_left hle, max_eq_right (by norm_num)]
      rw [Finset.sum_congr rfl hmin, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      have hlast : max (0 : ℝ) (min 1 (u - (n : ℝ))) = u - (n : ℝ) := by
        have h1 : u - (n : ℝ) ≤ 1 := by push_cast at huE; linarith
        rw [min_eq_right h1, max_eq_right (by linarith)]
      rw [hlast]
      ring

private lemma coeff_anti (r : ℕ) {w1 w2 : ℕ} (h : w1 ≤ w2) :
    ((w1 - 2 * r : ℕ) : ℝ) / (w1 : ℝ) ≤ ((w2 - 2 * r : ℕ) : ℝ) / (w2 : ℝ) := by
  by_cases hw1 : w1 ≤ 2 * r
  · have h0 : w1 - 2 * r = 0 := Nat.sub_eq_zero_of_le hw1
    rw [h0, Nat.cast_zero, zero_div]
    positivity
  · have hw1_pos : (0 : ℝ) < (w1 : ℝ) := by exact_mod_cast (by omega : 0 < w1)
    have hw2_pos : (0 : ℝ) < (w2 : ℝ) := by exact_mod_cast (by omega : 0 < w2)
    rw [div_le_div_iff₀ hw1_pos hw2_pos]
    have hsub1 : ((w1 - 2 * r : ℕ) : ℝ) = (w1 : ℝ) - 2 * (r : ℝ) := by
      have := Nat.cast_sub (R := ℝ) (by omega : 2 * r ≤ w1)
      push_cast at this; exact this
    have hsub2 : ((w2 - 2 * r : ℕ) : ℝ) = (w2 : ℝ) - 2 * (r : ℝ) := by
      have := Nat.cast_sub (R := ℝ) (by omega : 2 * r ≤ w2)
      push_cast at this; exact this
    rw [hsub1, hsub2]
    have hle : (w1 : ℝ) ≤ (w2 : ℝ) := by exact_mod_cast h
    have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    nlinarith

private lemma level_bound {q : ℕ} (r : ℕ) (W V : Finset (Fin q))
    (hVcard : V.card = r) (y : Fin q → ℝ)
    (hy0 : ∀ j, 0 ≤ y j)
    (hsupp : ∀ j, j ∉ W → y j = 0)
    (hmax : ∀ a ∈ V, ∀ b ∉ V, y b ≤ y a) :
    (∑ j : Fin q, y j) - 2 * (∑ j ∈ V, y j) ≤
      (∑ j : Fin q, y j) * (((W.card - 2 * r : ℕ) : ℝ) / (W.card : ℝ)) := by
  have hsumW : ∑ j : Fin q, y j = ∑ j ∈ W, y j := by
    symm
    apply Finset.sum_subset (Finset.subset_univ W)
    intro j _ hj
    exact hsupp j hj
  have hs0 : 0 ≤ ∑ j : Fin q, y j := Finset.sum_nonneg (fun j _ => hy0 j)
  by_cases hsub : V ⊆ W
  · have hsplit : ∑ j ∈ W, y j = (∑ j ∈ V, y j) + (∑ j ∈ W \ V, y j) := by
      rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hsub]
    have hdouble : (r : ℝ) * (∑ j ∈ W \ V, y j) ≤ ((W \ V).card : ℝ) * (∑ j ∈ V, y j) := by
      have hle : ∑ a ∈ V, ∑ b ∈ W \ V, y b ≤ ∑ a ∈ V, ∑ b ∈ W \ V, y a := by
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro b hb
        exact hmax a ha b (Finset.mem_sdiff.mp hb).2
      rw [Finset.sum_const, nsmul_eq_mul, hVcard] at hle
      have hrhs : ∑ a ∈ V, ∑ _b ∈ W \ V, y a = ((W \ V).card : ℝ) * ∑ a ∈ V, y a := by
        simp_rw [Finset.sum_const, nsmul_eq_mul]
        rw [← Finset.mul_sum]
      rw [hrhs] at hle
      exact hle
    have hcard_sdiff : (W \ V).card + r = W.card := by
      rw [← hVcard]
      exact Finset.card_sdiff_add_card_eq_card hsub
    have hkey : (r : ℝ) * (∑ j : Fin q, y j) ≤ (W.card : ℝ) * (∑ j ∈ V, y j) := by
      rw [hsumW, hsplit]
      have hcast : ((W \ V).card : ℝ) + (r : ℝ) = (W.card : ℝ) := by exact_mod_cast hcard_sdiff
      have hWmul : (W.card : ℝ) * (∑ j ∈ V, y j) =
          ((W \ V).card : ℝ) * (∑ j ∈ V, y j) + (r : ℝ) * (∑ j ∈ V, y j) := by
        rw [← hcast]; ring
      linarith
    by_cases hw2r : W.card ≤ 2 * r
    · have h0 : W.card - 2 * r = 0 := Nat.sub_eq_zero_of_le hw2r
      rw [h0, Nat.cast_zero, zero_div, mul_zero]
      by_cases hw0 : W.card = 0
      · have hWempty : W = ∅ := Finset.card_eq_zero.mp hw0
        rw [hsumW, hWempty, Finset.sum_empty]
        have hV0 : 0 ≤ ∑ j ∈ V, y j := Finset.sum_nonneg (fun j _ => hy0 j)
        linarith
      · have hw_pos : (0 : ℝ) < (W.card : ℝ) := by exact_mod_cast (by omega : 0 < W.card)
        have hle2 : (W.card : ℝ) ≤ 2 * (r : ℝ) := by exact_mod_cast hw2r
        nlinarith
    · have hw_pos : (0 : ℝ) < (W.card : ℝ) := by exact_mod_cast (by omega : 0 < W.card)
      have hsub_cast : ((W.card - 2 * r : ℕ) : ℝ) = (W.card : ℝ) - 2 * (r : ℝ) := by
        have := Nat.cast_sub (R := ℝ) (by omega : 2 * r ≤ W.card)
        push_cast at this; exact this
      rw [hsub_cast, ← mul_div_assoc, le_div_iff₀ hw_pos]
      nlinarith
  · rw [Finset.not_subset] at hsub
    rcases hsub with ⟨a, haV, haW⟩
    have ha0 : y a = 0 := hsupp a haW
    have hout0 : ∀ b, b ∉ V → y b = 0 := by
      intro b hb
      exact le_antisymm (ha0 ▸ hmax a haV b hb) (hy0 b)
    have heq : ∑ j : Fin q, y j = ∑ j ∈ V, y j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ V)
      intro b _ hb
      exact hout0 b hb
    rw [heq]
    have hV0 : 0 ≤ ∑ j ∈ V, y j := Finset.sum_nonneg (fun j _ => hy0 j)
    have hrhs0 : 0 ≤ (∑ j ∈ V, y j) * (((W.card - 2 * r : ℕ) : ℝ) / (W.card : ℝ)) := by positivity
    linarith

private lemma capped_alloc_lower {q E t : ℕ} (ht : t ≤ q) (cap : Fin q → ℕ)
    (x : Fin q → ℝ) (hx0 : ∀ j, 0 ≤ x j) (hxcap : ∀ j, x j ≤ cap j)
    (hxsum : ∑ j, x j ≤ E) :
    ∃ U : Finset (Fin q), U.card = t ∧
      (∑ j : Fin q, x j) - 2 * (∑ j ∈ Uᶜ, x j) ≤ gainOf cap E t := by
  let r := q - t
  have hrq : r ≤ q := Nat.sub_le q t
  have hne : (Finset.powersetCard r (Finset.univ : Finset (Fin q))).Nonempty := by
    rw [Finset.powersetCard_nonempty]
    simp [hrq]
  obtain ⟨V, hVmem, hVmax⟩ := Finset.exists_max_image
    (Finset.powersetCard r (Finset.univ : Finset (Fin q))) (fun S => ∑ j ∈ S, x j) hne
  have hVcard : V.card = r := (Finset.mem_powersetCard.mp hVmem).2
  have hmax : ∀ a ∈ V, ∀ b ∉ V, x b ≤ x a := by
    intro a ha b hb
    let V' := insert b (V.erase a)
    have hb_erase : b ∉ V.erase a := fun h => hb (Finset.mem_erase.mp h).2
    have hV'card : V'.card = r := by
      rw [Finset.card_insert_of_notMem hb_erase, Finset.card_erase_of_mem ha]
      have hpos : 0 < V.card := Finset.card_pos.mpr ⟨a, ha⟩
      omega
    have hV'mem : V' ∈ Finset.powersetCard r (Finset.univ : Finset (Fin q)) :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hV'card⟩
    have hle := hVmax V' hV'mem
    have hsum1 : ∑ j ∈ V', x j = x b + ∑ j ∈ V.erase a, x j :=
      Finset.sum_insert hb_erase
    have hsum2 : ∑ j ∈ V, x j = x a + ∑ j ∈ V.erase a, x j :=
      (Finset.add_sum_erase V x ha).symm
    linarith
  refine ⟨Vᶜ, ?_, ?_⟩
  · rw [Finset.card_compl, Fintype.card_fin, hVcard]
    omega
  · rw [compl_compl]
    let y : ℕ → Fin q → ℝ := fun l j => max (0 : ℝ) (min 1 (x j - (l : ℝ)))
    have hx_eq : ∀ j : Fin q, x j = ∑ l ∈ Finset.range E, y l j := by
      intro j
      have hxjE : x j ≤ E := le_trans (Finset.single_le_sum (fun i _ => hx0 i) (Finset.mem_univ j)) hxsum
      exact (slice_sum_eq E (x j) (hx0 j) hxjE).symm
    have hlhs : (∑ j : Fin q, x j) - 2 * (∑ j ∈ V, x j) =
        ∑ l ∈ Finset.range E, ((∑ j : Fin q, y l j) - 2 * (∑ j ∈ V, y l j)) := by
      simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      congr 1
      · rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; exact hx_eq j
      · congr 1; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; exact hx_eq j
    rw [hlhs]
    let s : ℕ → ℝ := fun l => ∑ j : Fin q, y l j
    let c : ℕ → ℝ := fun l => ((widthOf cap l - 2 * r : ℕ) : ℝ) / (widthOf cap l : ℝ)
    have hstep1 : ∑ l ∈ Finset.range E, ((∑ j : Fin q, y l j) - 2 * (∑ j ∈ V, y l j)) ≤
        ∑ l ∈ Finset.range E, s l * c l := by
      apply Finset.sum_le_sum
      intro l _
      let W := (Finset.univ : Finset (Fin q)).filter (fun j => l < cap j)
      have hWcard : W.card = widthOf cap l := rfl
      have hsupp : ∀ j, j ∉ W → y l j = 0 := by
        intro j hj
        simp only [W, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
        have hle : x j ≤ (l : ℝ) := le_trans (hxcap j) (by exact_mod_cast hj)
        apply max_eq_left
        exact le_trans (min_le_right _ _) (by linarith)
      have hymax : ∀ a ∈ V, ∀ b ∉ V, y l b ≤ y l a := by
        intro a ha b hb
        have hba := hmax a ha b hb
        dsimp only [y]
        exact max_le_max_left 0 (min_le_min_left 1 (by linarith))
      simpa only [s, c, hWcard] using level_bound r W V hVcard (y l) (fun j => le_max_left _ _) hsupp hymax
    let sStar : ℕ → ℕ := fun l => min (widthOf cap l) (E - usedOf cap l)
    have hgain_eq : gainOf cap E t = ∑ l ∈ Finset.range E, (sStar l : ℝ) * c l := by
      unfold gainOf
      apply Finset.sum_congr rfl
      intro l _
      simp only [sStar, c, r, Nat.cast_mul, mul_div_assoc]
    have hs_le_w : ∀ l : ℕ, s l ≤ (widthOf cap l : ℝ) := by
      intro l
      let W := (Finset.univ : Finset (Fin q)).filter (fun j => l < cap j)
      have hsumW : s l = ∑ j ∈ W, y l j := by
        symm
        apply Finset.sum_subset (Finset.subset_univ W)
        intro j _ hj
        simp only [W, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
        have hle : x j ≤ (l : ℝ) := le_trans (hxcap j) (by exact_mod_cast hj)
        apply max_eq_left
        exact le_trans (min_le_right _ _) (by linarith)
      rw [hsumW]
      calc ∑ j ∈ W, y l j ≤ ∑ _j ∈ W, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro j _
            exact max_le (by norm_num) (min_le_left _ _)
        _ = (W.card : ℝ) := by simp
        _ = (widthOf cap l : ℝ) := rfl
    have hs_nonneg : ∀ l : ℕ, 0 ≤ s l := fun l => Finset.sum_nonneg (fun j _ => le_max_left _ _)
    have hs_sum : ∑ l ∈ Finset.range E, s l ≤ E := by
      have heq : ∑ l ∈ Finset.range E, s l = ∑ j : Fin q, x j := by
        dsimp only [s]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        exact (hx_eq j).symm
      rw [heq]; exact hxsum
    have hc_anti : Antitone c := fun a b hab => coeff_anti r (widthOf_anti cap hab)
    have hc_nonneg : ∀ l, 0 ≤ c l := fun l => by dsimp only [c]; positivity
    have hstep2 : ∑ l ∈ Finset.range E, s l * c l ≤ ∑ l ∈ Finset.range E, (sStar l : ℝ) * c l := by
      by_cases hused : usedOf cap E ≤ E
      · apply Finset.sum_le_sum
        intro l hl
        rw [Finset.mem_range] at hl
        have hle : usedOf cap l + widthOf cap l ≤ E := by
          rw [← usedOf_succ]
          exact le_trans (usedOf_mono cap (by omega)) hused
        have hsStar_eq : sStar l = widthOf cap l := min_eq_left (by omega)
        rw [hsStar_eq]
        exact mul_le_mul_of_nonneg_right (hs_le_w l) (hc_nonneg l)
      · push Not at hused
        have hex : ∃ l, E < usedOf cap (l + 1) := by
          refine ⟨E - 1, ?_⟩
          have hEpos : 0 < E := by
            by_contra h0
            have hE0 : E = 0 := by omega
            subst hE0
            rw [usedOf_zero] at hused
            omega
          have hrew : E - 1 + 1 = E := by omega
          rw [hrew]; exact hused
        classical
        let L := Nat.find hex
        have hL_gt : E < usedOf cap (L + 1) := Nat.find_spec hex
        have hL_le : usedOf cap L ≤ E := by
          by_cases hL0 : L = 0
          · rw [hL0, usedOf_zero]; exact Nat.zero_le _
          · have hprev := Nat.find_min hex (by omega : L - 1 < L)
            have hrew : L - 1 + 1 = L := by omega
            rw [hrew] at hprev
            omega
        have hL_lt_E : L < E := by
          by_contra hge
          have hle := usedOf_mono cap (by omega : E ≤ L)
          omega
        have hsStar_lt : ∀ l < L, sStar l = widthOf cap l := by
          intro l hl
          have : usedOf cap l + widthOf cap l ≤ usedOf cap L := by
            rw [← usedOf_succ]; exact usedOf_mono cap (by omega)
          exact min_eq_left (by omega)
        have hsStar_eq : sStar L = E - usedOf cap L := by
          have : usedOf cap L + widthOf cap L = usedOf cap (L + 1) := (usedOf_succ cap L).symm
          exact min_eq_right (by omega)
        have hsStar_gt : ∀ l, L < l → sStar l = 0 := by
          intro l hl
          have : usedOf cap (L + 1) ≤ usedOf cap l := usedOf_mono cap (by omega)
          have h0 : E - usedOf cap l = 0 := Nat.sub_eq_zero_of_le (by omega)
          dsimp only [sStar]
          rw [h0]
          exact min_eq_right (Nat.zero_le _)
        have hsum_sStar : ∑ l ∈ Finset.range E, sStar l = E := by
          have hsplit : Finset.range E = Finset.range (L + 1) ∪ (Finset.Ico (L + 1) E) := by
            ext l; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
          rw [hsplit, Finset.sum_union]
          · have h2 : ∑ l ∈ Finset.Ico (L + 1) E, sStar l = 0 := by
              apply Finset.sum_eq_zero
              intro l hl
              exact hsStar_gt l (Finset.mem_Ico.mp hl).1
            rw [h2, add_zero, Finset.sum_range_succ, hsStar_eq]
            have h1 : ∑ l ∈ Finset.range L, sStar l = usedOf cap L := by
              have hcong : ∑ l ∈ Finset.range L, sStar l = ∑ l ∈ Finset.range L, widthOf cap l := by
                apply Finset.sum_congr rfl
                intro l hl
                exact hsStar_lt l (Finset.mem_range.mp hl)
              rw [hcong]
              exact sum_widthOf_eq_usedOf cap L
            rw [h1]
            omega
          · rw [Finset.disjoint_left]
            intro l hl1 hl2
            rw [Finset.mem_range] at hl1
            rw [Finset.mem_Ico] at hl2
            omega
        have hpoint : ∀ l ∈ Finset.range E,
            c L * ((sStar l : ℝ) - s l) ≤ c l * ((sStar l : ℝ) - s l) := by
          intro l hl
          by_cases hlt : l < L
          · rw [hsStar_lt l hlt]
            have hc1 : c L ≤ c l := hc_anti (by omega)
            have hs1 : 0 ≤ (widthOf cap l : ℝ) - s l := by linarith [hs_le_w l]
            nlinarith
          · by_cases heq : l = L
            · subst heq; exact le_refl _
            · rw [hsStar_gt l (by omega), Nat.cast_zero, zero_sub]
              have hc1 : c l ≤ c L := hc_anti (by omega)
              have hs1 : 0 ≤ s l := hs_nonneg l
              nlinarith
        have htot := Finset.sum_le_sum hpoint
        rw [← Finset.mul_sum] at htot
        have hsum_cast : (∑ l ∈ Finset.range E, (sStar l : ℝ)) = (E : ℝ) := by
          exact_mod_cast hsum_sStar
        have hdiff_nonneg : 0 ≤ ∑ l ∈ Finset.range E, ((sStar l : ℝ) - s l) := by
          rw [Finset.sum_sub_distrib, hsum_cast]
          linarith
        have h0le : 0 ≤ ∑ l ∈ Finset.range E, c l * ((sStar l : ℝ) - s l) :=
          le_trans (mul_nonneg (hc_nonneg L) hdiff_nonneg) htot
        have hrew : ∑ l ∈ Finset.range E, c l * ((sStar l : ℝ) - s l) =
            (∑ l ∈ Finset.range E, (sStar l : ℝ) * c l) -
            (∑ l ∈ Finset.range E, s l * c l) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro l _; ring
        linarith
    rw [hgain_eq]
    exact le_trans hstep1 hstep2

private lemma exists_opt_alloc {q E t : ℕ} (hq : 0 < q) (ht : t ≤ q) (cap : Fin q → ℕ) :
    ∃ (p : ℕ) (a : Fin p → Fin q → ℕ),
      0 < p ∧ p ≤ q ∧
      (∀ m j, a m j ≤ cap j) ∧
      (∀ m, ∑ j, a m j ≤ E) ∧
      ∀ U : Finset (Fin q), U.card = t →
        gainOf cap E t ≤
          ((∑ m : Fin p, ((∑ j : Fin q, (a m j : ℝ)) - 2 * ∑ j ∈ Uᶜ, (a m j : ℝ))) / (p : ℝ)) := by
  let r := q - t
  let posL : Finset ℕ := (Finset.range E).filter
    (fun l => 2 * r < widthOf cap l ∧ 0 < min (widthOf cap l) (E - usedOf cap l))
  by_cases hne : posL.Nonempty
  · let lmax := posL.max' hne
    have hlmax_mem : lmax ∈ posL := Finset.max'_mem posL hne
    have hlmax_lt_E : lmax < E := Finset.mem_range.mp (Finset.mem_filter.mp hlmax_mem).1
    have hlmax_w : 2 * r < widthOf cap lmax := (Finset.mem_filter.mp hlmax_mem).2.1
    have hlmax_s : 0 < min (widthOf cap lmax) (E - usedOf cap lmax) := (Finset.mem_filter.mp hlmax_mem).2.2
    let p := widthOf cap lmax
    let s0 := min p (E - usedOf cap lmax)
    have hp_pos : 0 < p := by omega
    have hp_le_q : p ≤ q := by
      have : p ≤ (Finset.univ : Finset (Fin q)).card := Finset.card_le_card (Finset.filter_subset _ _)
      simpa using this
    have hs0_le_p : s0 ≤ p := min_le_left _ _
    let Wmax : Finset (Fin q) := (Finset.univ : Finset (Fin q)).filter (fun j => lmax < cap j)
    have hWmax_card : Wmax.card = p := rfl
    let wl : List (Fin q) := Wmax.toList
    have hwl_len : wl.length = p := by simp [wl, hWmax_card]
    have hwl_nodup : wl.Nodup := Finset.nodup_toList Wmax
    have hwl_mem : ∀ j : Fin q, j ∈ wl ↔ j ∈ Wmax := fun j => Finset.mem_toList
    let pick (m : Fin p) : Finset (Fin q) :=
      (Finset.range s0).image (fun k => wl[(m.val + k) % p]'(by rw [hwl_len]; exact Nat.mod_lt _ hp_pos))
    have hpick_sub : ∀ m : Fin p, pick m ⊆ Wmax := by
      intro m j hj
      rcases Finset.mem_image.mp hj with ⟨k, _, rfl⟩
      exact (hwl_mem _).mp (List.getElem_mem _)
    have hpick_card : ∀ m : Fin p, (pick m).card = s0 := by
      intro m
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro k1 hk1 k2 hk2 heq
      rw [Finset.mem_coe, Finset.mem_range] at hk1 hk2
      have hidx := (List.Nodup.getElem_inj_iff hwl_nodup).mp heq
      have hmod1 : (m.val + k1) % p = (m.val + k2) % p := hidx
      have hk1' : k1 < p := by omega
      have hk2' : k2 < p := by omega
      have hm_lt : m.val < p := m.isLt
      by_cases c1 : m.val + k1 < p <;> by_cases c2 : m.val + k2 < p
      · rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_of_lt c2] at hmod1; omega
      · rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_sub_mod (by omega),
            Nat.mod_eq_of_lt (by omega)] at hmod1; omega
      · rw [Nat.mod_eq_of_lt c2, Nat.mod_eq_sub_mod (by omega),
            Nat.mod_eq_of_lt (by omega)] at hmod1; omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hmod1; omega
    let a : Fin p → Fin q → ℕ := fun m j => min (cap j) lmax + if j ∈ pick m then 1 else 0
    have ha_cap : ∀ m j, a m j ≤ cap j := by
      intro m j
      dsimp only [a]
      split_ifs with hj
      · have hjW := hpick_sub m hj
        have hlt : lmax < cap j := (Finset.mem_filter.mp hjW).2
        omega
      · omega
    have ha_sum : ∀ m, ∑ j, a m j ≤ E := by
      intro m
      dsimp only [a]
      rw [Finset.sum_add_distrib]
      have h1 : ∑ j : Fin q, min (cap j) lmax = usedOf cap lmax := rfl
      have h2 : ∑ j : Fin q, (if j ∈ pick m then 1 else 0) = s0 := by
        rw [Finset.sum_boole, Nat.cast_id]
        have : Finset.univ.filter (fun j : Fin q => j ∈ pick m) = pick m := by ext j; simp
        rw [this, hpick_card m]
      rw [h1, h2]
      have : s0 ≤ E - usedOf cap lmax := min_le_right _ _
      omega
    have hcount_pick : ∀ j : Fin q,
        (Finset.univ.filter (fun m : Fin p => j ∈ pick m)).card = if j ∈ Wmax then s0 else 0 := by
      intro j
      by_cases hj : j ∈ Wmax
      · simp only [hj, ↓reduceIte]
        have hjwl : j ∈ wl := (hwl_mem j).mpr hj
        obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.getElem_of_mem hjwl
        have hidx_p : idx < p := by omega
        have hbij : Finset.univ.filter (fun m : Fin p => j ∈ pick m) =
            (Finset.range s0).image (fun k => (⟨(idx + p - k) % p, Nat.mod_lt _ hp_pos⟩ : Fin p)) := by
          ext m
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_range, pick]
          constructor
          · rintro ⟨k, hk, hget⟩
            refine ⟨k, hk, ?_⟩
            have hmod : (m.val + k) % p = idx := by
              rw [← hidx_eq] at hget
              exact (List.Nodup.getElem_inj_iff hwl_nodup).mp hget
            apply Fin.ext
            dsimp only
            have hk_lt : k < p := by omega
            have hm_lt : m.val < p := m.isLt
            by_cases c1 : m.val + k < p
            · rw [Nat.mod_eq_of_lt c1] at hmod
              have heq2 : idx + p - k = m.val + p := by omega
              rw [heq2, Nat.add_mod_right, Nat.mod_eq_of_lt hm_lt]
            · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
              have heq2 : idx + p - k = m.val := by omega
              rw [heq2, Nat.mod_eq_of_lt hm_lt]
          · rintro ⟨k, hk, rfl⟩
            refine ⟨k, hk, ?_⟩
            dsimp only
            have hk_lt : k < p := by omega
            have hmod : ((idx + p - k) % p + k) % p = idx := by
              rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
              have heq2 : idx + p - k + k = idx + p := by omega
              rw [heq2, Nat.add_mod_right, Nat.mod_eq_of_lt hidx_p]
            simp only [hmod, hidx_eq]
        rw [hbij, Finset.card_image_of_injOn, Finset.card_range]
        intro k1 hk1 k2 hk2 heq
        rw [Finset.mem_coe, Finset.mem_range] at hk1 hk2
        have hval := congrArg Fin.val heq
        dsimp only at hval
        have hk1_lt : k1 < p := by omega
        have hk2_lt : k2 < p := by omega
        by_cases c1 : idx + p - k1 < p <;> by_cases c2 : idx + p - k2 < p
        · rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_of_lt c2] at hval; omega
        · rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_sub_mod (by omega),
              Nat.mod_eq_of_lt (by omega)] at hval; omega
        · rw [Nat.mod_eq_of_lt c2, Nat.mod_eq_sub_mod (by omega),
              Nat.mod_eq_of_lt (by omega)] at hval; omega
        · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
              Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hval; omega
      · simp only [hj, ↓reduceIte]
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro m _ hm
        exact hj (hpick_sub m hm)
    refine ⟨p, a, hp_pos, hp_le_q, ha_cap, ha_sum, ?_⟩
    intro U hU
    let V := Uᶜ
    have hVcard : V.card = r := by rw [Finset.card_compl, Fintype.card_fin, hU]
    have hp_real : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_pos
    let xbar : Fin q → ℝ := fun j => (∑ m : Fin p, (a m j : ℝ)) / (p : ℝ)
    have hxbar_eq : ∀ j : Fin q, xbar j =
        (min (cap j) lmax : ℝ) + (if j ∈ Wmax then (s0 : ℝ) / (p : ℝ) else 0) := by
      intro j
      dsimp only [xbar, a]
      simp_rw [Nat.cast_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      have hsum_ind : ∑ m : Fin p, ((if j ∈ pick m then 1 else 0 : ℕ) : ℝ) =
          if j ∈ Wmax then (s0 : ℝ) else 0 := by
        have hnat : ∑ m : Fin p, (if j ∈ pick m then 1 else 0) =
            (Finset.univ.filter (fun m : Fin p => j ∈ pick m)).card := by
          rw [Finset.sum_boole, Nat.cast_id]
        rw [← Nat.cast_sum, hnat, hcount_pick j]
        split_ifs <;> simp
      rw [hsum_ind, add_div, mul_div_cancel_left₀ _ (ne_of_gt hp_real)]
      split_ifs <;> simp
    have havg_eq :
        ((∑ m : Fin p, ((∑ j : Fin q, (a m j : ℝ)) - 2 * ∑ j ∈ V, (a m j : ℝ))) / (p : ℝ)) =
        (∑ j : Fin q, xbar j) - 2 * (∑ j ∈ V, xbar j) := by
      rw [Finset.sum_sub_distrib, sub_div, ← Finset.mul_sum, mul_div_assoc]
      congr 1
      · rw [Finset.sum_comm]; simp_rw [xbar, div_eq_mul_inv, ← Finset.sum_mul]
      · congr 1; rw [Finset.sum_comm]; simp_rw [xbar, div_eq_mul_inv, ← Finset.sum_mul]
    rw [havg_eq]
    have hmin_sum : ∀ j : Fin q, (min (cap j) lmax : ℝ) =
        ∑ l ∈ Finset.range lmax, (if l < cap j then (1 : ℝ) else 0) := by
      intro j
      have hnat : min (cap j) lmax = ∑ l ∈ Finset.range lmax, (if l < cap j then 1 else 0) := by
        induction lmax with
        | zero => simp
        | succ k ih =>
          rw [Finset.sum_range_succ, ← ih]
          split_ifs <;> omega
      have hmin_cast : (min (cap j) lmax : ℝ) = ((min (cap j) lmax : ℕ) : ℝ) := by simp
      rw [hmin_cast, hnat, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro l _; split_ifs <;> simp
    have hdecomp : (∑ j : Fin q, xbar j) - 2 * (∑ j ∈ V, xbar j) =
        (∑ l ∈ Finset.range lmax,
          ((widthOf cap l : ℝ) - 2 * ((V.filter (fun j => l < cap j)).card : ℝ))) +
        ((s0 : ℝ) / (p : ℝ)) * ((p : ℝ) - 2 * ((V.filter (fun j => lmax < cap j)).card : ℝ)) := by
      simp_rw [hxbar_eq, Finset.sum_add_distrib]
      have hL1 : ∑ j : Fin q, (min (cap j) lmax : ℝ) =
          ∑ l ∈ Finset.range lmax, (widthOf cap l : ℝ) := by
        simp_rw [hmin_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro l _
        rw [Finset.sum_boole]
        rfl
      have hL2 : ∑ j ∈ V, (min (cap j) lmax : ℝ) =
          ∑ l ∈ Finset.range lmax, ((V.filter (fun j => l < cap j)).card : ℝ) := by
        simp_rw [hmin_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro l _
        rw [Finset.sum_boole]
      have hT1 : ∑ j : Fin q, (if j ∈ Wmax then (s0 : ℝ) / (p : ℝ) else 0) =
          ((s0 : ℝ) / (p : ℝ)) * (p : ℝ) := by
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, hWmax_card, mul_comm]
      have hT2 : ∑ j ∈ V, (if j ∈ Wmax then (s0 : ℝ) / (p : ℝ) else 0) =
          ((s0 : ℝ) / (p : ℝ)) * ((V.filter (fun j => lmax < cap j)).card : ℝ) := by
        have hfilt : V.filter (fun j => j ∈ Wmax) = V.filter (fun j => lmax < cap j) := by
          ext j; simp [Wmax]
        rw [Finset.sum_ite_mem, ← Finset.filter_mem_eq_inter, hfilt, Finset.sum_const, nsmul_eq_mul, mul_comm]
      rw [hL1, hL2, hT1, hT2, Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    rw [hdecomp]
    have hgain_split : gainOf cap E t =
        (∑ l ∈ Finset.range lmax, ((widthOf cap l - 2 * r : ℕ) : ℝ)) +
        ((s0 : ℝ) / (p : ℝ)) * ((p - 2 * r : ℕ) : ℝ) := by
      unfold gainOf
      have hsplit : Finset.range E = Finset.range (lmax + 1) ∪ Finset.Ico (lmax + 1) E := by
        ext l; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
      rw [hsplit, Finset.sum_union]
      · have htail : ∑ l ∈ Finset.Ico (lmax + 1) E,
            ((min (widthOf cap l) (E - usedOf cap l) * (widthOf cap l - 2 * r) : ℕ) : ℝ) /
              (widthOf cap l : ℝ) = 0 := by
          apply Finset.sum_eq_zero
          intro l hl
          have hnot : l ∉ posL := fun hm => by
            have hle := Finset.le_max' posL l hm
            have := (Finset.mem_Ico.mp hl).1
            omega
          have hrange : l ∈ Finset.range E := Finset.mem_range.mpr (Finset.mem_Ico.mp hl).2
          simp only [posL, Finset.mem_filter, hrange, true_and, not_and_or, not_lt] at hnot
          rcases hnot with h1 | h2
          · have : widthOf cap l - 2 * r = 0 := Nat.sub_eq_zero_of_le h1
            simp [this]
          · have : min (widthOf cap l) (E - usedOf cap l) = 0 := by omega
            simp [this]
        rw [htail, add_zero, Finset.sum_range_succ]
        congr 1
        · apply Finset.sum_congr rfl
          intro l hl
          rw [Finset.mem_range] at hl
          have hle_used : usedOf cap l + widthOf cap l ≤ usedOf cap lmax := by
            rw [← usedOf_succ]; exact usedOf_mono cap (by omega)
          have hused_lt : usedOf cap lmax < E := by omega
          have hmin : min (widthOf cap l) (E - usedOf cap l) = widthOf cap l :=
            min_eq_left (by omega)
          have hw_pos : 0 < widthOf cap l := by
            have := widthOf_anti cap (by omega : l ≤ lmax)
            omega
          rw [hmin, Nat.cast_mul, mul_div_cancel_left₀ _ (by exact_mod_cast (ne_of_gt hw_pos))]
        · simp only [s0, p, Nat.cast_mul, mul_div_assoc]
          ring
      · rw [Finset.disjoint_left]
        intro l hl1 hl2
        rw [Finset.mem_range] at hl1
        rw [Finset.mem_Ico] at hl2
        omega
    rw [hgain_split]
    apply add_le_add
    · apply Finset.sum_le_sum
      intro l hl
      rw [Finset.mem_range] at hl
      have hw_gt : 2 * r < widthOf cap l := lt_of_lt_of_le hlmax_w (widthOf_anti cap (by omega))
      have hsub : ((widthOf cap l - 2 * r : ℕ) : ℝ) = (widthOf cap l : ℝ) - 2 * (r : ℝ) := by
        have := Nat.cast_sub (R := ℝ) (by omega : 2 * r ≤ widthOf cap l)
        push_cast at this; exact this
      have hfilt_le : (V.filter (fun j => l < cap j)).card ≤ r := by
        rw [← hVcard]; exact Finset.card_le_card (Finset.filter_subset _ _)
      have hfilt_r : ((V.filter (fun j => l < cap j)).card : ℝ) ≤ (r : ℝ) := by exact_mod_cast hfilt_le
      rw [hsub]
      linarith
    · have hsub : ((p - 2 * r : ℕ) : ℝ) = (p : ℝ) - 2 * (r : ℝ) := by
        have := Nat.cast_sub (R := ℝ) (by omega : 2 * r ≤ p)
        push_cast at this; exact this
      have hfilt_le : (V.filter (fun j => lmax < cap j)).card ≤ r := by
        rw [← hVcard]; exact Finset.card_le_card (Finset.filter_subset _ _)
      have hfilt_r : ((V.filter (fun j => lmax < cap j)).card : ℝ) ≤ (r : ℝ) := by exact_mod_cast hfilt_le
      rw [hsub]
      apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have hgain0 : gainOf cap E t = 0 := by
      unfold gainOf
      apply Finset.sum_eq_zero
      intro l hl
      have hnot : l ∉ posL := fun hm => hne ⟨l, hm⟩
      simp only [posL, Finset.mem_filter, hl, true_and, not_and_or, not_lt] at hnot
      rcases hnot with h1 | h2
      · have h0 : widthOf cap l - 2 * (q - t) = 0 := Nat.sub_eq_zero_of_le h1
        simp [h0]
      · have h0 : min (widthOf cap l) (E - usedOf cap l) = 0 := by omega
        simp [h0]
    refine ⟨1, fun _ _ => 0, by omega, hq, fun _ _ => Nat.zero_le _, fun _ => by simp, ?_⟩
    intro U _
    rw [hgain0]
    simp

private def legalGate (g : Gate) : Prop :=
  g.inputs.length ≤ 2 ∧ (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))

private def namedGates {N : ℕ} (R S : Finset (Fin N)) (gs : List Gate) : Prop :=
  (∀ x : Fin N, (∃ g ∈ gs, x.val ∈ g.inputs) → x ∈ R) ∧
  (∀ y : Fin N, (∃ g ∈ gs, N + y.val ∈ g.inputs) → y ∈ S)

private def readsBackList (n0 : ℕ) (gs : List Gate) : Prop :=
  ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨.or, []⟩).inputs, i < n0 + j

private lemma readsBackList_append {n0 : ℕ} {gs extra : List Gate}
    (h1 : readsBackList n0 gs)
    (h2 : ∀ k < extra.length, ∀ i ∈ (extra.getD k ⟨.or, []⟩).inputs, i < n0 + gs.length + k) :
    readsBackList n0 (gs ++ extra) := by
  intro j hj i hi
  rw [List.length_append] at hj
  by_cases hlt : j < gs.length
  · have hget : (gs ++ extra).getD j ⟨.or, []⟩ = gs.getD j ⟨.or, []⟩ := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    rw [hget] at hi
    exact h1 j hlt i hi
  · have hget : (gs ++ extra).getD j ⟨.or, []⟩ = extra.getD (j - gs.length) ⟨.or, []⟩ := by
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega : gs.length ≤ j)]
    rw [hget] at hi
    have hlt2 := h2 (j - gs.length) (by omega) i hi
    omega

private lemma namedGates_append {N : ℕ} {R S : Finset (Fin N)} {gs extra : List Gate}
    (h1 : namedGates R S gs) (h2 : namedGates R S extra) :
    namedGates R S (gs ++ extra) := by
  constructor
  · intro x ⟨g, hg, hmem⟩
    rcases List.mem_append.mp hg with h | h
    · exact h1.1 x ⟨g, h, hmem⟩
    · exact h2.1 x ⟨g, h, hmem⟩
  · intro y ⟨g, hg, hmem⟩
    rcases List.mem_append.mp hg with h | h
    · exact h1.2 y ⟨g, h, hmem⟩
    · exact h2.2 y ⟨g, h, hmem⟩

private lemma namedGates_of_ge {N : ℕ} (R S : Finset (Fin N)) (gs : List Gate)
    (hge : ∀ g ∈ gs, ∀ i ∈ g.inputs, N + N ≤ i) :
    namedGates R S gs := by
  constructor
  · intro x ⟨g, hg, hm⟩
    have := hge g hg x.val hm
    omega
  · intro y ⟨g, hg, hm⟩
    have := hge g hg (N + y.val) hm
    omega

private def tableGatesAux (N : ℕ) (n0 : ℕ) (acc : ℕ) (gs : List Gate) :
    List (Fin N × Fin N) → List Gate × ℕ
  | [] => (gs, acc)
  | (x, y) :: rest =>
    let wAnd := n0 + gs.length
    let wOr := wAnd + 1
    let gs' := gs ++ [⟨.and, [x.val, N + y.val]⟩, ⟨.or, [acc, wAnd]⟩]
    tableGatesAux N n0 wOr gs' rest

private def appendTable (N : ℕ) (n0 : ℕ) (z0 : ℕ) (gs : List Gate) :
    List (Fin N × Fin N) → List Gate × ℕ
  | [] => (gs, z0)
  | (x, y) :: rest =>
    let wFirst := n0 + gs.length
    let gs1 := gs ++ [⟨.and, [x.val, N + y.val]⟩]
    tableGatesAux N n0 wFirst gs1 rest

private lemma tableGatesAux_spec {N h : ℕ} (R S : Finset (Fin N))
    (cells : List (Fin N × Fin N)) (hcells : ∀ p ∈ cells, p.1 ∈ R ∧ p.2 ∈ S)
    (gs : List Gate) (acc : ℕ) (hacc_lt : acc < N + N + h + gs.length)
    (hacc_ge : N + N + h ≤ acc)
    (hRB : readsBackList (N + N + h) gs)
    (hLG : ∀ g ∈ gs, legalGate g)
    (hNG : namedGates R S gs) :
    let res := tableGatesAux N (N + N + h) acc gs cells
    (∃ extra, res.1 = gs ++ extra ∧ extra.length = 2 * cells.length) ∧
    readsBackList (N + N + h) res.1 ∧
    (∀ g ∈ res.1, legalGate g) ∧
    namedGates R S res.1 ∧
    N + N + h ≤ res.2 ∧ res.2 < N + N + h + res.1.length ∧
    ∀ (x0 y0 : Fin N) (w : Fin h → Bool),
      (res.1.foldl stepW (oneEach x0 y0 ++ List.ofFn w)).getD res.2 false =
        ((gs.foldl stepW (oneEach x0 y0 ++ List.ofFn w)).getD acc false ||
          decide ((x0, y0) ∈ cells)) := by
  induction cells generalizing gs acc with
  | nil =>
    refine ⟨⟨[], by simp [tableGatesAux], by simp⟩, hRB, hLG, hNG, hacc_ge, hacc_lt, ?_⟩
    intro x0 y0 w
    simp [tableGatesAux]
  | cons p rest ih =>
    rcases p with ⟨x, y⟩
    have hxy : x ∈ R ∧ y ∈ S := hcells (x, y) (List.mem_cons_self ..)
    have hrest : ∀ q ∈ rest, q.1 ∈ R ∧ q.2 ∈ S := fun q hq => hcells q (List.mem_cons_of_mem _ hq)
    let n0 := N + N + h
    let wAnd := n0 + gs.length
    let wOr := wAnd + 1
    let gAnd : Gate := ⟨.and, [x.val, N + y.val]⟩
    let gOr : Gate := ⟨.or, [acc, wAnd]⟩
    let gs' := gs ++ [gAnd, gOr]
    have hlen' : gs'.length = gs.length + 2 := by simp [gs']
    have hRB' : readsBackList n0 gs' := by
      apply readsBackList_append hRB
      intro k hk i hi
      have hk2 : k = 0 ∨ k = 1 := by simp at hk; omega
      rcases hk2 with rfl | rfl
      · simp only [List.getD_cons_zero, gAnd, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> omega
      · simp only [List.getD_cons_succ, List.getD_cons_zero, gOr, List.mem_cons,
          List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> omega
    have hLG' : ∀ g ∈ gs', legalGate g := by
      intro g hg
      rcases List.mem_append.mp hg with h1 | h2
      · exact hLG g h1
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
        rcases h2 with rfl | rfl <;> simp [legalGate, gAnd, gOr]
    have hNG' : namedGates R S gs' := by
      apply namedGates_append hNG
      constructor
      · intro a ⟨g, hg, hmem⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl
        · simp only [gAnd, List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with h1 | h2
          · have ha : a = x := Fin.ext h1; subst ha; exact hxy.1
          · omega
        · simp only [gOr, List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with h1 | h2 <;> omega
      · intro b ⟨g, hg, hmem⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl
        · simp only [gAnd, List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with h1 | h2
          · omega
          · have hb : b = y := Fin.ext (by omega); subst hb; exact hxy.2
        · simp only [gOr, List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with h1 | h2 <;> omega
    have hspec := ih hrest gs' wOr (by omega) (by omega) hRB' hLG' hNG'
    rcases hspec with ⟨⟨extra, hex, hexlen⟩, hRB_f, hLG_f, hNG_f, hge_f, hlt_f, heval_f⟩
    refine ⟨⟨[gAnd, gOr] ++ extra, ?_, ?_⟩, hRB_f, hLG_f, hNG_f, hge_f, hlt_f, ?_⟩
    · change (tableGatesAux N n0 wOr gs' rest).1 = gs ++ ([gAnd, gOr] ++ extra)
      rw [hex, List.append_assoc]
    · simp [hexlen]; omega
    · intro x0 y0 w
      change ((tableGatesAux N n0 wOr gs' rest).1.foldl stepW (oneEach x0 y0 ++ List.ofFn w)).getD
          (tableGatesAux N n0 wOr gs' rest).2 false = _
      rw [heval_f x0 y0 w]
      let inp := oneEach x0 y0 ++ List.ofFn w
      let W0 := gs.foldl stepW inp
      have hW0_len : W0.length = wAnd := by
        rw [foldl_stepW_len, oneEach_append_len]
      have hW1 : gs'.foldl stepW inp = stepW (stepW W0 gAnd) gOr := by
        simp [gs', W0, List.foldl_append]
      rw [hW1]
      have hW1_len : (stepW W0 gAnd).length = wOr := by
        simp [stepW, hW0_len, wOr]
      have hval_or : (stepW (stepW W0 gAnd) gOr).getD wOr false =
          ((stepW W0 gAnd).getD acc false || (stepW W0 gAnd).getD wAnd false) := by
        rw [← hW1_len, stepW_getD_self]
        simp [gOr, GateOp.eval]
      have hval_acc : (stepW W0 gAnd).getD acc false = W0.getD acc false := by
        have hlt : acc < W0.length := by omega
        simp only [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      have hval_and : (stepW W0 gAnd).getD wAnd false = (decide (x = x0) && decide (y = y0)) := by
        rw [← hW0_len, stepW_getD_self]
        simp only [gAnd, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true]
        have hxlt : x.val < inp.length := by rw [oneEach_append_len]; omega
        have hylt : N + y.val < inp.length := by rw [oneEach_append_len]; omega
        rw [foldl_stepW_getD_lt gs inp x.val hxlt, foldl_stepW_getD_lt gs inp (N + y.val) hylt,
            oneEach_append_getD x0 y0 w x.val (by omega),
            oneEach_append_getD x0 y0 w (N + y.val) (by omega)]
        have hnot : ¬(N + y.val < N) := by omega
        have hlt2 : N + y.val < N + N := by omega
        simp only [x.isLt, ↓reduceDIte, hnot, hlt2]
        have hx_eq : (⟨x.val, x.isLt⟩ : Fin N) = x := rfl
        have hy_eq : (⟨N + y.val - N, by omega⟩ : Fin N) = y := Fin.ext (by simp)
        simp [hx_eq, hy_eq]
      rw [hval_or, hval_acc, hval_and]
      have hpair : (decide (x = x0) && decide (y = y0)) = decide ((x0, y0) = (x, y)) := by
        by_cases h1 : x = x0 <;> by_cases h2 : y = y0 <;> simp [h1, h2, eq_comm]
      have hmem : decide ((x0, y0) ∈ (x, y) :: rest) =
          (decide ((x0, y0) = (x, y)) || decide ((x0, y0) ∈ rest)) := by
        by_cases h1 : (x0, y0) = (x, y) <;> by_cases h2 : (x0, y0) ∈ rest <;> simp [h1, h2]
      rw [hpair, hmem]
      cases W0.getD acc false <;> cases decide ((x0, y0) = (x, y)) <;>
        cases decide ((x0, y0) ∈ rest) <;> rfl

private lemma appendTable_spec {N h : ℕ} (R S : Finset (Fin N))
    (cells : List (Fin N × Fin N)) (hcells : ∀ p ∈ cells, p.1 ∈ R ∧ p.2 ∈ S)
    (gs : List Gate) (z0 : ℕ) (hz0_lt : z0 < N + N + h + gs.length)
    (hz0_ge : N + N + h ≤ z0)
    (hz0_false : ∀ (x0 y0 : Fin N) (w : Fin h → Bool),
      (gs.foldl stepW (oneEach x0 y0 ++ List.ofFn w)).getD z0 false = false)
    (hRB : readsBackList (N + N + h) gs)
    (hLG : ∀ g ∈ gs, legalGate g)
    (hNG : namedGates R S gs) :
    let res := appendTable N (N + N + h) z0 gs cells
    (∃ extra, res.1 = gs ++ extra ∧ extra.length ≤ 2 * cells.length) ∧
    readsBackList (N + N + h) res.1 ∧
    (∀ g ∈ res.1, legalGate g) ∧
    namedGates R S res.1 ∧
    N + N + h ≤ res.2 ∧ res.2 < N + N + h + res.1.length ∧
    ∀ (x0 y0 : Fin N) (w : Fin h → Bool),
      (res.1.foldl stepW (oneEach x0 y0 ++ List.ofFn w)).getD res.2 false =
        decide ((x0, y0) ∈ cells) := by
  cases cells with
  | nil =>
    refine ⟨⟨[], by simp [appendTable], by simp⟩, hRB, hLG, hNG, hz0_ge, hz0_lt, ?_⟩
    intro x0 y0 w
    simpa [appendTable] using hz0_false x0 y0 w
  | cons p rest =>
    rcases p with ⟨x, y⟩
    have hxy : x ∈ R ∧ y ∈ S := hcells (x, y) (List.mem_cons_self ..)
    have hrest : ∀ q ∈ rest, q.1 ∈ R ∧ q.2 ∈ S := fun q hq => hcells q (List.mem_cons_of_mem _ hq)
    let n0 := N + N + h
    let wFirst := n0 + gs.length
    let gAnd : Gate := ⟨.and, [x.val, N + y.val]⟩
    let gs1 := gs ++ [gAnd]
    have hRB1 : readsBackList n0 gs1 := by
      apply readsBackList_append hRB
      intro k hk i hi
      have hk0 : k = 0 := by simp at hk; omega
      subst hk0
      simp only [List.getD_cons_zero, gAnd, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    have hLG1 : ∀ g ∈ gs1, legalGate g := by
      intro g hg
      rcases List.mem_append.mp hg with h1 | h2
      · exact hLG g h1
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
        subst h2; simp [legalGate, gAnd]
    have hNG1 : namedGates R S gs1 := by
      apply namedGates_append hNG
      constructor
      · intro a ⟨g, hg, hmem⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        subst hg
        simp only [gAnd, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h1 | h2
        · have ha : a = x := Fin.ext h1; subst ha; exact hxy.1
        · omega
      · intro b ⟨g, hg, hmem⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        subst hg
        simp only [gAnd, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h1 | h2
        · omega
        · have hb : b = y := Fin.ext (by omega); subst hb; exact hxy.2
    have hspec := tableGatesAux_spec R S rest hrest gs1 wFirst
      (by simp [gs1, wFirst, n0]) (by omega) hRB1 hLG1 hNG1
    rcases hspec with ⟨⟨extra, hex, hexlen⟩, hRB_f, hLG_f, hNG_f, hge_f, hlt_f, heval_f⟩
    refine ⟨⟨[gAnd] ++ extra, ?_, ?_⟩, hRB_f, hLG_f, hNG_f, hge_f, hlt_f, ?_⟩
    · change (tableGatesAux N n0 wFirst gs1 rest).1 = gs ++ ([gAnd] ++ extra)
      rw [hex, List.append_assoc]
    · simp only [List.length_append, List.length_cons, List.length_nil, hexlen]; omega
    · intro x0 y0 w
      change ((tableGatesAux N n0 wFirst gs1 rest).1.foldl stepW (oneEach x0 y0 ++ List.ofFn w)).getD
          (tableGatesAux N n0 wFirst gs1 rest).2 false = _
      rw [heval_f x0 y0 w]
      let inp := oneEach x0 y0 ++ List.ofFn w
      let W0 := gs.foldl stepW inp
      have hW0_len : W0.length = wFirst := by rw [foldl_stepW_len, oneEach_append_len]
      have hval_first : (gs1.foldl stepW inp).getD wFirst false =
          (decide (x = x0) && decide (y = y0)) := by
        rw [show gs1.foldl stepW inp = stepW W0 gAnd by simp [gs1, W0, List.foldl_append]]
        rw [← hW0_len, stepW_getD_self]
        simp only [gAnd, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true]
        have hxlt : x.val < inp.length := by rw [oneEach_append_len]; omega
        have hylt : N + y.val < inp.length := by rw [oneEach_append_len]; omega
        rw [foldl_stepW_getD_lt gs inp x.val hxlt, foldl_stepW_getD_lt gs inp (N + y.val) hylt,
            oneEach_append_getD x0 y0 w x.val (by omega),
            oneEach_append_getD x0 y0 w (N + y.val) (by omega)]
        have hnot : ¬(N + y.val < N) := by omega
        have hlt2 : N + y.val < N + N := by omega
        simp only [x.isLt, ↓reduceDIte, hnot, hlt2]
        have hx_eq : (⟨x.val, x.isLt⟩ : Fin N) = x := rfl
        have hy_eq : (⟨N + y.val - N, by omega⟩ : Fin N) = y := Fin.ext (by simp)
        simp [hx_eq, hy_eq]
      rw [hval_first]
      have hpair : (decide (x = x0) && decide (y = y0)) = decide ((x0, y0) = (x, y)) := by
        by_cases h1 : x = x0 <;> by_cases h2 : y = y0 <;> simp [h1, h2, eq_comm]
      have hmem : decide ((x0, y0) ∈ (x, y) :: rest) =
          (decide ((x0, y0) = (x, y)) || decide ((x0, y0) ∈ rest)) := by
        by_cases h1 : (x0, y0) = (x, y) <;> by_cases h2 : (x0, y0) ∈ rest <;> simp [h1, h2]
      rw [hpair, hmem]

private def appendTables (N n0 z0 : ℕ) :
    List (List (Fin N × Fin N)) → List Gate → List Gate × List ℕ
  | [], gs => (gs, [])
  | cs :: rest, gs =>
    let r1 := appendTable N n0 z0 gs cs
    let r2 := appendTables N n0 z0 rest r1.1
    (r2.1, r1.2 :: r2.2)

private lemma appendTables_spec {N h E : ℕ} (R S : Finset (Fin N))
    (tables : List (List (Fin N × Fin N)))
    (htab_cells : ∀ cs ∈ tables, ∀ p ∈ cs, p.1 ∈ R ∧ p.2 ∈ S)
    (htab_len : ∀ cs ∈ tables, cs.length ≤ E)
    (gs : List Gate) (z0 : ℕ) (hz0_lt : z0 < N + N + h + gs.length)
    (hz0_ge : N + N + h ≤ z0)
    (hz0_false : ∀ (x0 y0 : Fin N) (w : Fin h → Bool),
      (gs.foldl stepW (oneEach x0 y0 ++ List.ofFn w)).getD z0 false = false)
    (hRB : readsBackList (N + N + h) gs)
    (hLG : ∀ g ∈ gs, legalGate g)
    (hNG : namedGates R S gs) :
    let res := appendTables N (N + N + h) z0 tables gs
    (∃ extra, res.1 = gs ++ extra ∧ extra.length ≤ 2 * tables.length * E) ∧
    res.2.length = tables.length ∧
    readsBackList (N + N + h) res.1 ∧
    (∀ g ∈ res.1, legalGate g) ∧
    namedGates R S res.1 ∧
    (∀ k < tables.length, N + N + h ≤ res.2.getD k z0 ∧
      res.2.getD k z0 < N + N + h + res.1.length) ∧
    (∀ (k : ℕ) (hk : k < tables.length) (x0 y0 : Fin N) (w : Fin h → Bool),
      (res.1.foldl stepW (oneEach x0 y0 ++ List.ofFn w)).getD (res.2.getD k z0) false =
        decide ((x0, y0) ∈ tables[k])) := by
  induction tables generalizing gs with
  | nil =>
    refine ⟨⟨[], by simp [appendTables], by simp⟩, rfl, hRB, hLG, hNG, fun _ h => by simp at h, fun _ h => by simp at h⟩
  | cons cs rest ih =>
    have hcs_cells := htab_cells cs (List.mem_cons_self ..)
    have hcs_len := htab_len cs (List.mem_cons_self ..)
    have hsp1 := appendTable_spec R S cs hcs_cells gs z0 hz0_lt hz0_ge hz0_false hRB hLG hNG
    rcases hsp1 with ⟨⟨ex1, hex1, hex1_len⟩, hRB1, hLG1, hNG1, hw1_ge, hw1_lt, heval1⟩
    let r1 := appendTable N (N + N + h) z0 gs cs
    have hz0_lt1 : z0 < N + N + h + r1.1.length := by rw [hex1, List.length_append]; omega
    have hz0_false1 : ∀ (x0 y0 : Fin N) (w : Fin h → Bool),
        (r1.1.foldl stepW (oneEach x0 y0 ++ List.ofFn w)).getD z0 false = false := by
      intro x0 y0 w
      rw [hex1, List.foldl_append, foldl_stepW_getD_lt _ _ z0 (by rw [foldl_stepW_len, oneEach_append_len]; exact hz0_lt)]
      exact hz0_false x0 y0 w
    have hsp2 := ih (fun c hc => htab_cells c (List.mem_cons_of_mem _ hc))
      (fun c hc => htab_len c (List.mem_cons_of_mem _ hc))
      r1.1 hz0_lt1 hz0_false1 hRB1 hLG1 hNG1
    rcases hsp2 with ⟨⟨ex2, hex2, hex2_len⟩, hlen2, hRB2, hLG2, hNG2, hbounds2, heval2⟩
    refine ⟨⟨ex1 ++ ex2, ?_, ?_⟩, ?_, hRB2, hLG2, hNG2, ?_, ?_⟩
    · change (appendTables N (N + N + h) z0 rest r1.1).1 = gs ++ (ex1 ++ ex2)
      rw [hex2, hex1, List.append_assoc]
    · simp only [List.length_append, List.length_cons]
      have : 2 * (rest.length + 1) * E = 2 * E + 2 * rest.length * E := by ring
      omega
    · change (r1.2 :: (appendTables N (N + N + h) z0 rest r1.1).2).length = (cs :: rest).length
      simp [hlen2]
    · intro k hk
      cases k with
      | zero =>
        change N + N + h ≤ r1.2 ∧ r1.2 < N + N + h + (appendTables N (N + N + h) z0 rest r1.1).1.length
        rw [hex2, List.length_append]
        have hge1 : N + N + h ≤ r1.2 := hw1_ge
        have hlt1 : r1.2 < N + N + h + r1.1.length := hw1_lt
        omega
      | succ k' =>
        exact hbounds2 k' (by simp at hk; omega)
    · intro k hk x0 y0 w
      cases k with
      | zero =>
        change ((appendTables N (N + N + h) z0 rest r1.1).1.foldl stepW
          (oneEach x0 y0 ++ List.ofFn w)).getD r1.2 false = decide ((x0, y0) ∈ cs)
        rw [hex2, List.foldl_append,
            foldl_stepW_getD_lt _ _ r1.2 (by rw [foldl_stepW_len, oneEach_append_len]; exact hw1_lt)]
        exact heval1 x0 y0 w
      | succ k' =>
        exact heval2 k' (by simp at hk; omega) x0 y0 w

private def decodeBits {h : ℕ} (d : ℕ) (hd : d ≤ h) (w : Fin h → Bool) : ℕ :=
  ∑ i ∈ Finset.range d, if hlt : i < h then (if w ⟨i, hlt⟩ then 2 ^ i else 0) else 0

private lemma decodeBits_zero {h : ℕ} (w : Fin h → Bool) :
    decodeBits 0 (Nat.zero_le h) w = 0 := by
  simp [decodeBits]

private lemma decodeBits_succ {h d : ℕ} (hd : d + 1 ≤ h) (w : Fin h → Bool) :
    decodeBits (d + 1) hd w =
      decodeBits d (by omega) w + if w ⟨d, by omega⟩ then 2 ^ d else 0 := by
  unfold decodeBits
  rw [Finset.sum_range_succ]
  have hdlt : d < h := by omega
  simp [hdlt]

private lemma decodeBits_lt {h d : ℕ} (hd : d ≤ h) (w : Fin h → Bool) :
    decodeBits d hd w < 2 ^ d := by
  induction d with
  | zero => simp [decodeBits_zero]
  | succ d ih =>
    rw [decodeBits_succ hd w, pow_succ]
    have hlt := ih (by omega)
    split_ifs <;> omega

private lemma decodeBits_code {h : ℕ} (d : ℕ) (hd : d ≤ h) (j : ℕ) :
    decodeBits d hd (fun i : Fin h => j.testBit i.val) = j % 2 ^ d := by
  induction d with
  | zero => simp [decodeBits_zero, Nat.mod_one]
  | succ d ih =>
    rw [decodeBits_succ hd, ih (by omega)]
    have hmod : j % 2 ^ (d + 1) = j % 2 ^ d + (if j.testBit d then 2 ^ d else 0) := by
      have hdiv : j % 2 ^ (d + 1) = j % 2 ^ d + 2 ^ d * ((j / 2 ^ d) % 2) := by
        have h1 := Nat.div_add_mod j (2 ^ d)
        have h2 := Nat.div_add_mod (j / 2 ^ d) 2
        have h3 : j = 2 ^ (d + 1) * ((j / 2 ^ d) / 2) + (j % 2 ^ d + 2 ^ d * ((j / 2 ^ d) % 2)) := by
          calc j = 2 ^ d * (j / 2 ^ d) + j % 2 ^ d := h1.symm
            _ = 2 ^ d * (2 * (j / 2 ^ d / 2) + j / 2 ^ d % 2) + j % 2 ^ d := by rw [h2]
            _ = 2 ^ (d + 1) * (j / 2 ^ d / 2) + (j % 2 ^ d + 2 ^ d * (j / 2 ^ d % 2)) := by
                rw [pow_succ]; ring
        have hlt : j % 2 ^ d + 2 ^ d * ((j / 2 ^ d) % 2) < 2 ^ (d + 1) := by
          have ha : j % 2 ^ d < 2 ^ d := Nat.mod_lt j (by positivity)
          have hb : (j / 2 ^ d) % 2 ≤ 1 := by omega
          have hmul : 2 ^ d * ((j / 2 ^ d) % 2) ≤ 2 ^ d := by
            calc 2 ^ d * ((j / 2 ^ d) % 2) ≤ 2 ^ d * 1 := Nat.mul_le_mul_left _ hb
              _ = 2 ^ d := mul_one _
          rw [pow_succ]; omega
        conv_lhs => rw [h3]
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
      rw [hdiv, Nat.testBit_eq_decide_div_mod_eq]
      have h2mod : (j / 2 ^ d) % 2 = 0 ∨ (j / 2 ^ d) % 2 = 1 := by omega
      rcases h2mod with hzero | hone
      · simp [hzero]
      · simp [hone]
    exact hmod.symm

private def buildMux (N h : ℕ) (leaf : ℕ → ℕ) :
    (d : ℕ) → ℕ → List Gate → List Gate × ℕ
  | 0, base, gs => (gs, leaf base)
  | d + 1, base, gs =>
    let rL := buildMux N h leaf d base gs
    let rR := buildMux N h leaf d (base + 2 ^ d) rL.1
    let n0 := N + N + h
    let wNot := n0 + 1 + d
    let wBit := N + N + d
    let w1 := n0 + rR.1.length
    let w2 := w1 + 1
    let w3 := w1 + 2
    let gs' := rR.1 ++ [⟨.and, [wNot, rL.2]⟩, ⟨.and, [wBit, rR.2]⟩, ⟨.or, [w1, w2]⟩]
    (gs', w3)

private lemma buildMux_spec {N h : ℕ} (R S : Finset (Fin N)) (leaf : ℕ → ℕ)
    (d : ℕ) (hd : d ≤ h) (base : ℕ) (gs : List Gate)
    (hleaf_lt : ∀ m, leaf m < N + N + h + gs.length)
    (hleaf_ge : ∀ m, N + N + h ≤ leaf m)
    (hnot_lt : ∀ i < h, N + N + h + 1 + i < N + N + h + gs.length)
    (hnot_eval : ∀ (i : Fin h) (x0 y0 : Fin N) (w : Fin h → Bool),
      (gs.foldl stepW (oneEach x0 y0 ++ List.ofFn w)).getD (N + N + h + 1 + i.val) false = !w i)
    (hRB : readsBackList (N + N + h) gs)
    (hLG : ∀ g ∈ gs, legalGate g)
    (hNG : namedGates R S gs) :
    let res := buildMux N h leaf d base gs
    (∃ extra, res.1 = gs ++ extra ∧ extra.length = 3 * (2 ^ d - 1)) ∧
    readsBackList (N + N + h) res.1 ∧
    (∀ g ∈ res.1, legalGate g) ∧
    namedGates R S res.1 ∧
    N + N + h ≤ res.2 ∧ res.2 < N + N + h + res.1.length ∧
    ∀ (x0 y0 : Fin N) (w : Fin h → Bool),
      (res.1.foldl stepW (oneEach x0 y0 ++ List.ofFn w)).getD res.2 false =
        (gs.foldl stepW (oneEach x0 y0 ++ List.ofFn w)).getD (leaf (base + decodeBits d hd w)) false := by
  induction d generalizing base gs with
  | zero =>
    refine ⟨⟨[], by simp [buildMux], by simp⟩, hRB, hLG, hNG, hleaf_ge base, hleaf_lt base, ?_⟩
    intro x0 y0 w
    simp [buildMux, decodeBits_zero]
  | succ d ih =>
    let n0 := N + N + h
    have hspL := ih (by omega) base gs hleaf_lt hnot_lt hnot_eval hRB hLG hNG
    rcases hspL with ⟨⟨exL, hexL, hexL_len⟩, hRBL, hLGL, hNGL, hgeL, hltL, hevalL⟩
    let rL := buildMux N h leaf d base gs
    have hexL' : rL.1 = gs ++ exL := hexL
    have hgeL' : n0 ≤ rL.2 := hgeL
    have hltL' : rL.2 < n0 + rL.1.length := hltL
    have hleaf_ltL : ∀ m, leaf m < n0 + rL.1.length := fun m => by
      rw [hexL', List.length_append]; have := hleaf_lt m; omega
    have hnot_ltL : ∀ i < h, n0 + 1 + i < n0 + rL.1.length := fun i hi => by
      rw [hexL', List.length_append]; have := hnot_lt i hi; omega
    have hnot_evalL : ∀ (i : Fin h) (x0 y0 : Fin N) (w : Fin h → Bool),
        (rL.1.foldl stepW (oneEach x0 y0 ++ List.ofFn w)).getD (n0 + 1 + i.val) false = !w i := by
      intro i x0 y0 w
      rw [hexL', List.foldl_append,
          foldl_stepW_getD_lt _ _ _ (by rw [foldl_stepW_len, oneEach_append_len]; exact hnot_lt i.val i.isLt)]
      exact hnot_eval i x0 y0 w
    have hspR := ih (by omega) (base + 2 ^ d) rL.1 hleaf_ltL hnot_ltL hnot_evalL hRBL hLGL hNGL
    rcases hspR with ⟨⟨exR, hexR, hexR_len⟩, hRBR, hLGR, hNGR, hgeR, hltR, hevalR⟩
    let rR := buildMux N h leaf d (base + 2 ^ d) rL.1
    have hexR' : rR.1 = rL.1 ++ exR := hexR
    have hgeR' : n0 ≤ rR.2 := hgeR
    have hltR' : rR.2 < n0 + rR.1.length := hltR
    let wNot := n0 + 1 + d
    let wBit := N + N + d
    let w1 := n0 + rR.1.length
    let w2 := w1 + 1
    let w3 := w1 + 2
    let g1 : Gate := ⟨.and, [wNot, rL.2]⟩
    let g2 : Gate := ⟨.and, [wBit, rR.2]⟩
    let g3 : Gate := ⟨.or, [w1, w2]⟩
    let gs' := rR.1 ++ [g1, g2, g3]
    have hwNot_lt : wNot < n0 + rR.1.length := by
      rw [hexR', List.length_append]; have := hnot_ltL d (by omega); omega
    have hrL_ltR : rL.2 < n0 + rR.1.length := by
      rw [hexR', List.length_append]; omega
    have hRB' : readsBackList n0 gs' := by
      have hRBR' : readsBackList n0 rR.1 := hRBR
      apply readsBackList_append hRBR'
      intro k hk i hi
      have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by simp at hk; omega
      rcases hk3 with rfl | rfl | rfl
      · simp only [List.getD_cons_zero, g1, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> dsimp only [n0, wNot, wBit, w1, w2, w3] at * <;> omega
      · simp only [List.getD_cons_succ, List.getD_cons_zero, g2, List.mem_cons,
          List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> dsimp only [n0, wNot, wBit, w1, w2, w3] at * <;> omega
      · simp only [List.getD_cons_succ, List.getD_cons_zero, g3, List.mem_cons,
          List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> dsimp only [n0, wNot, wBit, w1, w2, w3] at * <;> omega
    have hLG' : ∀ g ∈ gs', legalGate g := by
      intro g hg
      rcases List.mem_append.mp hg with h1 | h2
      · exact hLGR g h1
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
        rcases h2 with rfl | rfl | rfl <;> simp [legalGate, g1, g2, g3]
    have hNG' : namedGates R S gs' := by
      apply namedGates_append hNGR
      apply namedGates_of_ge
      intro g hg i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      · simp only [g1, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> dsimp only [n0, wNot, wBit, w1, w2, w3] at * <;> omega
      · simp only [g2, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> dsimp only [n0, wNot, wBit, w1, w2, w3] at * <;> omega
      · simp only [g3, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> dsimp only [n0, wNot, wBit, w1, w2, w3] at * <;> omega
    refine ⟨⟨exL ++ exR ++ [g1, g2, g3], ?_, ?_⟩, hRB', hLG', hNG',
      by change n0 ≤ w3; dsimp only [n0, w1, w3]; omega,
      by change w3 < n0 + gs'.length; simp only [gs', List.length_append, List.length_cons, List.length_nil]; dsimp only [n0, w1, w3]; omega, ?_⟩
    · change gs' = gs ++ (exL ++ exR ++ [g1, g2, g3])
      simp only [gs', hexR', hexL', List.append_assoc]
    · simp only [List.length_append, List.length_cons, List.length_nil, hexL_len, hexR_len]
      have hp1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
      rw [pow_succ]; omega
    · intro x0 y0 w
      change (gs'.foldl stepW (oneEach x0 y0 ++ List.ofFn w)).getD w3 false = _
      let inp := oneEach x0 y0 ++ List.ofFn w
      let WR := rR.1.foldl stepW inp
      have hWR_len : WR.length = w1 := by rw [foldl_stepW_len, oneEach_append_len]
      have hstep3 : gs'.foldl stepW inp = stepW (stepW (stepW WR g1) g2) g3 := by
        simp [gs', WR, List.foldl_append]
      rw [hstep3]
      have hlen1 : (stepW WR g1).length = w2 := by simp [stepW, hWR_len, w2]
      have hlen2 : (stepW (stepW WR g1) g2).length = w3 := by rw [stepW, List.length_append, hlen1]; simp [w3, w2]
      have hv3 : (stepW (stepW (stepW WR g1) g2) g3).getD w3 false =
          ((stepW (stepW WR g1) g2).getD w1 false || (stepW (stepW WR g1) g2).getD w2 false) := by
        rw [← hlen2, stepW_getD_self]
        simp [g3, GateOp.eval]
      have hv1_in2 : (stepW (stepW WR g1) g2).getD w1 false = (stepW WR g1).getD w1 false := by
        have hlt : w1 < (stepW WR g1).length := by rw [hlen1]; dsimp only [w1, w2]; omega
        rw [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD]
      have hv1 : (stepW WR g1).getD w1 false = (WR.getD wNot false && WR.getD rL.2 false) := by
        rw [← hWR_len, stepW_getD_self]
        simp [g1, GateOp.eval]
      have hv2 : (stepW (stepW WR g1) g2).getD w2 false =
          ((stepW WR g1).getD wBit false && (stepW WR g1).getD rR.2 false) := by
        rw [← hlen1, stepW_getD_self]
        simp [g2, GateOp.eval]
      have hbit_eq : (stepW WR g1).getD wBit false = w ⟨d, by omega⟩ := by
        have hlt1 : wBit < WR.length := by rw [hWR_len]; dsimp only [w1, wBit, n0]; omega
        rw [show (stepW WR g1).getD wBit false = WR.getD wBit false by
              rw [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt1, ← List.getD_eq_getElem?_getD],
            foldl_stepW_getD_lt _ _ wBit (by rw [oneEach_append_len]; dsimp only [wBit]; omega),
            oneEach_append_getD x0 y0 w wBit (by dsimp only [wBit]; omega)]
        have h1 : ¬(wBit < N) := by dsimp only [wBit]; omega
        have h2 : ¬(wBit < N + N) := by dsimp only [wBit]; omega
        simp only [h1, h2, ↓reduceDIte]
        congr 1; apply Fin.ext; simp [wBit]
      have hrR_eq : (stepW WR g1).getD rR.2 false = WR.getD rR.2 false := by
        have hlt1 : rR.2 < WR.length := by rw [hWR_len]; dsimp only [w1]; exact hltR'
        rw [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt1, ← List.getD_eq_getElem?_getD]
      have hnot_eq : WR.getD wNot false = !w ⟨d, by omega⟩ := by
        change (rR.1.foldl stepW inp).getD wNot false = !w ⟨d, by omega⟩
        rw [hexR', List.foldl_append,
            foldl_stepW_getD_lt _ _ wNot (by rw [foldl_stepW_len, oneEach_append_len]; exact hnot_ltL d (by omega))]
        exact hnot_evalL ⟨d, by omega⟩ x0 y0 w
      have hrL_val : WR.getD rL.2 false =
          (gs.foldl stepW inp).getD (leaf (base + decodeBits d (by omega) w)) false := by
        change (rR.1.foldl stepW inp).getD rL.2 false = _
        rw [hexR', List.foldl_append,
            foldl_stepW_getD_lt _ _ rL.2 (by rw [foldl_stepW_len, oneEach_append_len]; exact hltL')]
        exact hevalL x0 y0 w
      have hrR_val : WR.getD rR.2 false =
          (gs.foldl stepW inp).getD (leaf (base + 2 ^ d + decodeBits d (by omega) w)) false := by
        change (rR.1.foldl stepW inp).getD rR.2 false = _
        rw [hevalR x0 y0 w, hexL', List.foldl_append,
            foldl_stepW_getD_lt _ _ _ (by rw [foldl_stepW_len, oneEach_append_len]; exact hleaf_lt _)]
      rw [hv3, hv1_in2, hv1, hv2, hbit_eq, hrR_eq, hnot_eq, hrL_val, hrR_val, decodeBits_succ hd w]
      cases hwd : w ⟨d, by omega⟩
      · simp only [Bool.not_false, Bool.true_and, Bool.false_and, Bool.or_false, ↓reduceIte, Nat.add_zero]
        rfl
      · simp only [Bool.not_true, Bool.false_and, Bool.true_and, Bool.false_or, ↓reduceIte]
        have hrew : base + 2 ^ d + decodeBits d (by omega) w =
            base + (decodeBits d (by omega) w + 2 ^ d) := by omega
        rw [hrew]

private lemma exists_bitwidth (p : ℕ) (hp : 0 < p) : ∃ h : ℕ, p ≤ 2 ^ h ∧ 2 ^ h ≤ 2 * p := by
  by_cases hp1 : p = 1
  · exact ⟨0, by omega, by omega⟩
  · refine ⟨Nat.log 2 (p - 1) + 1, ?_, ?_⟩
    · have hlt : p - 1 < 2 ^ (Nat.log 2 (p - 1) + 1) := Nat.lt_pow_succ_log_self (by omega) (p - 1)
      omega
    · have hle : 2 ^ Nat.log 2 (p - 1) ≤ p - 1 := Nat.pow_log_le_self 2 (by omega)
      rw [pow_succ]
      omega

end PEqualNP.Outside.L_meta_32013_aux

open PEqualNP.Outside.L_meta_32013_aux PEqualNP.CircuitLowerBounds PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_32013 : (∀ (N q E t : ℕ), 0 < N → 0 < q → t ≤ q →
  let X := Fin N
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (h : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N+h) C ∧ C.output < N+N+h+C.size ∧
    ∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))
  let uses := fun (C : Circ) (j : ℕ) => C.output = j ∨ ∃ g ∈ C.gates, j ∈ g.inputs
  let named := fun (C : Circ) (R S : Finset X) =>
    (∀ x : X, uses C x.val → x ∈ R) ∧ (∀ y : X, uses C (N+y.val) → y ∈ S)
  let table := fun (h : ℕ) (C : Circ) (w : Fin h → Bool) (x y : X) =>
    C.eval (PEqualNP.Represents.oneEach x y ++ List.ofFn w)
  let code := fun (h j : ℕ) (i : Fin h) => j.testBit i.val
  let I := Fin q
  ∀ (f : I → Equiv.Perm X), (∀ x : X, Function.Injective (fun j => f j x)) →
  ∀ R S : Finset X, R.card+E < N → S.card+E < N →
    let cap := fun j : I => (R.filter (fun x => f j x ∈ S)).card
    let width := fun l : ℕ => ((Finset.univ : Finset I).filter (fun j => l < cap j)).card
    let used := fun l : ℕ => ∑ j : I, min (cap j) l
    let gain := ∑ l ∈ Finset.range E,
      ((min (width l) (E-used l) * (width l-2*(q-t)) : ℕ) : ℝ)/(width l : ℝ)
    let value := ((N*t : ℕ) : ℝ) - gain
    let loss := fun (H : X → X → Bool) (U : Finset I) =>
      ((Finset.univ : Finset (X × X)).filter (fun z =>
        H z.1 z.2 ≠ decide (z.2 ∈ U.image (fun j => f j z.1)))).card
    let fits := fun (h : ℕ) (C : Circ) =>
      legal h C ∧ named C R S ∧ ∀ w : Fin h → Bool, loss (table h C w) ∅ ≤ E
    (∀ (h : ℕ) (C : Circ) (P : (Fin h → Bool) → ℝ),
      fits h C → (∀ w, 0 ≤ P w) → (∑ w, P w) = 1 →
      ∃ U : Finset I, U.card = t ∧ value ≤ ∑ w, P w * (loss (table h C w) U : ℝ)) ∧
    ∃ (p h : ℕ) (C : Circ), 0 < p ∧ p ≤ q ∧ p ≤ 2^h ∧ 2^h ≤ 2*p ∧
      fits h C ∧ C.size ≤ 2*p*E+8*p+h+2 ∧
      ∀ U : Finset I, U.card = t →
        (∑ j : Fin p, (loss (table h C (code h j.val)) U : ℝ))/(p : ℝ) ≤ value) := by
  intro N q E t hN hq ht X Circ legal uses named table code I f hf R S hR hS
    cap width used gain value loss fits
  constructor
  ·
    intro h C P hfits hP0 hPsum
    rcases hfits with ⟨⟨hRB, _, _⟩, ⟨hNameR, hNameS⟩, hE⟩
    let x : Fin q → ℝ := fun j => ∑ w : Fin h → Bool, P w * (matchCount f (table h C w) j : ℝ)
    have hsupp : ∀ w x0 y0, table h C w x0 y0 = true → x0 ∈ R ∧ y0 ∈ S := by
      intro w x0 y0 hxy
      have hcard : totalOnes (table h C w) ≤ E := by
        rw [← lossFun_empty f]; exact hE w
      exact table_supp_rect hR hS C w hRB hNameR hNameS hcard x0 y0 hxy
    have hx0 : ∀ j, 0 ≤ x j := fun j =>
      Finset.sum_nonneg (fun w _ => mul_nonneg (hP0 w) (Nat.cast_nonneg _))
    have hxcap : ∀ j, x j ≤ cap j := by
      intro j
      calc x j = ∑ w, P w * (matchCount f (table h C w) j : ℝ) := rfl
        _ ≤ ∑ w, P w * (cap j : ℝ) := by
            apply Finset.sum_le_sum
            intro w _
            apply mul_le_mul_of_nonneg_left _ (hP0 w)
            exact_mod_cast matchCount_le_cap f R S (table h C w) (hsupp w) j
        _ = (∑ w, P w) * (cap j : ℝ) := (Finset.sum_mul _ _ _).symm
        _ = (cap j : ℝ) := by rw [hPsum, one_mul]
    have hxsum : ∑ j, x j ≤ E := by
      calc ∑ j, x j = ∑ w, P w * ∑ j, (matchCount f (table h C w) j : ℝ) := by
            dsimp only [x]; rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro w _; rw [← Finset.mul_sum]
        _ ≤ ∑ w, P w * (E : ℝ) := by
            apply Finset.sum_le_sum
            intro w _
            apply mul_le_mul_of_nonneg_left _ (hP0 w)
            have h1 := sum_matchCount_le_totalOnes f hf (table h C w)
            have h2 : totalOnes (table h C w) ≤ E := by rw [← lossFun_empty f]; exact hE w
            have h3 : ∑ j : Fin q, matchCount f (table h C w) j ≤ E := le_trans h1 h2
            exact_mod_cast h3
        _ = (∑ w, P w) * (E : ℝ) := (Finset.sum_mul _ _ _).symm
        _ = (E : ℝ) := by rw [hPsum, one_mul]
    obtain ⟨U, hUcard, hUbound⟩ := capped_alloc_lower ht cap x hx0 hxcap hxsum
    refine ⟨U, hUcard, ?_⟩
    have hexpand : ∑ w, P w * (loss (table h C w) U : ℝ) =
        ((N * t : ℕ) : ℝ) +
          (∑ w, P w * (totalOnes (table h C w) : ℝ)) - 2 * ∑ j ∈ U, x j := by
      have hterm : ∀ w, P w * (loss (table h C w) U : ℝ) =
          P w * ((N * t : ℕ) : ℝ) + P w * (totalOnes (table h C w) : ℝ) -
            2 * ∑ j ∈ U, P w * (matchCount f (table h C w) j : ℝ) := by
        intro w
        have heq := lossFun_eq_real f hf (table h C w) U
        rw [hUcard] at heq
        change P w * (lossFun f (table h C w) U : ℝ) = _
        rw [heq]
        have hmul : P w * (2 * ∑ j ∈ U, (matchCount f (table h C w) j : ℝ)) =
            2 * ∑ j ∈ U, P w * (matchCount f (table h C w) j : ℝ) := by
          rw [← mul_assoc, mul_comm (P w) 2, mul_assoc, Finset.mul_sum]
        linarith
      simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, hPsum,
        one_mul]
      congr 1
      rw [← Finset.mul_sum]
      congr 1
      dsimp only [x]
      rw [Finset.sum_comm]
    rw [hexpand]
    have hones_ge : ∑ j, x j ≤ ∑ w, P w * (totalOnes (table h C w) : ℝ) := by
      calc ∑ j, x j = ∑ w, P w * ∑ j, (matchCount f (table h C w) j : ℝ) := by
            dsimp only [x]; rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro w _; rw [← Finset.mul_sum]
        _ ≤ ∑ w, P w * (totalOnes (table h C w) : ℝ) := by
            apply Finset.sum_le_sum
            intro w _
            apply mul_le_mul_of_nonneg_left _ (hP0 w)
            exact_mod_cast sum_matchCount_le_totalOnes f hf (table h C w)
    have hsplit_x : ∑ j : Fin q, x j = (∑ j ∈ U, x j) + (∑ j ∈ Uᶜ, x j) :=
      (Finset.sum_add_sum_compl U x).symm
    have hgain_eq : gainOf cap E t = gain := rfl
    rw [hgain_eq] at hUbound
    change ((N * t : ℕ) : ℝ) - gain ≤ _
    linarith
  ·
    obtain ⟨p, a, hp_pos, hp_le_q, ha_cap, ha_sum, ha_opt⟩ := exists_opt_alloc hq ht cap
    obtain ⟨h, hp_le_pow, hpow_le_2p⟩ := exists_bitwidth p hp_pos
    let n0 := N + N + h

    let cellsOf : Fin p → List (Fin N × Fin N) := fun m =>
      (List.finRange q).flatMap fun j =>
        (((R.filter (fun x => f j x ∈ S)).toList).take (a m j)).map (fun x => (x, f j x))
    have hcells_RS : ∀ m p0, p0 ∈ cellsOf m → p0.1 ∈ R ∧ p0.2 ∈ S := by
      intro m p0 hp0
      simp only [cellsOf, List.mem_flatMap, List.mem_map] at hp0
      rcases hp0 with ⟨j, _, x, hx, rfl⟩
      have hx' := Finset.mem_toList.mp (List.mem_of_mem_take hx)
      exact Finset.mem_filter.mp hx'
    have hcells_len : ∀ m, (cellsOf m).length ≤ E := by
      intro m
      have hlen : (cellsOf m).length = ∑ j : Fin q, a m j := by
        dsimp only [cellsOf]
        rw [List.length_flatMap]
        have hsum_list : ∀ l : List (Fin q),
            (l.map fun j => ((((R.filter (fun x => f j x ∈ S)).toList).take (a m j)).map
              (fun x => (x, f j x))).length).sum = (l.map fun j => a m j).sum := by
          intro l
          congr 1
          apply List.map_congr_left
          intro j _
          rw [List.length_map, List.length_take]
          have hcard : ((R.filter (fun x => f j x ∈ S)).toList).length = cap j :=
            Finset.length_toList _
          rw [hcard]
          exact min_eq_left (ha_cap m j)
        rw [hsum_list, ← Fin.sum_univ_def]
      rw [hlen]
      exact ha_sum m
    have hcells_mem_iff : ∀ m j x,
        (x, f j x) ∈ cellsOf m ↔ x ∈ ((R.filter (fun z => f j z ∈ S)).toList).take (a m j) := by
      intro m j x
      simp only [cellsOf, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨j', _, x', hx', hpair⟩
        rcases Prod.mk.inj hpair with ⟨rfl, hf_eq⟩
        have hjeq : j' = j := hf x' hf_eq
        subst hjeq
        exact hx'
      · intro hx
        exact ⟨j, List.mem_finRange j, x, hx, rfl⟩
    have hcells_matchCount : ∀ m j,
        matchCount f (fun x y => decide ((x, y) ∈ cellsOf m)) j = a m j := by
      intro m j
      unfold matchCount
      have hfilt : Finset.univ.filter (fun x : Fin N => decide ((x, f j x) ∈ cellsOf m) = true) =
          (((R.filter (fun z => f j z ∈ S)).toList).take (a m j)).toFinset := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, List.mem_toFinset]
        exact hcells_mem_iff m j x
      rw [hfilt, List.toFinset_card_of_nodup ((Finset.nodup_toList _).take), List.length_take]
      have hcard : ((R.filter (fun z => f j z ∈ S)).toList).length = cap j := Finset.length_toList _
      rw [hcard]
      exact min_eq_left (ha_cap m j)
    have hcells_totalOnes : ∀ m,
        totalOnes (fun x y => decide ((x, y) ∈ cellsOf m)) = ∑ j : Fin q, a m j := by
      intro m
      have hge := sum_matchCount_le_totalOnes f hf (fun x y => decide ((x, y) ∈ cellsOf m))
      simp_rw [hcells_matchCount] at hge
      have hle : totalOnes (fun x y => decide ((x, y) ∈ cellsOf m)) ≤ (cellsOf m).length := by
        unfold totalOnes
        have hsub : Finset.univ.filter (fun z : Fin N × Fin N => decide (z ∈ cellsOf m) = true) ⊆
            (cellsOf m).toFinset := by
          intro z hz; simp only [Finset.mem_filter, decide_eq_true_eq] at hz; exact List.mem_toFinset.mpr hz.2
        exact le_trans (Finset.card_le_card hsub) (List.toFinset_card_le _)
      have hlen : (cellsOf m).length = ∑ j : Fin q, a m j := by
        dsimp only [cellsOf]
        rw [List.length_flatMap]
        have hsum_list : ∀ l : List (Fin q),
            (l.map fun j => ((((R.filter (fun x => f j x ∈ S)).toList).take (a m j)).map
              (fun x => (x, f j x))).length).sum = (l.map fun j => a m j).sum := by
          intro l; congr 1; apply List.map_congr_left; intro j _
          rw [List.length_map, List.length_take, Finset.length_toList]
          exact min_eq_left (ha_cap m j)
        rw [hsum_list, ← Fin.sum_univ_def]
      omega

    let gs0 : List Gate := ⟨.or, []⟩ :: (List.finRange h).map (fun i => ⟨.not, [N + N + i.val]⟩)
    have hgs0_len : gs0.length = 1 + h := by simp [gs0]; omega
    have hRB0 : readsBackList n0 gs0 := by
      intro j hj i hi
      cases j with
      | zero => simp [gs0] at hi
      | succ j' =>
        have hj' : j' < h := by simp [gs0] at hj; omega
        have hget : gs0.getD (j' + 1) ⟨.or, []⟩ = ⟨.not, [N + N + j']⟩ := by
          change ((⟨.or, []⟩ : Gate) ::
            (List.finRange h).map (fun i => ⟨.not, [N + N + i.val]⟩)).getD (j' + 1) ⟨.or, []⟩ = _
          rw [List.getD_cons_succ, List.getD_eq_getElem?_getD,
              List.getElem?_map, List.getElem?_eq_getElem (by simp [hj'])]
          simp
        rw [hget] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        omega
    have hLG0 : ∀ g ∈ gs0, legalGate g := by
      intro g hg
      simp only [gs0, List.mem_cons, List.mem_map] at hg
      rcases hg with rfl | ⟨i, _, rfl⟩ <;> simp [legalGate]
    have hNG0 : namedGates R S gs0 := by
      apply namedGates_of_ge
      intro g hg i hi
      simp only [gs0, List.mem_cons, List.mem_map] at hg
      rcases hg with rfl | ⟨k, _, rfl⟩
      · simp at hi
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega
    have hz0_false : ∀ (x0 y0 : Fin N) (w : Fin h → Bool),
        (gs0.foldl stepW (oneEach x0 y0 ++ List.ofFn w)).getD n0 false = false := by
      intro x0 y0 w
      let inp := oneEach x0 y0 ++ List.ofFn w
      change ((((⟨.or, []⟩ : Gate) ::
        (List.finRange h).map (fun i => ⟨.not, [N + N + i.val]⟩)).foldl stepW inp)).getD n0 false = false
      have hlen : inp.length = n0 := oneEach_append_len x0 y0 w
      rw [List.foldl_cons, foldl_stepW_getD_lt _ _ n0 (by rw [stepW, List.length_append, hlen]; simp)]
      rw [← hlen, stepW_getD_self]
      simp [GateOp.eval]
    have hnot_eval0 : ∀ (i : Fin h) (x0 y0 : Fin N) (w : Fin h → Bool),
        (gs0.foldl stepW (oneEach x0 y0 ++ List.ofFn w)).getD (n0 + 1 + i.val) false = !w i := by
      intro i x0 y0 w
      let inp := oneEach x0 y0 ++ List.ofFn w
      have htake : gs0 = gs0.take (1 + i.val) ++ [⟨.not, [N + N + i.val]⟩] ++ gs0.drop (2 + i.val) := by
        have hlt : 1 + i.val < gs0.length := by rw [hgs0_len]; omega
        have h1 := List.take_append_drop (1 + i.val) gs0
        have h2 : gs0.drop (1 + i.val) = gs0[1 + i.val] :: gs0.drop (2 + i.val) := by
          rw [List.drop_eq_getElem_cons hlt, show 1 + i.val + 1 = 2 + i.val by omega]
        have hget : gs0[1 + i.val] = ⟨.not, [N + N + i.val]⟩ := by
          have hrew : 1 + i.val = i.val + 1 := by omega
          simp [gs0, hrew]
        rw [h2, hget] at h1
        simpa [List.append_assoc] using h1.symm
      rw [htake, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen_pre : ((gs0.take (1 + i.val)).foldl stepW inp).length = n0 + 1 + i.val := by
        rw [foldl_stepW_len, oneEach_append_len, List.length_take_of_le (by rw [hgs0_len]; omega)]
        omega
      have hlt_step : n0 + 1 + i.val < (stepW ((gs0.take (1 + i.val)).foldl stepW inp)
          ⟨.not, [N + N + i.val]⟩).length := by
        simp [stepW, hlen_pre]
      rw [foldl_stepW_getD_lt _ _ _ hlt_step]
      rw [← hlen_pre, stepW_getD_self]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
      rw [foldl_stepW_getD_lt _ _ (N + N + i.val) (by rw [oneEach_append_len]; omega),
          oneEach_append_getD x0 y0 w (N + N + i.val) (by omega)]
      have h1 : ¬(N + N + i.val < N) := by omega
      have h2 : ¬(N + N + i.val < N + N) := by omega
      simp only [h1, h2, ↓reduceDIte]
      congr 2; apply Fin.ext; simp

    let tabList : List (List (Fin N × Fin N)) := (List.finRange p).map cellsOf
    have htabList_len : tabList.length = p := by simp [tabList]
    have hspT := appendTables_spec (E := E) R S tabList
      (by intro cs hcs; rcases List.mem_map.mp hcs with ⟨m, _, rfl⟩; exact hcells_RS m)
      (by intro cs hcs; rcases List.mem_map.mp hcs with ⟨m, _, rfl⟩; exact hcells_len m)
      gs0 n0 (by rw [hgs0_len]; omega) (le_refl n0) hz0_false hRB0 hLG0 hNG0
    rcases hspT with ⟨⟨exT, hexT, hexT_len⟩, hT_wlen, hRBT, hLGT, hNGT, hT_bounds, hT_eval⟩
    let rT := appendTables N n0 n0 tabList gs0

    let leaf : ℕ → ℕ := fun m => if m < p then rT.2.getD m n0 else n0
    have hleaf_lt : ∀ m, leaf m < n0 + rT.1.length := by
      intro m
      dsimp only [leaf]
      split_ifs with hm
      · exact (hT_bounds m (by rw [htabList_len]; exact hm)).2
      · rw [hexT, List.length_append, hgs0_len]; omega
    have hleaf_ge : ∀ m, n0 ≤ leaf m := by
      intro m
      dsimp only [leaf]
      split_ifs with hm
      · exact (hT_bounds m (by rw [htabList_len]; exact hm)).1
      · exact le_refl n0
    have hnot_ltT : ∀ i < h, n0 + 1 + i < n0 + rT.1.length := fun i hi => by
      rw [hexT, List.length_append, hgs0_len]; omega
    have hnot_evalT : ∀ (i : Fin h) (x0 y0 : Fin N) (w : Fin h → Bool),
        (rT.1.foldl stepW (oneEach x0 y0 ++ List.ofFn w)).getD (n0 + 1 + i.val) false = !w i := by
      intro i x0 y0 w
      rw [hexT, List.foldl_append,
          foldl_stepW_getD_lt _ _ _ (by rw [foldl_stepW_len, oneEach_append_len, hgs0_len]; omega)]
      exact hnot_eval0 i x0 y0 w
    have hspM := buildMux_spec R S leaf h (le_refl h) 0 rT.1 hleaf_lt hleaf_ge
      hnot_ltT hnot_evalT hRBT hLGT hNGT
    rcases hspM with ⟨⟨exM, hexM, hexM_len⟩, hRBM, hLGM, hNGM, hout_ge, hout_lt, hevalM⟩
    let rM := buildMux N h leaf h 0 rT.1
    let C : Circ := ⟨rM.1, rM.2⟩
    have hC_eval : ∀ (w : Fin h → Bool) (x0 y0 : Fin N),
        table h C w x0 y0 =
          if hm : decodeBits h (le_refl h) w < p then
            decide ((x0, y0) ∈ cellsOf ⟨decodeBits h (le_refl h) w, hm⟩)
          else false := by
      intro w x0 y0
      change (rM.1.foldl stepW (oneEach x0 y0 ++ List.ofFn w)).getD rM.2 false = _
      rw [hevalM x0 y0 w, zero_add]
      dsimp only [leaf]
      split_ifs with hm
      · have hte := hT_eval (decodeBits h (le_refl h) w) (by rw [htabList_len]; exact hm) x0 y0 w
        have htab_get : tabList[decodeBits h (le_refl h) w]'(by rw [htabList_len]; exact hm) =
            cellsOf ⟨decodeBits h (le_refl h) w, hm⟩ := by
          simp [tabList]
        simpa [htab_get] using hte
      · rw [hexT, List.foldl_append,
            foldl_stepW_getD_lt _ _ n0 (by rw [foldl_stepW_len, oneEach_append_len, hgs0_len]; omega)]
        exact hz0_false x0 y0 w
    refine ⟨p, h, C, hp_pos, hp_le_q, hp_le_pow, hpow_le_2p, ?_, ?_, ?_⟩
    ·
      refine ⟨⟨hRBM, hout_lt, hLGM⟩, ?_, ?_⟩
      · constructor
        · intro x hx
          rcases hx with hout_eq | hmem
          · exfalso; dsimp only [C, rM] at hout_eq; omega
          · exact hNGM.1 x hmem
        · intro y hy
          rcases hy with hout_eq | hmem
          · exfalso; dsimp only [C, rM] at hout_eq; omega
          · exact hNGM.2 y hmem
      · intro w
        change lossFun f (table h C w) ∅ ≤ E
        rw [lossFun_empty]
        by_cases hm : decodeBits h (le_refl h) w < p
        · have hfun : table h C w = fun x0 y0 =>
              decide ((x0, y0) ∈ cellsOf ⟨decodeBits h (le_refl h) w, hm⟩) := by
            ext x0 y0; simp [hC_eval, hm]
          rw [hfun, hcells_totalOnes]
          exact ha_sum ⟨decodeBits h (le_refl h) w, hm⟩
        · have hfun : table h C w = fun _ _ => false := by
            ext x0 y0; simp [hC_eval, hm]
          rw [hfun]
          unfold totalOnes
          simp
    ·
      change rM.1.length ≤ 2 * p * E + 8 * p + h + 2
      rw [hexM, List.length_append, hexT, List.length_append, hgs0_len, hexM_len]
      rw [htabList_len] at hexT_len
      omega
    ·
      intro U hU
      have hterm : ∀ m : Fin p,
          (loss (table h C (code h m.val)) U : ℝ) =
            ((N * t : ℕ) : ℝ) - ((∑ j : Fin q, (a m j : ℝ)) - 2 * ∑ j ∈ Uᶜ, (a m j : ℝ)) := by
        intro m
        have hdec : decodeBits h (le_refl h) (code h m.val) = m.val := by
          rw [decodeBits_code, Nat.mod_eq_of_lt (lt_of_lt_of_le m.isLt hp_le_pow)]
        have hfun : table h C (code h m.val) = fun x0 y0 => decide ((x0, y0) ∈ cellsOf m) := by
          ext x0 y0
          rw [hC_eval, hdec]
          simp [m.isLt]
        change (lossFun f (table h C (code h m.val)) U : ℝ) = _
        rw [hfun, lossFun_eq_real f hf _ U, hU, hcells_totalOnes m]
        simp_rw [hcells_matchCount m]
        have hsplit : ∑ j : Fin q, (a m j : ℝ) =
            (∑ j ∈ U, (a m j : ℝ)) + (∑ j ∈ Uᶜ, (a m j : ℝ)) :=
          (Finset.sum_add_sum_compl U (fun j => (a m j : ℝ))).symm
        rw [Nat.cast_sum]
        linarith
      simp_rw [hterm]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, sub_div]
      have hp_ne : (p : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hp_pos)
      rw [mul_div_cancel_left₀ _ hp_ne]
      have hopt := ha_opt U hU
      have hgain_eq : gainOf cap E t = gain := rfl
      rw [hgain_eq] at hopt
      change _ ≤ ((N * t : ℕ) : ℝ) - gain
      linarith
