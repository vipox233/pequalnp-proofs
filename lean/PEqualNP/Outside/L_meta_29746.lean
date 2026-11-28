import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29746

open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

-- The exit mean, finite packing, matching loss, and circuit extension lemmas below
-- are adapted from lean/PEqualNP/Outside/L_meta_29757.lean at
-- b78349653c117b287f5389d9c425659a0ee3fa1f, with private names.

section ExitMean

variable {s : ℕ} (n : Fin s → Bool → Option (Fin s))

private def Absorbs := ∃ c : Fin s → Bool, ∀ i : Fin s,
  (fun x : Option (Fin s) => x.bind (fun j => n j (c j)))^[s] (some i) = none

private def Ends (r : Fin s → Bool → ℝ) (x : Fin s → ℝ) (i : Fin s) (b : Bool) : ℝ :=
  (n i b).elim (r i b) x

private def Solves (r : Fin s → Bool → ℝ) (x : Fin s → ℝ) : Prop :=
  ∀ i, 2 * x i = Ends n r x i false + Ends n r x i true

private theorem minimumLaw (hn : Absorbs n) (x : Fin s → ℝ)
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

private def drift : (Fin s → ℝ) →ₗ[ℝ] (Fin s → ℝ) where
  toFun x i := 2 * x i - (n i false).elim 0 x - (n i true).elim 0 x
  map_add' x y := by
    ext i
    cases h₀ : n i false <;> cases h₁ : n i true <;> simp [h₀, h₁] <;> ring
  map_smul' a x := by
    ext i
    cases h₀ : n i false <;> cases h₁ : n i true <;> simp [h₀, h₁] <;> ring

private theorem uniqueDrift (hn : Absorbs n) : Function.Injective (drift n) := by
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

private def boundary (r : Fin s → Bool → ℝ) (i : Fin s) : ℝ :=
  (n i false).elim (r i false) (fun _ => 0) + (n i true).elim (r i true) (fun _ => 0)

private theorem solves_iff (r : Fin s → Bool → ℝ) (x : Fin s → ℝ) :
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

private noncomputable def mean (hn : Absorbs n) : (Fin s → Bool → ℝ) →ₗ[ℝ] (Fin s → ℝ) :=
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

private theorem mean_solves (hn : Absorbs n) (r) : Solves n r (mean n hn r) := by
  rw [solves_iff]
  exact (LinearEquiv.ofBijective (drift n)
    ⟨uniqueDrift n hn, LinearMap.surjective_of_injective (uniqueDrift n hn)⟩).apply_symm_apply _

private theorem eqMean (hn : Absorbs n) {r x} (h : Solves n r x) : x = mean n hn r :=
  uniqueDrift n hn (((solves_iff n _ _).mp h).trans ((solves_iff n _ _).mp (mean_solves n hn r)).symm)

private theorem mean_const (hn : Absorbs n) (a : ℝ) : mean n hn (fun _ _ => a) = fun _ => a := by
  symm
  apply eqMean
  intro i
  cases h₀ : n i false <;> cases h₁ : n i true <;> simp [Ends, h₀, h₁] <;> ring

private theorem mean_nonneg (hn : Absorbs n) (r : Fin s → Bool → ℝ) (hr : ∀ i b, 0 ≤ r i b) :
    ∀ i, 0 ≤ mean n hn r i := by
  apply minimumLaw n hn
  intro i
  rw [mean_solves n hn r i]
  cases h₀ : n i false <;> cases h₁ : n i true <;> simp [Ends, h₀, h₁, hr, add_nonneg]

end ExitMean

private theorem apportion {ι : Type} [DecidableEq ι] (u : Finset ι) (cap : ι → ℕ) (a : ℕ)
    (ha : a ≤ ∑ j ∈ u, cap j) :
    ∃ v : ι → ℕ, (∀ j, v j ≤ cap j) ∧ ∑ j ∈ u, v j = a := by
  induction u using Finset.induction_on generalizing a with
  | empty => exact ⟨fun _ => 0, by simp, by simpa [eq_comm] using ha⟩
  | @insert i u hi ih =>
    rw [sum_insert hi] at ha
    obtain ⟨v, hv, he⟩ := ih (a-cap i) (by omega)
    refine ⟨Function.update v i (min a (cap i)), ?_, ?_⟩
    · intro j
      by_cases h : j = i <;> simp [Function.update, h, hv]
    · rw [sum_insert hi, Function.update_self, sum_congr rfl (g := v) (by
        intro j hj
        exact Function.update_of_ne (ne_of_mem_of_not_mem hj hi) ..), he]
      omega

private def remMass (q E b : ℕ) := (2^b*E) % q

private theorem carryRule (q E b : ℕ) :
    2 * remMass q E b = q * (2*remMass q E b / q) + remMass q E (b+1) := by
  have hh : remMass q E (b+1) = (2*remMass q E b) % q := by
    simp [remMass, pow_succ', mul_assoc, Nat.mul_mod_mod]
  rw [hh, Nat.div_add_mod]

private theorem packStep {q E b : ℕ} (v : Fin q → ℕ)
    (hv : (∑ j, v j) + remMass q E b = E) (hnext : remMass q E (b+1) ≤ E) :
    ∃ u d : Fin q → ℕ, (∑ j, u j) + remMass q E (b+1) = E ∧ (∑ j, d j) = E ∧
      ∀ j, 2 * (q*v j + remMass q E b) = q*d j + (q*u j + remMass q E (b+1)) := by
  let c := 2*remMass q E b / q
  let cap := fun j => 2*v j + c
  have hc : 2*remMass q E b = q*c + remMass q E (b+1) := carryRule q E b
  have hcap : (∑ j, cap j) + remMass q E (b+1) = 2*E := by
    simp only [cap, sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    change 2 * (∑ j, v j) + q*c + remMass q E (b+1) = 2*E
    omega
  obtain ⟨u, hu, hsum⟩ := apportion univ cap (E - remMass q E (b+1)) (by omega)
  refine ⟨u, fun j => cap j - u j, by omega, ?_, ?_⟩
  · rw [sum_tsub_distrib univ (fun j _ => hu j)]
    omega
  · intro j
    have h := Nat.sub_add_cancel (hu j)
    change cap j - u j + u j = 2*v j+c at h
    calc
      _ = q*(2*v j) + 2*remMass q E b := by ring
      _ = q*(2*v j+c) + remMass q E (b+1) := by rw [hc]; ring
      _ = _ := by rw [← h]; ring

private theorem packCycle {q E p : ℕ} (hE : E < q) (hp : 0 < p)
    (hpow : 2^p % q = 1) (horb : ∀ b < p, remMass q E b ≤ E) :
    ∃ (v d : ℕ → Fin q → ℕ), (∀ j, v 0 j = E) ∧ (∀ j, v p j = E) ∧
      (∀ b < p, (∑ j, d b j) = E) ∧
      ∀ b < p, ∀ j, 2*v b j = q*d b j + v (b+1) j := by
  classical
  have hzero : remMass q E 0 = E := by simp [remMass, Nat.mod_eq_of_lt hE]
  have hend : remMass q E p = E := by
    rw [remMass, Nat.mul_mod, hpow, one_mul, Nat.mod_mod, Nat.mod_eq_of_lt hE]
  have extBound (b : ℕ) (hb : b ≤ p) : remMass q E b ≤ E := by
    rcases lt_or_eq_of_le hb with h | rfl
    · exact horb _ h
    · exact hend.le
  let shift (v : Fin q → ℕ) (b : ℕ) (j : Fin q) := q*v j + remMass q E b
  have build (k : ℕ) (hk : k ≤ p) :
      ∃ v d : ℕ → Fin q → ℕ, v 0 = 0 ∧ (∑ j, v k j) + remMass q E k = E ∧
        ∀ b < k, (∑ j, d b j) = E ∧ ∀ j, 2*shift (v b) b j =
            q*d b j + shift (v (b+1)) (b+1) j := by
    induction k with
    | zero => exact ⟨0, 0, rfl, by simp [hzero], by simp⟩
    | succ k ih =>
      obtain ⟨v, d, h0, hv, hd⟩ := ih (by omega)
      obtain ⟨u, e, hu, he, hstep⟩ := packStep (v k) hv (extBound _ hk)
      refine ⟨Function.update v (k+1) u, Function.update d k e, ?_, ?_, ?_⟩
      · simpa using h0
      · simpa using hu
      · intro b hb
        rcases Nat.lt_succ_iff_lt_or_eq.mp hb with h | rfl
        · simpa [Function.update_of_ne h.ne, Function.update_of_ne (show b ≠ k+1 by omega),
            Function.update_of_ne (show b+1 ≠ k+1 by omega)] using hd b h
        · simpa [shift] using And.intro he hstep
  obtain ⟨v, d, h0, hpv, hd⟩ := build p le_rfl
  have hsum : (∑ j, v p j) = 0 := by omega
  have hvp (j) : v p j = 0 := (sum_eq_zero_iff_of_nonneg (by simp)).mp hsum _ (mem_univ j)
  exact ⟨fun b => shift (v b) b, d, by simp [shift, h0, hzero], by simp [shift, hvp, hend],
    fun b hb => (hd b hb).1, fun b hb => (hd b hb).2⟩

section MatchingLoss
variable {q N : ℕ}
variable (f : Fin q → Equiv.Perm (Fin N))

private def row (j : Fin q) : Finset (Fin N × Fin N) :=
  univ.map ⟨fun x => (x,f j x), fun _ _ h => congrArg Prod.fst h⟩

@[local simp] private theorem mem_row (x y : Fin N) (j : Fin q) : (x,y) ∈ row f j ↔ f j x = y := by
  rw [row, mem_map]
  change (∃ a ∈ univ, (a,f j a) = (x,y)) ↔ _
  simp

@[local simp] private theorem card_row (j : Fin q) : (row f j).card = N := by simp [row]

private def cost (B H : Fin N → Fin N → Bool) (D : Finset (Fin q)) :=
  (univ.filter (fun z : Fin N × Fin N => H z.1 z.2 ≠
    xor (B z.1 z.2) (decide (z.2 ∈ D.image (fun j => f j z.1))))).card

private def changed (B H : Fin N → Fin N → Bool) :=
  univ.filter (fun z : Fin N × Fin N => H z.1 z.2 ≠ B z.1 z.2)

@[local simp] private theorem cost_empty (B H : Fin N → Fin N → Bool) :
    cost f B H ∅ = (changed B H).card := by simp [cost, changed]

private theorem separateRows (hf : ∀ x, Function.Injective (fun j => f j x))
    {j k : Fin q} (hne : j ≠ k) : Disjoint (row f j) (row f k) := by
  rw [disjoint_left]
  rintro ⟨x,y⟩ h1 h2
  exact hne (hf x ((mem_row .. |>.mp h1).trans (mem_row .. |>.mp h2).symm))

private theorem overlap (hf : ∀ x, Function.Injective (fun j => f j x)) (S : Finset (Fin N × Fin N))
    (D : Finset (Fin q)) :
    (S ∩ D.biUnion (row f)).card = ∑ j ∈ D, (S ∩ row f j).card := by
  rw [inter_biUnion, card_biUnion]
  intro j _ k _ hne
  exact (separateRows f hf hne).mono (inter_subset_right ..) (inter_subset_right ..)

private theorem totalEdits (hf : ∀ x, Function.Injective (fun j => f j x)) (S : Finset (Fin N × Fin N)) :
    (∑ j, (S ∩ row f j).card) ≤ S.card := by
  rw [← overlap f hf]
  exact card_le_card (inter_subset_left ..)

private theorem cost_id (hf : ∀ x, Function.Injective (fun j => f j x))
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

private def toggled (B : Fin N → Fin N → Bool) (S : Finset (Fin N × Fin N)) (x y : Fin N) :=
  xor (B x y) (decide ((x,y) ∈ S))

@[local simp] private theorem changed_toggled (B : Fin N → Fin N → Bool) (S : Finset (Fin N × Fin N)) :
    changed B (toggled B S) = S := by
  ext ⟨x,y⟩
  by_cases h : (x,y) ∈ S <;> cases e : B x y <;> simp [changed, toggled, e, h]

private theorem editSet (hf : ∀ x, Function.Injective (fun j => f j x))
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
end MatchingLoss

private theorem smallSet {q t : ℕ} (ht : 0 < t) (htq : t < q) (a : Fin q → ℝ) :
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

private theorem gameBound {q N t E : ℕ} (hq : 1 < q) (hqN : q ≤ N) (hE : E < q)
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

private def gateOK (g : Gate) := g.inputs.length ≤ 2 ∧
  (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))

private def legal (N : ℕ) (C : Circuit) := ReadsBack (N+N) C ∧ C.output < N+N+C.size ∧
  ∀ g ∈ C.gates, gateOK g

private def table {N : ℕ} (C : Circuit) (x y : Fin N) := C.eval (oneEach x y)

private def fits {N q : ℕ} (f : Fin q → Equiv.Perm (Fin N)) (E : ℕ) (base C : Circuit) :=
  legal N C ∧ C.gates.take base.size = base.gates ∧ C.size ≤ base.size+2*E+3 ∧
    cost f (table base) (table C) ∅ ≤ E

private def atBit {N : ℕ} (C : Circuit) (w : ℕ) (F : Fin N → Fin N → Bool) :=
  w < N+N+C.size ∧ ∀ x y, (C.wires (oneEach x y)).getD w false = F x y

private theorem wireLength (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length+C.size := by
  rcases C with ⟨gs,o⟩
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires, Circuit.size]
  | append_singleton gs g ih => simp [Circuit.wires, Circuit.size, List.foldl_append] at ih ⊢; omega

private theorem carryBit {N : ℕ} {A B : Circuit} (hab : A.gates <+: B.gates)
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

private def snoc (N : ℕ) (C : Circuit) (g : Gate) : Circuit := ⟨C.gates ++ [g], N+N+C.size⟩

private theorem snocLeg {N : ℕ} {C : Circuit} (hc : legal N C) (g : Gate) (hg : gateOK g)
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

private theorem snocEval {N : ℕ} (C : Circuit) (g : Gate) (x y : Fin N) :
    table (snoc N C g) x y =
      g.op.eval (g.inputs.map fun i => (C.wires (oneEach x y)).getD i false) := by
  have hlen : (C.wires (oneEach x y)).length = N+N+C.size := by simp [wireLength,oneEach]
  unfold table Circuit.eval
  change (((C.gates++[g]).foldl _ (oneEach x y)).getD (N+N+C.size) false) = _
  rw [← hlen, List.foldl_append]
  change ((C.wires (oneEach x y)) ++ [_]).getD (C.wires (oneEach x y)).length false = _
  simp [List.getD_eq_getElem?_getD, Circuit.wires]

private theorem endBit {N : ℕ} {C : Circuit} (hc : legal N C) : atBit C C.output (@table N C) :=
  ⟨hc.2.1, by intros; rfl⟩

private theorem addBinary {N : ℕ} {C : Circuit} (hc : legal N C) {a b : ℕ}
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

private theorem addNot {N : ℕ} {C : Circuit} (hc : legal N C) {a : ℕ} {A : Fin N → Fin N → Bool}
    (ha : atBit C a A) : ∃ K : Circuit, C.gates <+: K.gates ∧ legal N K ∧ K.size = C.size+1 ∧
      atBit K K.output (fun x y => !(A x y)) := by
  let g : Gate := ⟨.not,[a]⟩
  have hgood := snocLeg hc g (by simp [g,gateOK])
    (by intro i hi; simp [g] at hi; simpa [hi] using ha.1)
  refine ⟨snoc N C g,⟨[g],rfl⟩,hgood, by simp [snoc,Circuit.size],hgood.2.1,?_⟩
  intro x y
  change table (snoc N C g) x y = _
  simp [-List.getD_eq_getElem?_getD,snocEval,g,GateOp.eval,ha.2 x y]

private theorem addCell {N : ℕ} {C : Circuit} (hc : legal N C) (p : Fin N × Fin N) :
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

private theorem addCells {N : ℕ} {C : Circuit} (hc : legal N C) (S : Finset (Fin N × Fin N)) (hs : S.Nonempty) :
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

private theorem compileSet {q N E : ℕ} (f : Fin q → Equiv.Perm (Fin N)) {base : Circuit} (hbase : legal N base)
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

private def terminates {s : ℕ} (n : Fin s → Bool → Option (Fin s))
    (p : Fin s → Bool) : Prop :=
  ∀ i : Fin s, (fun x : Option (Fin s) => x.bind (fun h => n h (p h)))^[s] (some i) = none

private def ring (s : ℕ) (n : Fin s → Bool → Option (Fin s)) : Prop :=
  ∃ (perm : Equiv.Perm (Fin s)) (c : Fin s → Bool),
    (∀ i, n i (c i) = some (perm i) ∧ n i (!(c i)) = none) ∧
    ∀ i j : Fin s, ∃ k < s, (perm : Fin s → Fin s)^[k] i = j

private def exitLaw {s : ℕ} (n : Fin s → Bool → Option (Fin s))
    (P : Fin s → (Fin s × Bool) → ℝ) : Prop :=
  (∃ p, terminates n p) ∧ (∀ i z, 0 ≤ P i z) ∧ (∀ i, (∑ z, P i z) = 1) ∧
    ∀ i z, 2 * P i z = ∑ b : Bool,
      (n i b).elim (if z = (i,b) then 1 else 0) (fun h => P h z)

private theorem rewardLaw {s : ℕ} {n : Fin s → Bool → Option (Fin s)}
    {P : Fin s → (Fin s × Bool) → ℝ} (hP : exitLaw n P)
    (r : (Fin s × Bool) → ℕ) (i : Fin s) :
    2 * (∑ z, P i z * (r z : ℝ)) = ∑ b : Bool,
      (n i b).elim (r (i,b) : ℝ) (fun h => ∑ z, P h z * (r z : ℝ)) := by
  classical
  calc
    _ = ∑ z, (2 * P i z) * (r z : ℝ) := by simp only [mul_sum, mul_assoc]
    _ = ∑ z, (∑ b : Bool, (n i b).elim (if z = (i,b) then 1 else 0)
          (fun h => P h z)) * (r z : ℝ) := by
      exact sum_congr rfl (fun z _ => congrArg (fun u : ℝ => u * (r z : ℝ)) (hP.2.2.2 i z))
    _ = _ := by
      simp only [sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro b _
      cases hb : n i b <;> simp [hb, ite_mul]

private theorem powerFacts {a : ℕ} (ha : 2 ≤ a) :
    let q := 2^a-1
    let E := 2^(a-1)
    1 < q ∧ 0 < E ∧ E < q ∧ q.Coprime E := by
  dsimp only
  have he : 2 ≤ 2^(a-1) := by
    calc
      2 = (2:ℕ)^1 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have hp : (2:ℕ)^a = 2*2^(a-1) := by
    calc
      _ = (2:ℕ)^((a-1)+1) := congrArg (fun k : ℕ => 2^k) (by omega)
      _ = _ := by rw [pow_succ']
  refine ⟨by omega, by omega, by omega, ?_⟩
  apply Nat.Coprime.pow_right
  apply Nat.coprime_two_right.mpr
  exact ⟨2^(a-1)-1, by omega⟩

open scoped Classical in
private theorem stateCount {a s : ℕ} (ha : 2 ≤ a)
    {n : Fin s → Bool → Option (Fin s)} (hex : ∃ p, terminates n p)
    {x : ℝ} (hx : ((2^a-1 : ℕ) : ℝ)*x = (2^(a-1) : ℕ))
    (hint : ∃ m : ℤ, ((univ.filter (terminates n)).card : ℝ)*x = m) :
    a ≤ s ∧ (s = a → ∃ c, ¬ terminates n c ∧ ∀ p, ¬ terminates n p → p = c) := by
  classical
  let q := 2^a-1
  let E := 2^(a-1)
  let F := (univ.filter (terminates n)).card
  change (q:ℝ)*x = (E:ℝ) at hx
  obtain ⟨m, hm⟩ := hint
  change (F:ℝ)*x = (m:ℝ) at hm
  have ⟨hq, _, hEq, hcop⟩ : 1 < q ∧ 0 < E ∧ E < q ∧ q.Coprime E := powerFacts ha
  have hm' : (F:ℝ)*(E:ℝ) = (q:ℝ)*(m:ℝ) := by
    linear_combination (q:ℝ)*hm - (F:ℝ)*hx
  have hi : (F:ℤ)*(E:ℤ) = (q:ℤ)*m := by exact_mod_cast hm'
  have hd : q ∣ F*E := Int.natCast_dvd_natCast.mp (by exact ⟨m, by push_cast; exact hi⟩)
  have hdiv : q ∣ F := hcop.dvd_of_dvd_mul_right hd
  have hF : 0 < F := by
    obtain ⟨p, hp⟩ := hex
    exact card_pos.mpr ⟨p, mem_filter.mpr ⟨mem_univ _, hp⟩⟩
  let bad := (univ : Finset (Fin s → Bool)).filter (fun p => ¬ terminates n p)
  have hcard : F + bad.card = 2^s := by
    simpa [F, bad, Fintype.card_fun] using
      (card_filter_add_card_filter_not (s := (univ : Finset (Fin s → Bool))) (terminates n))
  have hqF := Nat.le_of_dvd hF hdiv
  have has : a ≤ s := by
    by_contra! h
    have hbound : 2^s ≤ E := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  refine ⟨has, fun heq => ?_⟩
  have hq' : 2^a = q+1 := by
    have hp : 0 < (2:ℕ)^a := by positivity
    omega
  have hpowEq : (2:ℕ)^s = q+1 :=
    (congrArg (fun k : ℕ => (2:ℕ)^k) heq).trans hq'
  rw [hpowEq] at hcard
  have hFeq : F = q := by
    obtain ⟨k, hk⟩ := hdiv
    have hkpos : 0 < k := by
      by_contra! h
      have : k = 0 := by omega
      simp [this] at hk
      omega
    by_contra h
    have hkt : 2 ≤ k := by
      by_contra! hkl
      have : k = 1 := by omega
      exact h (by simpa [this] using hk)
    have h2 := Nat.mul_le_mul_left q hkt
    omega
  have hbad : bad.card = 1 := by omega
  obtain ⟨c, hc⟩ := card_eq_one.mp hbad
  have aux (p) : ¬ terminates n p ↔ p = c := by
    have h : p ∈ bad ↔ p = c := by simp [hc]
    exact (by simpa only [bad, mem_filter, mem_univ, true_and] using h)
  exact ⟨c, (aux c).mpr rfl, fun p hp => (aux p).mp hp⟩

private def editWeight {N : ℕ} {Z : Type} [Fintype Z]
    (B : Fin N → Fin N → Bool) (H : Z → Fin N → Fin N → Bool) (w : Z → ℝ) : ℝ :=
  ∑ z, w z * ((changed B (H z)).card : ℝ)

private def matchWeight {N q : ℕ} {Z : Type} [Fintype Z]
    (f : Fin q → Equiv.Perm (Fin N)) (B : Fin N → Fin N → Bool)
    (H : Z → Fin N → Fin N → Bool) (w : Z → ℝ) (j : Fin q) : ℝ :=
  ∑ z, w z * ((changed B (H z) ∩ row f j).card : ℝ)

private theorem weightedScore {N q : ℕ} {Z : Type} [Fintype Z]
    (f : Fin q → Equiv.Perm (Fin N)) (hf : ∀ x, Function.Injective (fun j => f j x))
    (B : Fin N → Fin N → Bool) (H : Z → Fin N → Fin N → Bool) (w : Z → ℝ)
    (hw : ∑ z, w z = 1) (D : Finset (Fin q)) :
    (∑ z, w z * (cost f B (H z) D : ℝ)) =
      editWeight B H w + (N:ℝ)*D.card - 2*(∑ j ∈ D, matchWeight f B H w j) := by
  let d := fun z j => ((changed B (H z) ∩ row f j).card : ℝ)
  have h₁ (z : Z) : (cost f B (H z) D : ℝ) + 2*(∑ j ∈ D, d z j) =
      ((changed B (H z)).card : ℝ) + (N:ℝ)*D.card := by
    dsimp [d]
    exact_mod_cast cost_id f hf B (H z) D
  have h₂ := sum_congr (s₁ := (univ : Finset Z)) rfl
    (fun z _ => congrArg (fun u : ℝ => w z * u) (h₁ z))
  simp only [mul_add, sum_add_distrib] at h₂
  have hc : (∑ z, w z * ((N:ℝ)*D.card)) = (N:ℝ)*D.card := by
    rw [← sum_mul, hw, one_mul]
  have hd : (∑ z, w z * (2*(∑ j ∈ D, d z j))) =
      2*(∑ j ∈ D, matchWeight f B H w j) := calc
    _ = ∑ z, 2*(∑ j ∈ D, w z * d z j) := by
      exact sum_congr rfl (fun z _ => by rw [mul_left_comm, mul_sum D])
    _ = _ := by rw [← mul_sum, sum_comm]; rfl
  rw [hc, hd] at h₂
  change (∑ z, w z * (cost f B (H z) D : ℝ)) + 2*(∑ j ∈ D, matchWeight f B H w j) =
    editWeight B H w + (N:ℝ)*D.card at h₂
  linarith

private theorem weightedGame {N q t E : ℕ} {Z : Type} [Fintype Z]
    (hq : 1 < q) (hqN : q ≤ N) (hE : E < q) (ht : q < 2*t) (htq : t < q)
    (f : Fin q → Equiv.Perm (Fin N)) (hf : ∀ x, Function.Injective (fun j => f j x))
    (B : Fin N → Fin N → Bool) (H : Z → Fin N → Fin N → Bool) (w : Z → ℝ)
    (hw : ∑ z, w z = 1) (hwn : ∀ z, 0 ≤ w z) (herr : ∀ z, cost f B (H z) ∅ ≤ E) :
    let ideal := q*N*t-(2*t-q)*E
    let risk := fun D => (q:ℝ)*(∑ z, w z * (cost f B (H z) D : ℝ))
    (∃ D : Finset (Fin q), D.card = t ∧ (ideal:ℝ) ≤ risk D) ∧
    ((∀ D : Finset (Fin q), D.card = t → risk D ≤ (ideal:ℝ)) →
      ∀ j, (q:ℝ)*matchWeight f B H w j = E) := by
  dsimp only
  have hq' : 0 < (q:ℝ) := by exact_mod_cast (show 0 < q by omega)
  have htotal : (∑ j, matchWeight f B H w j) ≤ editWeight B H w := by
    unfold matchWeight editWeight
    rw [sum_comm]
    apply sum_le_sum
    intro z _
    rw [← mul_sum]
    apply mul_le_mul_of_nonneg_left _ (hwn z)
    exact_mod_cast totalEdits f hf (changed B (H z))
  have hcap : editWeight B H w ≤ (E:ℝ) := calc
    _ ≤ ∑ z, w z * (E:ℝ) := sum_le_sum fun z _ =>
      mul_le_mul_of_nonneg_left (by exact_mod_cast (show (changed B (H z)).card ≤ E by
        simpa only [cost_empty] using herr z)) (hwn z)
    _ = _ := by rw [← sum_mul, hw, one_mul]
  obtain ⟨⟨D,hD,hlo⟩,hbal⟩ := gameBound hq hqN hE ht htq
    (editWeight B H w) (matchWeight f B H w) htotal hcap _
    (weightedScore f hf B H w hw)
  exact ⟨⟨D,hD,by simpa only [mul_comm (q:ℝ)] using (div_le_iff₀ hq').mp hlo⟩,
    fun h => hbal (fun A hA => (le_div_iff₀ hq').mpr (by simpa only [mul_comm (q:ℝ)] using h A hA))⟩

private theorem weightedCompile {N q t E : ℕ} {Z : Type} [Fintype Z]
    (he : 0 < E) (hE : E < q) (hqN : q ≤ N) (ht : q < 2*t) (htq : t < q)
    (f : Fin q → Equiv.Perm (Fin N)) (hf : ∀ x, Function.Injective (fun j => f j x))
    (base : Circuit) (hbase : legal N base) (w : Z → ℝ) (hw : ∑ z, w z = 1)
    (d : Z → Fin q → ℕ) (hd : ∀ z, ∑ j, d z j = E)
    (hbal : ∀ j, (q:ℝ)*(∑ z, w z*(d z j:ℝ)) = E) :
    ∃ C : Z → Circuit, (∀ z, fits f E base (C z)) ∧
      ∀ D : Finset (Fin q), D.card = t →
        (q:ℝ)*(∑ z, w z * (cost f (table base) (table (C z)) D : ℝ)) =
          ((q*N*t-(2*t-q)*E : ℕ):ℝ) := by
  classical
  have hlim (z j) : d z j ≤ N := by
    have hh := single_le_sum (f := d z) (fun _ _ => Nat.zero_le _) (mem_univ j)
    rw [hd z] at hh
    omega
  choose S hSc hSj using fun z => editSet f hf (d z) (hlim z)
  choose C hg htable using fun z => compileSet f hbase (S z) ((hSc z).trans (hd z)) he
  refine ⟨C, hg, fun D hD => ?_⟩
  have htotal : editWeight (table (N := N) base) (fun z => table (C z)) w = (E:ℝ) := by
    simp only [editWeight, htable, changed_toggled, hSc, hd]
    rw [← sum_mul, hw, one_mul]
  have hj (j : Fin q) : (q:ℝ)*matchWeight f (table base) (fun z => table (C z)) w j = E := by
    simpa only [matchWeight, htable, changed_toggled, hSj] using hbal j
  have hsum : (q:ℝ)*(∑ j ∈ D, matchWeight f (table base) (fun z => table (C z)) w j) =
      (t:ℝ)*(E:ℝ) := by rw [mul_sum]; simp [hj, hD, nsmul_eq_mul]
  have hsafe : (2*t-q)*E ≤ q*N*t := calc
    _ ≤ t*N := Nat.mul_le_mul (by omega) (by omega)
    _ ≤ _ := by rw [mul_comm t, mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega)
  rw [weightedScore f hf _ _ w hw, htotal, hD, Nat.cast_sub hsafe]
  push_cast [Nat.cast_sub ht.le]
  linear_combination -2*hsum

private theorem ringPrefixSome {α : Type*} (f : Option α → Option α)
    (hzero : f none = none) {x : Option α} {a b : ℕ} (hab : a ≤ b)
    (hb : f^[b] x ≠ none) : ∃ j, f^[a] x = some j := by
  cases h : f^[a] x with
  | none =>
      exfalso
      apply hb
      calc
        f^[b] x = f^[b - a + a] x := by rw [Nat.sub_add_cancel hab]
        _ = none := by rw [Function.iterate_add_apply, h, Function.iterate_fixed hzero]
  | some j => exact ⟨j, rfl⟩

private theorem badPeriodic {s : ℕ} {n : Fin s → Bool → Option (Fin s)}
    {p : Fin s → Bool} (hp : ¬ terminates n p) :
    ∃ i : Fin s, ∃ k : ℕ, 0 < k ∧ k ≤ s ∧
      (fun x : Option (Fin s) => x.bind (fun h => n h (p h)))^[k] (some i) = some i := by
  classical
  simp only [terminates, not_forall] at hp
  rcases hp with ⟨i, hi⟩
  let f : Option (Fin s) → Option (Fin s) := fun x => x.bind (fun h => n h (p h))
  change f^[s] (some i) ≠ none at hi
  change ∃ j : Fin s, ∃ k : ℕ, 0 < k ∧ k ≤ s ∧ f^[k] (some j) = some j
  have hprefix (a : Fin (s + 1)) : ∃ j, f^[a.val] (some i) = some j := by
    have ha := a.isLt
    exact ringPrefixSome f rfl (by omega : a.val ≤ s) hi
  let visit (a : Fin (s + 1)) : Fin s := Classical.choose (hprefix a)
  have hvis (a : Fin (s + 1)) : f^[a.val] (some i) = some (visit a) :=
    Classical.choose_spec (hprefix a)
  obtain ⟨a, b, hab, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt visit (by simp)
  have cycle (u v : Fin (s + 1)) (hlt : u.val < v.val) (h : visit u = visit v) :
      ∃ j : Fin s, ∃ k : ℕ, 0 < k ∧ k ≤ s ∧ f^[k] (some j) = some j := by
    have hv := v.isLt
    refine ⟨visit u, v.val - u.val, by omega, by omega, ?_⟩
    calc
      f^[v.val - u.val] (some (visit u)) = f^[v.val] (some i) := by
        rw [← hvis u, ← Function.iterate_add_apply, Nat.sub_add_cancel (Nat.le_of_lt hlt)]
      _ = some (visit u) := (hvis v).trans (congrArg some h.symm)
  rcases lt_or_gt_of_ne (fun h : a.val = b.val => hab (Fin.ext h)) with h | h
  · exact cycle a b h heq
  · exact cycle b a h heq.symm

private theorem ringPeriodicNonempty {α : Type*} (f : Option α → Option α)
    (hzero : f none = none) {i : α} {k : ℕ} (hk : 0 < k)
    (h : Function.IsPeriodicPt f k (some i)) (t : ℕ) :
    f^[t] (some i) ≠ none := by
  have hend : f^[k] (some i) ≠ none := by
    rw [h.eq]
    simp
  obtain ⟨j, hj⟩ := ringPrefixSome f hzero (Nat.le_of_lt (Nat.mod_lt t hk)) hend
  rw [← h.iterate_mod_apply t, hj]
  simp

private theorem uniqueBadRing {s : ℕ}
    (n : Fin s → Bool → Option (Fin s)) (c : Fin s → Bool)
    (hc : ¬ terminates n c) (hu : ∀ p, ¬ terminates n p → p = c) : ring s n := by
  classical
  let f : Option (Fin s) → Option (Fin s) := fun x => x.bind (fun a => n a (c a))
  obtain ⟨i, k, hk, hks, hcycle⟩ := badPeriodic hc
  change f^[k] (some i) = some i at hcycle
  have hend : f^[k] (some i) ≠ none := by rw [hcycle]; simp
  let flip (j a : Fin s) : Bool := if a = j then !(c a) else c a
  have hflipTerm (j : Fin s) : terminates n (flip j) := by
    by_contra h
    have heq : (!(c j)) = c j := by simpa [flip] using congrFun (hu _ h) j
    exact Bool.not_ne_self _ heq
  have hcov (j : Fin s) : ∃ t < k, f^[t] (some i) = some j := by
    by_contra hmiss
    let f' : Option (Fin s) → Option (Fin s) := fun x => x.bind (fun a => n a (flip j a))
    have hagree (t : ℕ) (ht : t ≤ k) : f'^[t] (some i) = f^[t] (some i) := by
      induction t with
      | zero => rfl
      | succ t ih =>
          obtain ⟨a, ha⟩ := ringPrefixSome f rfl (by omega : t ≤ k) hend
          have haj : a ≠ j := by
            rintro rfl
            exact hmiss ⟨t, by omega, ha⟩
          simp only [Function.iterate_succ_apply']
          rw [ih (by omega), ha]
          simp [f', f, flip, haj]
    have hcycle' : Function.IsPeriodicPt f' k (some i) :=
      (hagree k le_rfl).trans hcycle
    exact ringPeriodicNonempty f' rfl hk hcycle' s (hflipTerm j i)
  have htotal (j : Fin s) : ∃ a, n j (c j) = some a := by
    obtain ⟨t, ht, hj⟩ := hcov j
    obtain ⟨a, ha⟩ := ringPrefixSome f rfl (by omega : t + 1 ≤ k) hend
    rw [Function.iterate_succ_apply', hj] at ha
    exact ⟨a, ha⟩
  have halt (j : Fin s) : n j (!(c j)) = none := by
    cases h : n j (!(c j)) with
    | none => rfl
    | some b =>
        exfalso
        have htotal' (a : Fin s) : ∃ r, n a (flip j a) = some r := by
          by_cases haj : a = j
          · subst a
            exact ⟨b, by simpa [flip] using h⟩
          · simpa [flip, haj] using htotal a
        let f' : Option (Fin s) → Option (Fin s) := fun x => x.bind (fun a => n a (flip j a))
        have hsurvive (t : ℕ) : ∃ a, f'^[t] (some j) = some a := by
          induction t with
          | zero => exact ⟨j, rfl⟩
          | succ t ih =>
              obtain ⟨a, ha⟩ := ih
              obtain ⟨r, hr⟩ := htotal' a
              exact ⟨r, by rw [Function.iterate_succ_apply', ha]; exact hr⟩
        obtain ⟨a, ha⟩ := hsurvive s
        have hnil : f'^[s] (some j) = none := hflipTerm j j
        rw [hnil] at ha
        cases ha
  let g (j : Fin s) : Fin s := Classical.choose (htotal j)
  have hg (j : Fin s) : n j (c j) = some (g j) := Classical.choose_spec (htotal j)
  have hlift (t : ℕ) (j : Fin s) : f^[t] (some j) = some (g^[t] j) := by
    induction t with
    | zero => rfl
    | succ t ih =>
        simp only [Function.iterate_succ_apply']
        rw [ih]
        exact hg _
  have hgcycle : g^[k] i = i := Option.some.inj ((hlift k i).symm.trans hcycle)
  have horbit (j : Fin s) : ∃ t < k, g^[t] i = j := by
    obtain ⟨t, ht, hj⟩ := hcov j
    exact ⟨t, ht, Option.some.inj ((hlift t i).symm.trans hj)⟩
  have hsurj : Function.Surjective g := by
    intro j
    obtain ⟨t, ht, hj⟩ := horbit j
    cases t with
    | zero =>
        have hpred : (k - 1).succ = k := by omega
        refine ⟨g^[k - 1] i, ?_⟩
        calc
          g (g^[k - 1] i) = g^[(k - 1).succ] i :=
            (Function.iterate_succ_apply' g (k - 1) i).symm
          _ = i := by rw [hpred, hgcycle]
          _ = j := hj
    | succ t => exact ⟨g^[t] i, by simpa only [Function.iterate_succ_apply'] using hj⟩
  let perm : Equiv.Perm (Fin s) :=
    Equiv.ofBijective g ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  refine ⟨perm, c, fun j => ⟨hg j, halt j⟩, ?_⟩
  intro x y
  obtain ⟨a, ha, hax⟩ := horbit x
  obtain ⟨b, hb, hby⟩ := horbit y
  change ∃ t < s, g^[t] x = y
  by_cases hab : a ≤ b
  · refine ⟨b - a, by omega, ?_⟩
    rw [← hax, ← Function.iterate_add_apply, Nat.sub_add_cancel hab, hby]
  · have hadd : k + b - a + a = b + k := by omega
    refine ⟨k + b - a, by omega, ?_⟩
    rw [← hax, ← Function.iterate_add_apply, hadd, Function.iterate_add_apply, hgcycle, hby]


open Classical in
private theorem policyDet {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (p : Fin s → Bool) :
    (Matrix.of (fun i j : Fin s => (if i = j then (1 : ℤ) else 0) -
      (if n i (p i) = some j then 1 else 0))).det = if terminates n p then 1 else 0 := by
  classical
  let f (x : Option (Fin s)) : Option (Fin s) := x.bind fun i => n i (p i)
  let A : Matrix (Fin s) (Fin s) ℤ := Matrix.of fun i j =>
    (if i = j then 1 else 0) - (if f (some i) = some j then 1 else 0)
  change A.det = if terminates n p then 1 else 0
  by_cases ht : terminates n p
  · rw [if_pos ht]
    change ∀ i : Fin s, f^[s] (some i) = none at ht
    have hdiag (i : Fin s) : A i i = 1 := by
      have hloop : f (some i) ≠ some i := by
        intro h
        have habs := (Function.iterate_fixed h s).symm.trans (ht i)
        simp at habs
      simp [A, hloop]
    rw [Matrix.det_apply']
    refine (Finset.sum_eq_single (1 : Equiv.Perm (Fin s)) ?_ ?_).trans ?_
    · intro σ _ hσ
      have hmoved : ¬ ∀ i, σ i = i := fun h => hσ (Equiv.ext h)
      obtain ⟨i, hi⟩ := not_forall.mp hmoved
      by_contra hterm
      -- At moved indices a nonzero factor forces a transition along the inverse permutation.
      have hstep (j : Fin s) (hj : σ j ≠ j) : f (some (σ j)) = some j := by
        by_contra h
        have hz : A (σ j) j = 0 := by simp [A, hj, h]
        have hpz : (∏ i, A (σ i) i) = 0 :=
          Finset.prod_eq_zero (f := fun i => A (σ i) i) (Finset.mem_univ j) hz
        exact hterm (by rw [hpz, mul_zero])
      have hchain (k : ℕ) (j : Fin s) (hj : σ j ≠ j) :
          f^[k] (some j) = some ((σ.symm : Fin s → Fin s)^[k] j) := by
        induction k generalizing j with
        | zero => rfl
        | succ k ih =>
          have hj' : σ (σ.symm j) ≠ σ.symm j := by
            intro h
            have hjfix := (σ.apply_symm_apply j).symm.trans h
            exact hj ((congrArg σ hjfix).trans (σ.apply_symm_apply j))
          have hs : f (some j) = some (σ.symm j) := by
            simpa only [σ.apply_symm_apply] using hstep (σ.symm j) hj'
          simp only [Function.iterate_succ_apply, hs, ih _ hj']
      have habs := (hchain s i hi).symm.trans (ht i)
      simp at habs
    · simp
    · simp [hdiag]
  · rw [if_neg ht]
    obtain ⟨i, k, hk, _, hcycle⟩ := badPeriodic ht
    change f^[k] (some i) = some i at hcycle
    -- The indicator of states that never terminate is a nonzero kernel vector.
    let survives (j : Fin s) : Prop := ∀ t : ℕ, f^[t] (some j) ≠ none
    let v (j : Fin s) : ℤ := if survives j then 1 else 0
    have hi : survives i := by
      intro t h
      have hle : t ≤ k * t := by
        simpa only [Nat.one_mul] using Nat.mul_le_mul_right t (show 1 ≤ k from hk)
      obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le hle
      have hnone (m : ℕ) : f^[m] none = none := Function.iterate_fixed rfl m
      have hzero : f^[k * t] (some i) = none := by
        rw [hu, Nat.add_comm t u, Function.iterate_add_apply, h, hnone]
      have hrepeat : f^[k * t] (some i) = some i := by
        rw [Function.iterate_mul]
        exact Function.iterate_fixed hcycle t
      have habs := hrepeat.symm.trans hzero
      simp at habs
    let B : Matrix (Fin s) (Fin s) ℤ :=
      Matrix.of fun j l => if f (some j) = some l then 1 else 0
    have hA : A = 1 - B := by
      ext j l
      simp only [A, B, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply]
    have hB : B.mulVec v = v := by
      funext j
      rw [Matrix.mulVec_apply_eq_sum]
      cases hj : f (some j) with
      | none =>
        have hdead : ¬ survives j := by
          intro h
          exact h 1 (by simpa only [Function.iterate_one] using hj)
        simp [B, hj, v, hdead]
      | some l =>
        have hsurv : survives j ↔ survives l := by
          constructor
          · intro h t
            simpa only [Function.iterate_succ_apply, hj] using h t.succ
          · intro h t
            cases t with
            | zero => simp
            | succ t => simpa only [Function.iterate_succ_apply, hj] using h t
        have hv : v j = v l := by simp only [v, hsurv]
        simpa only [B, Matrix.of_apply, hj, Option.some.injEq, ite_mul, one_mul, zero_mul,
          Fintype.sum_ite_eq] using hv.symm
    apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors (v := v) (i := i)
    · rw [hA, Matrix.sub_mulVec, Matrix.one_mulVec, hB, sub_self]
    · rw [show v i = 1 by simp [v, hi]]
      exact one_mem _


open scoped Classical Matrix in
private theorem integralPolicy {s : ℕ} (n : Fin s → Bool → Option (Fin s))
    (r : Fin s → Bool → ℕ) (v : Fin s → ℝ)
    (hv : ∀ i, 2 * v i = ∑ b : Bool, (n i b).elim (r i b : ℝ) v) (i : Fin s) :
    ∃ m : ℤ, ((Finset.univ.filter (terminates n)).card : ℝ) * v i = m := by
  let row (j : Fin s) (b : Bool) (k : Fin s) : ℤ :=
    (if j = k then 1 else 0) - (if n j b = some k then 1 else 0)
  let A : Matrix (Fin s) (Fin s) ℤ := Matrix.of fun j => ∑ b : Bool, row j b
  let d (j : Fin s) : ℤ := ∑ b : Bool, (n j b).elim (r j b : ℤ) (fun _ => 0)
  have hdet : A.det = ((Finset.univ.filter (terminates n)).card : ℤ) := by
    calc
      A.det = ∑ p : Fin s → Bool, (Matrix.of fun j => row j (p j)).det := by
        exact (Matrix.detRowAlternating (n := Fin s) (R := ℤ)).toMultilinearMap.map_sum row
      _ = ∑ p : Fin s → Bool, if terminates n p then 1 else 0 := by
        refine Finset.sum_congr rfl fun p _ => ?_
        exact policyDet n p
      _ = _ := Finset.sum_boole _ _
  let f : ℤ →+* ℝ := Int.castRingHom ℝ
  let Aℝ : Matrix (Fin s) (Fin s) ℝ := f.mapMatrix A
  have hAR (j k : Fin s) : Aℝ j k = ∑ b : Bool,
      ((if j = k then (1 : ℝ) else 0) - (if n j b = some k then 1 else 0)) := by
    change (((∑ b : Bool, row j b) k : ℤ) : ℝ) = _
    rw [Finset.sum_apply, Int.cast_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hj : j = k <;> by_cases hn : n j b = some k <;> simp [row, hj, hn]
  have hAv : Aℝ *ᵥ v = fun j => (d j : ℝ) := by
    funext j
    let c (b : Bool) : ℤ := (n j b).elim (r j b : ℤ) (fun _ => 0)
    have hr (b : Bool) : (n j b).elim (r j b : ℝ) v =
        (c b : ℝ) + (n j b).elim 0 v := by
      cases h : n j b <;> simp [c, h]
    calc
      (Aℝ *ᵥ v) j = ∑ b : Bool, ∑ k : Fin s,
          ((if j = k then (1 : ℝ) else 0) - (if n j b = some k then 1 else 0)) * v k := by
        simp only [Matrix.mulVec_apply_eq_sum, hAR, Finset.sum_mul]
        rw [Finset.sum_comm]
      _ = ∑ b : Bool, (v j - (n j b).elim 0 v) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [sub_mul, Finset.sum_sub_distrib]
        rw [Finset.sum_boole_mul, if_pos (Finset.mem_univ j)]
        cases h : n j b <;> simp [h, boole_mul]
      _ = (∑ _ : Bool, v j) - ∑ b : Bool, (n j b).elim 0 v := by
        rw [Finset.sum_sub_distrib]
      _ = (d j : ℝ) := by
        have h := hv j
        simp_rw [hr] at h
        rw [Finset.sum_add_distrib, ← Int.cast_sum] at h
        change 2 * v j = (d j : ℝ) + ∑ b : Bool, (n j b).elim 0 v at h
        rw [Fintype.sum_bool]
        linarith only [h]
  have hdetR : Aℝ.det = ((Finset.univ.filter (terminates n)).card : ℝ) := by
    change (f.mapMatrix A).det = _
    rw [← f.map_det, hdet] <;> exact Int.cast_natCast _
  have hupdate : f.mapMatrix (A.updateCol i d) =
      Aℝ.updateCol i (fun j => (d j : ℝ)) := by
    ext j k
    change f (A.updateCol i d j k) = (Aℝ.updateCol i (fun t => (d t : ℝ))) j k
    rw [Matrix.updateCol_apply, Matrix.updateCol_apply]
    by_cases hk : k = i <;> simp only [hk, if_true, if_false] <;> rfl
  refine ⟨(A.updateCol i d).det, ?_⟩
  rw [← hdetR]
  calc
    Aℝ.det * v i = Aℝ.cramer (fun j => (d j : ℝ)) i := by
      have h : Aℝ.cramer (Aℝ *ᵥ v) = Aℝ.det • v := by
        rw [Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
          Matrix.smul_mulVec, Matrix.one_mulVec]
      rw [hAv] at h
      exact (congrFun h i).symm
    _ = ((A.updateCol i d).det : ℝ) := by
      rw [Matrix.cramer_apply]
      exact (congrArg Matrix.det hupdate).symm.trans (f.map_det _).symm


private theorem cycleWitness {a : ℕ} (ha : 2 ≤ a) :
    ∃ (start : Fin a) (n : Fin a → Bool → Option (Fin a))
      (P : Fin a → (Fin a × Bool) → ℝ) (d : (Fin a × Bool) → Fin (2^a-1) → ℕ),
      terminates n (fun _ => false) ∧ ring a n ∧
      (∀ i z, 0 ≤ P i z) ∧ (∀ i, (∑ z, P i z) = 1) ∧
      (∀ i z, 2 * P i z = ∑ b : Bool,
        (n i b).elim (if z = (i,b) then 1 else 0) (fun h => P h z)) ∧
      (∀ z, (∑ j, d z j) = 2^(a-1)) ∧
      ∀ j, ((2^a-1 : ℕ) : ℝ) * (∑ z, P start z * (d z j : ℝ)) = (2^(a-1) : ℕ) := by
  classical
  let q : ℕ := 2^a - 1
  let E : ℕ := 2^(a-1)
  have ha0 : 0 < a := by omega
  letI : NeZero a := ⟨ha0.ne'⟩
  have htw : (2:ℕ)^a = 2 * E := by
    calc
      _ = (2:ℕ)^(1+(a-1)) := congrArg (fun k : ℕ => (2:ℕ)^k) (by omega)
      _ = _ := by rw [pow_add]; norm_num [E]
  have htwoE : 2 ≤ E := calc
    2 = (2:ℕ)^1 := by norm_num
    _ ≤ E := Nat.pow_le_pow_right (by decide) (by omega)
  have hEq : q + 1 = 2 * E := by dsimp [q]; omega
  have hq : 1 < q := by omega
  have hE : E < q := by omega
  have hpow : (2:ℕ)^a % q = 1 := by
    calc
      _ = (q+1) % q := congrArg (fun k : ℕ => k % q) (htw.trans hEq.symm)
      _ = 1 := by rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hq]
  have horb : ∀ b < a, remMass q E b ≤ E := by
    intro b hb
    by_cases hzero : b = 0
    · simp [hzero, remMass, Nat.mod_eq_of_lt hE]
    · have hpower : (2:ℕ)^b * E = (2:ℕ)^a * 2^(b-1) := by
        dsimp [E]
        rw [← pow_add, ← pow_add, show b + (a-1) = a + (b-1) by omega]
      have hsmall : (2:ℕ)^(b-1) ≤ E := Nat.pow_le_pow_right (by decide) (by omega)
      rw [remMass, hpower, Nat.mul_mod, hpow, one_mul, Nat.mod_mod,
        Nat.mod_eq_of_lt (hsmall.trans_lt hE)]
      exact hsmall
  obtain ⟨v, d, h0, hend, hsum, hstep⟩ := packCycle hE ha0 hpow horb
  let start : Fin a := ⟨0, ha0⟩
  let perm : Equiv.Perm (Fin a) := finRotate a
  let n (i : Fin a) (b : Bool) : Option (Fin a) := if b then some (perm i) else none
  have hval (i : Fin a) : (perm i).val = (i.val + 1) % a := by
    have hone : (1 : Fin a).val = 1 :=
      Nat.mod_eq_of_lt (show 1 < a by omega)
    change (finRotate a i).val = _
    rw [finRotate_apply, Fin.add_def, hone]
  have hn : terminates n (fun _ => false) := by
    intro i
    let f := fun o : Option (Fin a) => o.bind (fun k => n k false)
    change f^[a] (some i) = none
    calc
      _ = f^[(a-1)+1] (some i) := congrArg (fun k : ℕ => f^[k] (some i)) (by omega)
      _ = f^[a-1] none := by rw [Function.iterate_succ_apply]; rfl
      _ = none := Function.iterate_fixed (f := f) rfl _
  have hring : ring a n := by
    refine ⟨perm, fun _ => true, by intro i; simp [n], ?_⟩
    intro i j
    let k := j - i
    refine ⟨k.val, k.isLt, ?_⟩
    change (finRotate a : Fin a → Fin a)^[k.val] i = j
    rw [← finCycle_eq_finRotate_iterate, finCycle_apply]
    dsimp [k]
    rw [add_comm i, sub_add_cancel]
  have hnA : Absorbs n := ⟨fun _ => false, hn⟩
  let R (z : Fin a × Bool) (i : Fin a) (b : Bool) : ℝ := if z = (i,b) then 1 else 0
  let P (i : Fin a) (z : Fin a × Bool) : ℝ := mean n hnA (R z) i
  let D (z : Fin a × Bool) (j : Fin q) : ℕ := d z.1.val j
  have hweighted (w : (Fin a × Bool) → ℝ) (i : Fin a) :
      mean n hnA (fun k b => w (k,b)) i = ∑ z, P i z * w z := by
    have hR : (fun k b => w (k,b)) = ∑ z, w z • R z := by
      funext k b
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, R, mul_ite,
        mul_one, mul_zero, Fintype.sum_ite_eq']
    rw [hR, map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, P, mul_comm]
  let V (i : Fin a) (j : Fin q) : ℝ := (v i.val j : ℝ) / (q : ℝ)
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hV (j : Fin q) : Solves n (fun i b => (D (i,b) j : ℝ)) (fun i => V i j) := by
    intro i
    have hsucc : v (perm i).val j = v (i.val+1) j := by
      rw [hval]
      by_cases h : i.val+1 < a
      · rw [Nat.mod_eq_of_lt h]
      · have hi := i.isLt
        rw [show i.val+1 = a by omega, Nat.mod_self, h0, hend]
    have hs : 2 * (v i.val j : ℝ) = (q : ℝ) * (d i.val j : ℝ) + (v (i.val+1) j : ℝ) := by
      exact_mod_cast hstep _ i.isLt j
    simp only [Ends, n, Bool.false_eq_true, ite_false, ite_true, Option.elim_none,
      Option.elim_some, V, D, hsucc]
    field_simp [hqR] <;> linarith only [hs]
  refine ⟨start, n, P, D, hn, hring, ?_, ?_, ?_, ?_, ?_⟩
  · intro i z
    exact mean_nonneg n hnA (R z) (fun k b => by dsimp [R]; split <;> norm_num) i
  · intro i
    simpa only [mul_one, mean_const] using (hweighted (fun _ => 1) i).symm
  · intro i z
    simpa only [Fintype.sum_bool, P, R, Ends, add_comm] using mean_solves n hnA (R z) i
  · intro z
    exact hsum z.1.val z.1.isLt
  · intro j
    change (q : ℝ) * (∑ z, P start z * (D z j : ℝ)) = (E : ℝ)
    rw [← hweighted (fun z => (D z j : ℝ)) start, ← eqMean n hnA (hV j)]
    change (q : ℝ) * ((v 0 j : ℝ) / (q : ℝ)) = (E : ℝ)
    rw [h0]
    field_simp [hqR]

end PEqualNP.Outside.L_meta_29746

open PEqualNP.Outside.L_meta_29746

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_meta_29746 : ∀ a : ℕ, 2 ≤ a →
  let q := 2^a-1
  let E := 2^(a-1)
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
    let ideal := q*N*t-(2*t-q)*E
    let ring := fun (s : ℕ) (n : Fin s → Bool → Option (Fin s)) =>
      ∃ (perm : Equiv.Perm (Fin s)) (c : Fin s → Bool),
        (∀ i, n i (c i) = some (perm i) ∧ n i (!(c i)) = none) ∧
        ∀ i j : Fin s, ∃ k < s, (perm : Fin s → Fin s)^[k] i = j
    let law := fun (s : ℕ) (n : Fin s → Bool → Option (Fin s))
        (P : Fin s → (Fin s × Bool) → ℝ) =>
      (∃ p : Fin s → Bool, ∀ i : Fin s,
        (fun x : Option (Fin s) => x.bind (fun h => n h (p h)))^[s] (some i) = none) ∧
      (∀ i z, 0 ≤ P i z) ∧ (∀ i, (∑ z, P i z) = 1) ∧
      ∀ i z, 2*P i z = ∑ b : Bool,
        (n i b).elim (if z = (i,b) then 1 else 0) (fun h => P h z)
    (∀ (s : ℕ) (start : Fin s) (n : Fin s → Bool → Option (Fin s))
        (P : Fin s → (Fin s × Bool) → ℝ) (H : (Fin s × Bool) → X → X → Bool),
      law s n P → (∀ z, loss (H z) ∅ ≤ E) →
      let risk := fun D : Finset I => (q : ℝ)*∑ z, P start z*(loss (H z) D : ℝ)
      (∃ D : Finset I, D.card = t ∧ (ideal : ℝ) ≤ risk D) ∧
      ((∀ D : Finset I, D.card = t → risk D ≤ (ideal : ℝ)) →
        a ≤ s ∧ (s = a → ring s n))) ∧
    ∃ (start : Fin a) (n : Fin a → Bool → Option (Fin a))
        (P : Fin a → (Fin a × Bool) → ℝ) (C : (Fin a × Bool) → Circ),
      law a n P ∧ ring a n ∧ (∀ z, fits (C z)) ∧
      ∀ D : Finset I, D.card = t →
        (q : ℝ)*(∑ z, P start z*(loss (table (C z)) D : ℝ)) = (ideal : ℝ) := by
  classical
  intro a ha
  dsimp only
  intro N t hN ht htq base hb f hf
  obtain ⟨hq, he, hEq, _⟩ := powerFacts ha
  constructor
  · intro s start n P H hlaw herr
    have hP : exitLaw n P := hlaw
    have hg := weightedGame hq hN hEq ht htq f hf (table base) H (P start)
      (hP.2.2.1 start) (hP.2.1 start) herr
    refine ⟨hg.1, fun h => ?_⟩
    let j : Fin (2^a-1) := ⟨0, by omega⟩
    have hj := hg.2 h j
    let r := fun z : Fin s × Bool => (changed (table base) (H z) ∩ row f j).card
    let v := fun i => ∑ z, P i z * (r z : ℝ)
    have hnum := integralPolicy n (fun i b => r (i,b)) v (rewardLaw hP r) start
    obtain ⟨hs, hunique⟩ := stateCount ha hP.1 hj hnum
    refine ⟨hs, fun heq => ?_⟩
    obtain ⟨c,hc,hu⟩ := hunique heq
    exact uniqueBadRing n c hc hu
  · obtain ⟨start,n,P,d,hterm,hring,hP₀,hP₁,hP₂,hd,hbal⟩ := cycleWitness ha
    obtain ⟨C,hfits,heq⟩ := weightedCompile he hEq hN ht htq f hf base hb (P start) (hP₁ start) d hd hbal
    exact ⟨start,n,P,C,⟨⟨fun _ => false,hterm⟩,hP₀,hP₁,hP₂⟩,hring,hfits,heq⟩
