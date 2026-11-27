import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_779_aux

private lemma xor_comm' (x y : ℕ) : x ^^^ y = y ^^^ x := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_xor]
  cases x.testBit k <;> cases y.testBit k <;> rfl

private lemma xor_assoc' (x y z : ℕ) : (x ^^^ y) ^^^ z = x ^^^ (y ^^^ z) := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_xor]
  cases x.testBit k <;> cases y.testBit k <;> cases z.testBit k <;> rfl

private lemma xor_self' (x : ℕ) : x ^^^ x = 0 := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_xor, Nat.zero_testBit]
  cases x.testBit k <;> rfl

private lemma zero_xor' (x : ℕ) : 0 ^^^ x = x := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_xor, Nat.zero_testBit]
  cases x.testBit k <;> rfl

private lemma xor_zero' (x : ℕ) : x ^^^ 0 = x := by
  rw [xor_comm', zero_xor']

private lemma xor_cancel_left (x y : ℕ) : x ^^^ (x ^^^ y) = y := by
  rw [← xor_assoc', xor_self', zero_xor']

private lemma xor_cancel_right (x y : ℕ) : (x ^^^ y) ^^^ y = x := by
  rw [xor_assoc', xor_self', xor_zero']

private lemma testBit_div_two_pow (x i k : ℕ) : (x / 2 ^ i).testBit k = x.testBit (i + k) := by
  rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]

private lemma xor_mod_two_pow (x y i : ℕ) : (x ^^^ y) % 2 ^ i = (x % 2 ^ i) ^^^ (y % 2 ^ i) := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_xor, Nat.testBit_mod_two_pow]
  by_cases h : k < i <;> simp [h]

private lemma xor_div_two_pow (x y i : ℕ) : (x ^^^ y) / 2 ^ i = (x / 2 ^ i) ^^^ (y / 2 ^ i) := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_xor, testBit_div_two_pow]

private lemma mul_two_pow_mod (i m : ℕ) : (2 ^ i * m) % 2 ^ i = 0 :=
  Nat.mul_mod_right (2 ^ i) m

private lemma mul_two_pow_div (i m : ℕ) : (2 ^ i * m) / 2 ^ i = m :=
  Nat.mul_div_right m (Nat.two_pow_pos i)

private lemma eq_of_mod_zero_div_eq {x y i : ℕ}
    (hx : x % 2 ^ i = 0) (hy : y % 2 ^ i = 0) (hd : x / 2 ^ i = y / 2 ^ i) : x = y := by
  have h1 := Nat.div_add_mod x (2 ^ i)
  have h2 := Nat.div_add_mod y (2 ^ i)
  rw [hx, hd] at h1
  rw [hy] at h2
  omega

private lemma mod_two_pow_succ_zero_iff (x i : ℕ) :
    x % 2 ^ (i + 1) = 0 ↔ x % 2 ^ i = 0 ∧ (x / 2 ^ i) % 2 = 0 := by
  set p := 2 ^ i
  have hp : 0 < p := Nat.two_pow_pos i
  have hpow : 2 ^ (i + 1) = p * 2 := Nat.pow_succ 2 i
  have h1 : p * (x / p) + x % p = x := Nat.div_add_mod x p
  have h2 : 2 * ((x / p) / 2) + (x / p) % 2 = x / p := Nat.div_add_mod (x / p) 2
  have hr : x % p < p := Nat.mod_lt x hp
  have hq : (x / p) % 2 < 2 := Nat.mod_lt (x / p) (by omega)
  have hrem_lt : p * ((x / p) % 2) + x % p < p * 2 := by
    have hle : (x / p) % 2 ≤ 1 := by omega
    have hmul : p * ((x / p) % 2) ≤ p * 1 := Nat.mul_le_mul_left p hle
    omega
  have hx_eq : x = (p * 2) * ((x / p) / 2) + (p * ((x / p) % 2) + x % p) := by
    calc x = p * (x / p) + x % p := h1.symm
      _ = p * (2 * ((x / p) / 2) + (x / p) % 2) + x % p := by rw [h2]
      _ = (p * 2) * ((x / p) / 2) + (p * ((x / p) % 2) + x % p) := by ring
  have hmod : x % (p * 2) = p * ((x / p) % 2) + x % p := by
    conv_lhs => rw [hx_eq]
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hrem_lt]
  rw [hpow, hmod]
  constructor
  · intro h0
    have hr0 : x % p = 0 := by omega
    have hmul0 : p * ((x / p) % 2) = 0 := by omega
    have hq0 : (x / p) % 2 = 0 := by
      rcases Nat.mul_eq_zero.mp hmul0 with hpeq | hqeq
      · omega
      · exact hqeq
    exact ⟨hr0, hq0⟩
  · rintro ⟨hr0, hq0⟩
    rw [hr0, hq0]
    simp

private lemma div_two_pow_succ (x i : ℕ) : x / 2 ^ (i + 1) = (x / 2 ^ i) / 2 := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]

private lemma log2_two_pow (d : ℕ) : Nat.log2 (2 ^ d) = d := by
  induction d with
  | zero => decide
  | succ d ih =>
    have hpos : 0 < 2 ^ d := Nat.two_pow_pos d
    rw [Nat.log2_def]
    have hge : 2 ≤ 2 ^ (d + 1) := by
      rw [Nat.pow_succ]
      omega
    rw [if_pos hge, Nat.pow_succ, Nat.mul_div_cancel _ (by omega : 0 < 2), ih]

private lemma le_of_pow_two_le {a b : ℕ} (h : 2 ^ a ≤ 2 ^ b) : a ≤ b := by
  by_contra hlt
  have hba : b + 1 ≤ a := by omega
  have h1 : 2 ^ (b + 1) ≤ 2 ^ a := Nat.pow_le_pow_right (by omega : 0 < 2) hba
  have h2 : 0 < 2 ^ b := Nat.two_pow_pos b
  rw [Nat.pow_succ] at h1
  omega

private lemma eq_of_pow_two_eq {a b : ℕ} (h : 2 ^ a = 2 ^ b) : a = b :=
  le_antisymm (le_of_pow_two_le (le_of_eq h)) (le_of_pow_two_le (le_of_eq h.symm))

private lemma xor_lt_32 {x y : ℕ} (hx : x < 32) (hy : y < 32) : x ^^^ y < 32 := by
  have h1 : x < 2 ^ 5 := hx
  have h2 : y < 2 ^ 5 := hy
  exact Nat.xor_lt_two_pow h1 h2

private def IsXorSub (W : Finset ℕ) : Prop :=
  0 ∈ W ∧ ∀ x ∈ W, ∀ y ∈ W, x ^^^ y ∈ W

private def adjoinXor (g : ℕ) (W : Finset ℕ) : Finset ℕ :=
  W ∪ W.image (fun v => v ^^^ g)

private lemma mem_adjoinXor {g : ℕ} {W : Finset ℕ} {x : ℕ} :
    x ∈ adjoinXor g W ↔ x ∈ W ∨ ∃ v ∈ W, v ^^^ g = x := by
  simp [adjoinXor]

private lemma adjoinXor_isXorSub {g : ℕ} {W : Finset ℕ} (hW : IsXorSub W) :
    IsXorSub (adjoinXor g W) := by
  refine ⟨Finset.mem_union_left _ hW.1, ?_⟩
  intro x hx y hy
  rw [mem_adjoinXor] at hx hy ⊢
  rcases hx with hx | ⟨u, hu, rfl⟩
  · rcases hy with hy | ⟨v, hv, rfl⟩
    · exact Or.inl (hW.2 x hx y hy)
    · refine Or.inr ⟨x ^^^ v, hW.2 x hx v hv, ?_⟩
      exact xor_assoc' x v g
  · rcases hy with hy | ⟨v, hv, rfl⟩
    · refine Or.inr ⟨u ^^^ y, hW.2 u hu y hy, ?_⟩
      calc (u ^^^ y) ^^^ g = u ^^^ (y ^^^ g) := xor_assoc' u y g
        _ = u ^^^ (g ^^^ y) := by rw [xor_comm' y g]
        _ = (u ^^^ g) ^^^ y := (xor_assoc' u g y).symm
    · refine Or.inl ?_
      have heq : (u ^^^ g) ^^^ (v ^^^ g) = u ^^^ v := by
        calc (u ^^^ g) ^^^ (v ^^^ g) = ((u ^^^ g) ^^^ v) ^^^ g := (xor_assoc' (u ^^^ g) v g).symm
          _ = (u ^^^ (g ^^^ v)) ^^^ g := by rw [xor_assoc' u g v]
          _ = (u ^^^ (v ^^^ g)) ^^^ g := by rw [xor_comm' g v]
          _ = ((u ^^^ v) ^^^ g) ^^^ g := by rw [← xor_assoc' u v g]
          _ = u ^^^ v := xor_cancel_right (u ^^^ v) g
      rw [heq]
      exact hW.2 u hu v hv

private lemma adjoinXor_eq_self {g : ℕ} {W : Finset ℕ} (hW : IsXorSub W) (hg : g ∈ W) :
    adjoinXor g W = W := by
  ext x
  rw [mem_adjoinXor]
  constructor
  · rintro (hx | ⟨v, hv, rfl⟩)
    · exact hx
    · exact hW.2 v hv g hg
  · exact Or.inl

private lemma adjoinXor_card_not_mem {g : ℕ} {W : Finset ℕ} (hW : IsXorSub W) (hg : g ∉ W) :
    (adjoinXor g W).card = 2 * W.card := by
  have hdisj : Disjoint W (W.image (fun v => v ^^^ g)) := by
    rw [Finset.disjoint_left]
    intro x hx hximg
    rcases Finset.mem_image.mp hximg with ⟨v, hv, rfl⟩
    have hgv : g = v ^^^ (v ^^^ g) := (xor_cancel_left v g).symm
    rw [hgv] at hg
    exact hg (hW.2 v hv (v ^^^ g) hx)
  have himg : (W.image (fun v => v ^^^ g)).card = W.card := by
    apply Finset.card_image_of_injective
    intro u v huv
    have h := congrArg (fun z => z ^^^ g) huv
    simpa only [xor_cancel_right] using h
  rw [adjoinXor, Finset.card_union_of_disjoint hdisj, himg]
  omega

private lemma adjoinXor_card_pow2 {g : ℕ} {W : Finset ℕ} (hW : IsXorSub W)
    (hcard : ∃ d, W.card = 2 ^ d) : ∃ d', (adjoinXor g W).card = 2 ^ d' := by
  rcases hcard with ⟨d, hd⟩
  by_cases hg : g ∈ W
  · exact ⟨d, by rw [adjoinXor_eq_self hW hg, hd]⟩
  · refine ⟨d + 1, ?_⟩
    rw [adjoinXor_card_not_mem hW hg, hd, Nat.pow_succ]
    ring

private lemma adjoinXor_subset_range32 {g : ℕ} {W : Finset ℕ}
    (hW : W ⊆ Finset.range 32) (hg : g < 32) : adjoinXor g W ⊆ Finset.range 32 := by
  intro x hx
  rw [Finset.mem_range]
  rw [mem_adjoinXor] at hx
  rcases hx with hx | ⟨v, hv, rfl⟩
  · exact Finset.mem_range.mp (hW hx)
  · exact xor_lt_32 (Finset.mem_range.mp (hW hv)) hg

private lemma isXorSub_card_pow2_aux {S : Finset ℕ} (hS : IsXorSub S) :
    ∀ n (U : Finset ℕ) (d : ℕ),
      S.card - U.card = n → IsXorSub U → U ⊆ S → U.card = 2 ^ d → ∃ d', S.card = 2 ^ d' := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro U d hrem hU hsub hcard
    by_cases hSU : S ⊆ U
    · exact ⟨d, by rw [Finset.Subset.antisymm hSU hsub, hcard]⟩
    · rw [Finset.not_subset] at hSU
      rcases hSU with ⟨g, hgS, hgU⟩
      let U' := adjoinXor g U
      have hU' : IsXorSub U' := adjoinXor_isXorSub hU
      have hsub' : U' ⊆ S := by
        intro x hx
        rw [mem_adjoinXor] at hx
        rcases hx with hx | ⟨v, hv, rfl⟩
        · exact hsub hx
        · exact hS.2 v (hsub hv) g hgS
      have hcard' : U'.card = 2 ^ (d + 1) := by
        rw [adjoinXor_card_not_mem hU hgU, hcard, Nat.pow_succ]
        ring
      have hUpos : 0 < U.card := Finset.card_pos.mpr ⟨0, hU.1⟩
      have hle' : U'.card ≤ S.card := Finset.card_le_card hsub'
      have hcard_gt : U.card < U'.card := by
        rw [hcard, hcard', Nat.pow_succ]
        have := Nat.two_pow_pos d
        omega
      have hlt : S.card - U'.card < n := by omega
      exact ih (S.card - U'.card) hlt U' (d + 1) rfl hU' hsub' hcard'

private lemma isXorSub_card_pow2 {S : Finset ℕ} (hS : IsXorSub S) :
    ∃ d, S.card = 2 ^ d := by
  have h0 : IsXorSub ({0} : Finset ℕ) := by
    refine ⟨by simp, ?_⟩
    intro x hx y hy
    simp only [Finset.mem_singleton] at hx hy ⊢
    rw [hx, hy]
    rfl
  have hsub : ({0} : Finset ℕ) ⊆ S := by
    intro x hx
    simp only [Finset.mem_singleton] at hx
    rw [hx]
    exact hS.1
  exact isXorSub_card_pow2_aux hS (S.card - ({0} : Finset ℕ).card) {0} 0 rfl h0 hsub (by simp)

private lemma even_div2_step {U : Finset ℕ} (hU : IsXorSub U) :
    let even := U.filter (fun v => v % 2 = 0)
    let inc := if even = U then 0 else 1
    let S' := even.image (fun v => v / 2)
    IsXorSub S' ∧ (U ⊆ Finset.range 32 → S' ⊆ Finset.range 16) ∧ U.card = 2 ^ inc * S'.card := by
  dsimp only
  set even := U.filter (fun v => v % 2 = 0)
  set inc := if even = U then 0 else 1
  set S' := even.image (fun v => v / 2)
  have hS'_sub : IsXorSub S' := by
    refine ⟨?_, ?_⟩
    · refine Finset.mem_image.mpr ⟨0, ?_, by decide⟩
      simp [even, hU.1]
    · intro x hx y hy
      rcases Finset.mem_image.mp hx with ⟨u, hu, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨v, hv, rfl⟩
      simp only [even, Finset.mem_filter] at hu hv
      refine Finset.mem_image.mpr ⟨u ^^^ v, ?_, ?_⟩
      · simp only [even, Finset.mem_filter]
        refine ⟨hU.2 u hu.1 v hv.1, ?_⟩
        have hmod := xor_mod_two_pow u v 1
        simp only [pow_one] at hmod
        rw [hmod, hu.2, hv.2]
        rfl
      · have hdiv := xor_div_two_pow u v 1
        simp only [pow_one] at hdiv
        exact hdiv
  have hS'_range : U ⊆ Finset.range 32 → S' ⊆ Finset.range 16 := by
    intro hU32 x hx
    rcases Finset.mem_image.mp hx with ⟨u, hu, rfl⟩
    simp only [even, Finset.mem_filter] at hu
    have hu32 : u < 32 := Finset.mem_range.mp (hU32 hu.1)
    rw [Finset.mem_range]
    omega
  have hS'_card : S'.card = even.card := by
    apply Finset.card_image_of_injOn
    intro u hu v hv huv
    simp only [Finset.mem_coe, even, Finset.mem_filter] at hu hv
    have hu1 : u % 2 ^ 1 = 0 := by simpa using hu.2
    have hv1 : v % 2 ^ 1 = 0 := by simpa using hv.2
    have hd1 : u / 2 ^ 1 = v / 2 ^ 1 := by simpa using huv
    exact eq_of_mod_zero_div_eq hu1 hv1 hd1
  have hcard : U.card = 2 ^ inc * S'.card := by
    rw [hS'_card]
    by_cases heq : even = U
    · simp [inc, heq]
    · simp only [inc, heq, ↓reduceIte, pow_one]
      have hnotSub : ¬ U ⊆ even := by
        intro hsub
        exact heq (Finset.Subset.antisymm (Finset.filter_subset _ U) hsub)
      rw [Finset.not_subset] at hnotSub
      rcases hnotSub with ⟨w0, hw0U, hw0ne⟩
      have hw0mod : w0 % 2 = 1 := by
        have hne0 : ¬ w0 % 2 = 0 := by
          intro h0
          exact hw0ne (Finset.mem_filter.mpr ⟨hw0U, h0⟩)
        omega
      let odd := U.filter (fun v => ¬ v % 2 = 0)
      have hunion : even ∪ odd = U := by
        ext v
        simp only [even, odd, Finset.mem_union, Finset.mem_filter]
        tauto
      have hdisj : Disjoint even odd := by
        rw [Finset.disjoint_left]
        intro v hv1 hv2
        simp only [even, odd, Finset.mem_filter] at hv1 hv2
        exact hv2.2 hv1.2
      have hbij : even.card = odd.card := by
        refine Finset.card_bij (fun v _ => v ^^^ w0) ?_ ?_ ?_
        · intro v hv
          simp only [even, odd, Finset.mem_filter] at hv ⊢
          refine ⟨hU.2 v hv.1 w0 hw0U, ?_⟩
          have hmod := xor_mod_two_pow v w0 1
          simp only [pow_one] at hmod
          rw [hmod, hv.2, hw0mod]
          decide
        · intro u _ v _ huv
          have h := congrArg (fun z => z ^^^ w0) huv
          simpa only [xor_cancel_right] using h
        · intro u hu
          simp only [odd, Finset.mem_filter] at hu
          have humod : u % 2 = 1 := by omega
          refine ⟨u ^^^ w0, ?_, xor_cancel_right u w0⟩
          simp only [even, Finset.mem_filter]
          refine ⟨hU.2 u hu.1 w0 hw0U, ?_⟩
          have hmod := xor_mod_two_pow u w0 1
          simp only [pow_one] at hmod
          rw [hmod, humod, hw0mod]
          decide
      rw [← hunion, Finset.card_union_of_disjoint hdisj, ← hbij]
      omega
  exact ⟨hS'_sub, hS'_range, hcard⟩

private lemma orbit_kernel_card {W : Finset ℕ} (hW : IsXorSub W) (i : ℕ) :
    W.card = (W.image (fun x => x % 2 ^ i)).card * (W.filter (fun x => x % 2 ^ i = 0)).card := by
  set Im := W.image (fun x => x % 2 ^ i)
  set Ker := W.filter (fun x => x % 2 ^ i = 0)
  have hpart : W = Im.biUnion (fun r => W.filter (fun x => x % 2 ^ i = r)) := by
    ext x
    simp only [Im, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
    constructor
    · intro hx
      exact ⟨x % 2 ^ i, ⟨x, hx, rfl⟩, hx, rfl⟩
    · rintro ⟨_, _, hx, _⟩
      exact hx
  have hdisj : (Im : Set ℕ).PairwiseDisjoint (fun r => W.filter (fun x => x % 2 ^ i = r)) := by
    intro r1 _ r2 _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_filter] at hx1 hx2
    exact hne (hx1.2.symm.trans hx2.2)
  have hfiber : ∀ r ∈ Im, (W.filter (fun x => x % 2 ^ i = r)).card = Ker.card := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨xr, hxrW, hxrMod⟩
    symm
    refine Finset.card_bij (fun k _ => xr ^^^ k) ?_ ?_ ?_
    · intro k hk
      simp only [Ker, Finset.mem_filter] at hk ⊢
      refine ⟨hW.2 xr hxrW k hk.1, ?_⟩
      rw [xor_mod_two_pow, hxrMod, hk.2, xor_zero']
    · intro k1 _ k2 _ hkeq
      have h := congrArg (fun z => xr ^^^ z) hkeq
      simpa only [xor_cancel_left] using h
    · intro y hy
      simp only [Finset.mem_filter] at hy
      refine ⟨xr ^^^ y, ?_, xor_cancel_left xr y⟩
      simp only [Ker, Finset.mem_filter]
      refine ⟨hW.2 xr hxrW y hy.1, ?_⟩
      rw [xor_mod_two_pow, hxrMod, hy.2, xor_self']
  calc W.card = (Im.biUnion (fun r => W.filter (fun x => x % 2 ^ i = r))).card := by rw [← hpart]
    _ = ∑ r ∈ Im, (W.filter (fun x => x % 2 ^ i = r)).card := Finset.card_biUnion hdisj
    _ = ∑ _r ∈ Im, Ker.card := Finset.sum_congr rfl hfiber
    _ = Im.card * Ker.card := by simp

private def advance (t : ℕ) (st : ℕ × Finset ℕ) (atSite : Fin t → ℕ) : ℕ × Finset ℕ :=
  let extended := (List.finRange t).foldl (fun (s : Finset ℕ) j =>
    s ∪ s.image (fun v => v ^^^ atSite j)) st.2
  let even := extended.filter (fun v => v % 2 = 0)
  (st.1 + (if even = extended then 0 else 1), even.image (fun v => v / 2))

private def selectMask (u v : Fin 32) (c : Fin 3) : ℕ :=
  if c.val = 0 then u.val else if c.val = 1 then v.val else u.val ^^^ v.val

private lemma selectMask_lt_32 (u v : Fin 32) (c : Fin 3) : selectMask u v c < 32 := by
  unfold selectMask
  split_ifs
  · exact u.isLt
  · exact v.isLt
  · exact xor_lt_32 u.isLt v.isLt

private def xorSum (A B : Finset ℕ) : Finset ℕ :=
  A.biUnion (fun x => B.image (fun y => x ^^^ y))

private lemma mem_xorSum {A B : Finset ℕ} {z : ℕ} :
    z ∈ xorSum A B ↔ ∃ x ∈ A, ∃ y ∈ B, x ^^^ y = z := by
  simp [xorSum]

private lemma xorSum_singleton_zero (S : Finset ℕ) : xorSum S {0} = S := by
  ext z
  rw [mem_xorSum]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    simp only [Finset.mem_singleton] at hy
    rw [hy, xor_zero']
    exact hx
  · intro hz
    exact ⟨z, hz, 0, Finset.mem_singleton_self 0, xor_zero' z⟩

private lemma adjoinXor_xorSum (g : ℕ) (S K : Finset ℕ) :
    adjoinXor g (xorSum S K) = xorSum S (adjoinXor g K) := by
  ext z
  simp only [mem_adjoinXor, mem_xorSum]
  constructor
  · rintro (⟨x, hx, y, hy, rfl⟩ | ⟨w, ⟨x, hx, y, hy, rfl⟩, rfl⟩)
    · exact ⟨x, hx, y, Or.inl hy, rfl⟩
    · refine ⟨x, hx, y ^^^ g, Or.inr ⟨y, hy, rfl⟩, ?_⟩
      exact (xor_assoc' x y g).symm
  · rintro ⟨x, hx, y, hy | ⟨u, hu, rfl⟩, rfl⟩
    · exact Or.inl ⟨x, hx, y, hy, rfl⟩
    · refine Or.inr ⟨x ^^^ u, ⟨x, hx, u, hu, rfl⟩, ?_⟩
      exact xor_assoc' x u g

private lemma subset_xorSum_right {S K : Finset ℕ} (h0 : 0 ∈ S) : K ⊆ xorSum S K := by
  intro y hy
  exact mem_xorSum.mpr ⟨0, h0, y, hy, zero_xor' y⟩

private lemma card_xorSum_le (A B : Finset ℕ) : (xorSum A B).card ≤ A.card * B.card := by
  unfold xorSum
  apply Finset.card_biUnion_le_card_mul
  intro x _
  exact Finset.card_image_le

private lemma adjoinXor_mul_two_pow_image_mod (i g : ℕ) (W : Finset ℕ) :
    (adjoinXor (2 ^ i * g) W).image (fun x => x % 2 ^ i) = W.image (fun x => x % 2 ^ i) := by
  ext r
  simp only [Finset.mem_image, mem_adjoinXor]
  constructor
  · rintro ⟨x, hx | ⟨v, hv, rfl⟩, rfl⟩
    · exact ⟨x, hx, rfl⟩
    · refine ⟨v, hv, ?_⟩
      rw [xor_mod_two_pow, mul_two_pow_mod, xor_zero']
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, Or.inl hx, rfl⟩

private lemma adjoinXor_mul_two_pow_kernel_div (i g : ℕ) (W : Finset ℕ) :
    ((adjoinXor (2 ^ i * g) W).filter (fun x => x % 2 ^ i = 0)).image (fun x => x / 2 ^ i) =
    adjoinXor g ((W.filter (fun x => x % 2 ^ i = 0)).image (fun x => x / 2 ^ i)) := by
  ext y
  simp only [mem_adjoinXor, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨x, ⟨hx | ⟨v, hv, rfl⟩, hxmod⟩, rfl⟩
    · exact Or.inl ⟨x, ⟨hx, hxmod⟩, rfl⟩
    · have hvmod : v % 2 ^ i = 0 := by
        rw [xor_mod_two_pow, mul_two_pow_mod, xor_zero'] at hxmod
        exact hxmod
      refine Or.inr ⟨v / 2 ^ i, ⟨v, ⟨hv, hvmod⟩, rfl⟩, ?_⟩
      rw [xor_div_two_pow, mul_two_pow_div]
  · rintro (⟨v, ⟨hv, hvmod⟩, rfl⟩ | ⟨u, ⟨v, ⟨hv, hvmod⟩, rfl⟩, rfl⟩)
    · exact ⟨v, ⟨Or.inl hv, hvmod⟩, rfl⟩
    · refine ⟨v ^^^ (2 ^ i * g), ⟨Or.inr ⟨v, hv, rfl⟩, ?_⟩, ?_⟩
      · rw [xor_mod_two_pow, mul_two_pow_mod, xor_zero']
        exact hvmod
      · rw [xor_div_two_pow, mul_two_pow_div]

private lemma filter_div_two_pow_succ (i : ℕ) (W : Finset ℕ) :
    (W.filter (fun x => x % 2 ^ (i + 1) = 0)).image (fun x => x / 2 ^ (i + 1)) =
    (((W.filter (fun x => x % 2 ^ i = 0)).image (fun x => x / 2 ^ i)).filter
      (fun v => v % 2 = 0)).image (fun v => v / 2) := by
  ext y
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨x, ⟨hxW, hxmod⟩, rfl⟩
    rw [mod_two_pow_succ_zero_iff] at hxmod
    exact ⟨x / 2 ^ i, ⟨⟨x, ⟨hxW, hxmod.1⟩, rfl⟩, hxmod.2⟩, (div_two_pow_succ x i).symm⟩
  · rintro ⟨u, ⟨⟨x, ⟨hxW, hxmod1⟩, rfl⟩, hxmod2⟩, rfl⟩
    refine ⟨x, ⟨hxW, (mod_two_pow_succ_zero_iff x i).mpr ⟨hxmod1, hxmod2⟩⟩, ?_⟩
    exact div_two_pow_succ x i

private def foldAdjoin (t : ℕ) (f : Fin t → ℕ) (L : List (Fin t)) (W : Finset ℕ) : Finset ℕ :=
  L.foldl (fun w j => adjoinXor (f j) w) W

private lemma foldAdjoin_isXorSub (t : ℕ) (f : Fin t → ℕ) (L : List (Fin t)) (W : Finset ℕ)
    (hW : IsXorSub W) : IsXorSub (foldAdjoin t f L W) := by
  induction L generalizing W with
  | nil => exact hW
  | cons j rest ih => exact ih (adjoinXor (f j) W) (adjoinXor_isXorSub hW)

private lemma foldAdjoin_card_pow2 (t : ℕ) (f : Fin t → ℕ) (L : List (Fin t)) (W : Finset ℕ)
    (hW : IsXorSub W) (hc : ∃ d, W.card = 2 ^ d) : ∃ d', (foldAdjoin t f L W).card = 2 ^ d' := by
  induction L generalizing W with
  | nil => exact hc
  | cons j rest ih =>
    exact ih (adjoinXor (f j) W) (adjoinXor_isXorSub hW) (adjoinXor_card_pow2 hW hc)

private lemma foldAdjoin_subset_range32 (t : ℕ) (f : Fin t → ℕ) (L : List (Fin t)) (W : Finset ℕ)
    (hW : W ⊆ Finset.range 32) (hf : ∀ j, f j < 32) :
    foldAdjoin t f L W ⊆ Finset.range 32 := by
  induction L generalizing W with
  | nil => exact hW
  | cons j rest ih =>
    exact ih (adjoinXor (f j) W) (adjoinXor_subset_range32 hW (hf j))

private lemma foldAdjoin_xorSum (t : ℕ) (f : Fin t → ℕ) (L : List (Fin t)) (S K : Finset ℕ) :
    foldAdjoin t f L (xorSum S K) = xorSum S (foldAdjoin t f L K) := by
  induction L generalizing K with
  | nil => rfl
  | cons j rest ih =>
    change foldAdjoin t f rest (adjoinXor (f j) (xorSum S K)) =
      xorSum S (foldAdjoin t f rest (adjoinXor (f j) K))
    rw [adjoinXor_xorSum, ih]

private lemma foldAdjoin_mul_two_pow_image_mod (t i : ℕ) (m : Fin t → ℕ) (L : List (Fin t))
    (W : Finset ℕ) :
    (foldAdjoin t (fun j => 2 ^ i * m j) L W).image (fun x => x % 2 ^ i) =
    W.image (fun x => x % 2 ^ i) := by
  induction L generalizing W with
  | nil => rfl
  | cons j rest ih =>
    change (foldAdjoin t (fun j => 2 ^ i * m j) rest (adjoinXor (2 ^ i * m j) W)).image
      (fun x => x % 2 ^ i) = _
    rw [ih, adjoinXor_mul_two_pow_image_mod]

private lemma foldAdjoin_mul_two_pow_kernel_div (t i : ℕ) (m : Fin t → ℕ) (L : List (Fin t))
    (W : Finset ℕ) :
    ((foldAdjoin t (fun j => 2 ^ i * m j) L W).filter (fun x => x % 2 ^ i = 0)).image
      (fun x => x / 2 ^ i) =
    foldAdjoin t m L ((W.filter (fun x => x % 2 ^ i = 0)).image (fun x => x / 2 ^ i)) := by
  induction L generalizing W with
  | nil => rfl
  | cons j rest ih =>
    change ((foldAdjoin t (fun j => 2 ^ i * m j) rest (adjoinXor (2 ^ i * m j) W)).filter
      (fun x => x % 2 ^ i = 0)).image (fun x => x / 2 ^ i) = _
    rw [ih, adjoinXor_mul_two_pow_kernel_div]
    rfl

private def stepW (t i : ℕ) (m : Fin t → ℕ) (W : Finset ℕ) : Finset ℕ :=
  foldAdjoin t (fun j => 2 ^ i * m j) (List.finRange t) W

private def runWIdx (t : ℕ) : ℕ → Finset ℕ → List (Fin t → ℕ) → Finset ℕ
  | _, W, [] => W
  | i, W, m :: rs => runWIdx t (i + 1) (stepW t i m W) rs

private def runW (t : ℕ) (S : Finset ℕ) (ms : List (Fin t → ℕ)) : Finset ℕ :=
  runWIdx t 0 S ms

private lemma runWIdx_append (t i : ℕ) (W : Finset ℕ) (ms : List (Fin t → ℕ)) (m : Fin t → ℕ) :
    runWIdx t i W (ms ++ [m]) = stepW t (i + ms.length) m (runWIdx t i W ms) := by
  induction ms generalizing i W with
  | nil => simp [runWIdx]
  | cons m0 rs ih =>
    simp only [List.cons_append, runWIdx, List.length_cons]
    rw [ih]
    congr 1
    omega

private lemma runW_append (t : ℕ) (S : Finset ℕ) (ms : List (Fin t → ℕ)) (m : Fin t → ℕ) :
    runW t S (ms ++ [m]) = stepW t ms.length m (runW t S ms) := by
  unfold runW
  rw [runWIdx_append, Nat.zero_add]

private def runSt (t : ℕ) (S : Finset ℕ) (ms : List (Fin t → ℕ)) : ℕ × Finset ℕ :=
  ms.foldl (advance t) (0, S)

private lemma card_kernel_div_eq (i : ℕ) (W : Finset ℕ) :
    ((W.filter (fun x => x % 2 ^ i = 0)).image (fun x => x / 2 ^ i)).card =
    (W.filter (fun x => x % 2 ^ i = 0)).card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  simp only [Finset.mem_coe, Finset.mem_filter] at hx hy
  exact eq_of_mod_zero_div_eq hx.2 hy.2 hxy

private lemma runW_runSt_inv (t : ℕ) (S : Finset ℕ) (hS : IsXorSub S) (hS16 : S ⊆ Finset.range 16)
    (ms : List (Fin t → ℕ)) (hms : ∀ m ∈ ms, ∀ j, m j < 32) :
    IsXorSub (runW t S ms) ∧
    (∃ d, (runW t S ms).card = 2 ^ d) ∧
    IsXorSub (runSt t S ms).2 ∧
    (runSt t S ms).2 ⊆ Finset.range 16 ∧
    (runW t S ms).card = 2 ^ (runSt t S ms).1 * (runSt t S ms).2.card ∧
    (runSt t S ms).2 =
      ((runW t S ms).filter (fun x => x % 2 ^ ms.length = 0)).image (fun x => x / 2 ^ ms.length) ∧
    runW t S ms = xorSum S (runW t {0} ms) := by
  induction ms using List.reverseRecOn with
  | nil =>
    refine ⟨hS, isXorSub_card_pow2 hS, hS, hS16, ?_, ?_, ?_⟩
    · simp [runW, runWIdx, runSt]
    · simp only [runW, runWIdx, runSt, List.foldl_nil, List.length_nil, pow_zero, Nat.mod_one,
        Nat.div_one]
      ext x
      simp
    · simp only [runW, runWIdx]
      exact (xorSum_singleton_zero S).symm
  | append_singleton ms m ih =>
    have hms_prev : ∀ m' ∈ ms, ∀ j, m' j < 32 := fun m' hm' => hms m' (List.mem_append_left _ hm')
    have hm : ∀ j, m j < 32 := hms m (List.mem_append_right _ (List.mem_singleton_self m))
    rcases ih hms_prev with ⟨hW_sub, hW_pow, hst_sub, hst_16, hcard_eq, hker_eq, hxor_eq⟩
    set i := ms.length
    set W := runW t S ms
    set W' := stepW t i m W
    set st := runSt t S ms
    set st' := advance t st m
    have hrunW' : runW t S (ms ++ [m]) = W' := runW_append t S ms m
    have hrunSt' : runSt t S (ms ++ [m]) = st' := by
      simp only [runSt, List.foldl_append, List.foldl_cons, List.foldl_nil, st, st']
    have hW'_sub : IsXorSub W' := foldAdjoin_isXorSub t _ _ W hW_sub
    have hW'_pow : ∃ d, W'.card = 2 ^ d := foldAdjoin_card_pow2 t _ _ W hW_sub hW_pow
    have hW'_xor : runW t S (ms ++ [m]) = xorSum S (runW t {0} (ms ++ [m])) := by
      rw [runW_append, runW_append]
      change stepW t i m W = xorSum S (stepW t i m (runW t {0} ms))
      rw [hxor_eq]
      exact foldAdjoin_xorSum t (fun j => 2 ^ i * m j) (List.finRange t) S (runW t {0} ms)
    set extended := foldAdjoin t m (List.finRange t) st.2
    have hext_sub : IsXorSub extended := foldAdjoin_isXorSub t m (List.finRange t) st.2 hst_sub
    have hst_32 : st.2 ⊆ Finset.range 32 := fun x hx =>
      Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp (hst_16 hx)) (by omega))
    have hext_32 : extended ⊆ Finset.range 32 :=
      foldAdjoin_subset_range32 t m (List.finRange t) st.2 hst_32 hm
    rcases even_div2_step hext_sub with ⟨hst'_sub, hst'_16_fn, hext_card⟩
    have hst'_16 : st'.2 ⊆ Finset.range 16 := hst'_16_fn hext_32
    have hker'_eq :
        ((W'.filter (fun x => x % 2 ^ i = 0)).image (fun x => x / 2 ^ i)) = extended := by
      unfold W' stepW extended
      rw [foldAdjoin_mul_two_pow_kernel_div, ← hker_eq]
    have him_eq :
        W'.image (fun x => x % 2 ^ i) = W.image (fun x => x % 2 ^ i) :=
      foldAdjoin_mul_two_pow_image_mod t i m (List.finRange t) W
    have hker_card : (W.filter (fun x => x % 2 ^ i = 0)).card = st.2.card := by
      rw [hker_eq, card_kernel_div_eq]
    have hker'_card : (W'.filter (fun x => x % 2 ^ i = 0)).card = extended.card := by
      rw [← hker'_eq, card_kernel_div_eq]
    have hokW := orbit_kernel_card hW_sub i
    have hokW' := orbit_kernel_card hW'_sub i
    have hst2_pos : 0 < st.2.card := Finset.card_pos.mpr ⟨0, hst_sub.1⟩
    have him_card : (W.image (fun x => x % 2 ^ i)).card = 2 ^ st.1 := by
      have hmul : (W.image (fun x => x % 2 ^ i)).card * st.2.card = 2 ^ st.1 * st.2.card := by
        calc (W.image (fun x => x % 2 ^ i)).card * st.2.card
            = (W.image (fun x => x % 2 ^ i)).card * (W.filter (fun x => x % 2 ^ i = 0)).card := by
              rw [hker_card]
          _ = W.card := hokW.symm
          _ = 2 ^ st.1 * st.2.card := hcard_eq
      exact Nat.eq_of_mul_eq_mul_right hst2_pos hmul
    have hcard'_eq : W'.card = 2 ^ st'.1 * st'.2.card := by
      rw [hokW', him_eq, him_card, hker'_card, hext_card]
      change 2 ^ st.1 * (2 ^ (if extended.filter (fun v => v % 2 = 0) = extended then 0 else 1) *
        st'.2.card) = 2 ^ (st.1 + (if extended.filter (fun v => v % 2 = 0) = extended then 0 else 1)) *
        st'.2.card
      rw [← mul_assoc, ← Nat.pow_add]
    have hker'_succ : st'.2 =
        ((W'.filter (fun x => x % 2 ^ (ms ++ [m]).length = 0)).image
          (fun x => x / 2 ^ (ms ++ [m]).length)) := by
      have hlen : (ms ++ [m]).length = i + 1 := by simp [i]
      rw [hlen, filter_div_two_pow_succ, hker'_eq]
      rfl
    rw [hrunW', hrunSt']
    refine ⟨hW'_sub, hW'_pow, hst'_sub, hst'_16, hcard'_eq, hker'_succ, ?_⟩
    rw [← hrunW']
    exact hW'_xor

private def costFrom {t : ℕ} (a b : Fin t → Fin 32) (S : Finset ℕ)
    (h : ℕ) (pick : Fin h → Fin t → Fin 3) : ℕ :=
  let last := (List.finRange h).foldl (fun st i =>
    advance t st (fun j => selectMask (a j) (b j) (pick i j))) ((0, S) : ℕ × Finset ℕ)
  last.1 + Nat.log2 last.2.card

private lemma runW_card_eq_two_pow_costFrom {t : ℕ} (a b : Fin t → Fin 32) (S : Finset ℕ)
    (hS : IsXorSub S) (hS16 : S ⊆ Finset.range 16)
    (h : ℕ) (pick : Fin h → Fin t → Fin 3) :
    let ms := (List.finRange h).map (fun i j => selectMask (a j) (b j) (pick i j))
    (runW t S ms).card = 2 ^ costFrom a b S h pick := by
  intro ms
  have hms : ∀ m ∈ ms, ∀ j, m j < 32 := by
    intro m hm j
    rcases List.mem_map.mp hm with ⟨i, _, rfl⟩
    exact selectMask_lt_32 (a j) (b j) (pick i j)
  rcases runW_runSt_inv t S hS hS16 ms hms with ⟨_, ⟨dW, hdW⟩, hst_sub, _, hcard_eq, _, _⟩
  rcases isXorSub_card_pow2 hst_sub with ⟨dS, hdS⟩
  have hfold : runSt t S ms =
      (List.finRange h).foldl (fun st i =>
        advance t st (fun j => selectMask (a j) (b j) (pick i j))) (0, S) := by
    simp only [runSt, ms, List.foldl_map]
  have hcost : costFrom a b S h pick = (runSt t S ms).1 + dS := by
    unfold costFrom
    dsimp only
    rw [← hfold, hdS, log2_two_pow]
  rw [hcost, Nat.pow_add, ← hdS, ← hcard_eq]

private lemma costFrom_discrepancy {t : ℕ} (a b : Fin t → Fin 32) (S : Finset ℕ)
    (hS : IsXorSub S) (hS16 : S ⊆ Finset.range 16)
    (h : ℕ) (pick : Fin h → Fin t → Fin 3) :
    costFrom a b {0} h pick ≤ costFrom a b S h pick ∧
    costFrom a b S h pick ≤ costFrom a b {0} h pick + 4 := by
  let ms := (List.finRange h).map (fun i j => selectMask (a j) (b j) (pick i j))
  have hms : ∀ m ∈ ms, ∀ j, m j < 32 := by
    intro m hm j
    rcases List.mem_map.mp hm with ⟨i, _, rfl⟩
    exact selectMask_lt_32 (a j) (b j) (pick i j)
  have h0sub : IsXorSub ({0} : Finset ℕ) := by
    refine ⟨by simp, ?_⟩
    intro x hx y hy
    simp only [Finset.mem_singleton] at hx hy ⊢
    rw [hx, hy]
    rfl
  have h016 : ({0} : Finset ℕ) ⊆ Finset.range 16 := by
    intro x hx
    simp only [Finset.mem_singleton] at hx
    rw [hx, Finset.mem_range]
    omega
  have hcS : (runW t S ms).card = 2 ^ costFrom a b S h pick :=
    runW_card_eq_two_pow_costFrom a b S hS hS16 h pick
  have hc0 : (runW t {0} ms).card = 2 ^ costFrom a b {0} h pick :=
    runW_card_eq_two_pow_costFrom a b {0} h0sub h016 h pick
  have hxor : runW t S ms = xorSum S (runW t {0} ms) :=
    (runW_runSt_inv t S hS hS16 ms hms).2.2.2.2.2.2
  constructor
  · apply le_of_pow_two_le
    rw [← hc0, ← hcS, hxor]
    exact Finset.card_le_card (subset_xorSum_right hS.1)
  · apply le_of_pow_two_le
    rw [← hcS, hxor, Nat.pow_add, ← hc0]
    have hS_le : S.card ≤ 16 := by
      calc S.card ≤ (Finset.range 16).card := Finset.card_le_card hS16
        _ = 16 := Finset.card_range 16
    calc (xorSum S (runW t {0} ms)).card
        ≤ S.card * (runW t {0} ms).card := card_xorSum_le S (runW t {0} ms)
      _ ≤ 16 * (runW t {0} ms).card := Nat.mul_le_mul_right _ hS_le
      _ = (runW t {0} ms).card * 2 ^ 4 := by ring

private lemma advance_add (t c : ℕ) (st : ℕ × Finset ℕ) (m : Fin t → ℕ) :
    advance t (c + st.1, st.2) m = (c + (advance t st m).1, (advance t st m).2) := by
  simp only [advance, Nat.add_assoc]

private lemma foldl_advance_add (t c : ℕ) (ms : List (Fin t → ℕ)) (st : ℕ × Finset ℕ) :
    ms.foldl (advance t) (c + st.1, st.2) =
      (c + (ms.foldl (advance t) st).1, (ms.foldl (advance t) st).2) := by
  induction ms generalizing st with
  | nil => rfl
  | cons m rs ih =>
    simp only [List.foldl_cons, advance_add]
    exact ih (advance t st m)

private lemma foldl_succ_eq {t : ℕ} (a b : Fin t → Fin 32) (S : Finset ℕ)
    (h : ℕ) (pick : Fin (h + 1) → Fin t → Fin 3) :
    let st1 := advance t (0, S) (fun j => selectMask (a j) (b j) (pick 0 j))
    let tail := (List.finRange h).foldl (fun st i =>
      advance t st (fun j => selectMask (a j) (b j) (pick i.succ j))) (0, st1.2)
    (List.finRange (h + 1)).foldl (fun st i =>
      advance t st (fun j => selectMask (a j) (b j) (pick i j))) (0, S) =
      (st1.1 + tail.1, tail.2) := by
  intro st1 tail
  rw [List.finRange_succ, List.foldl_cons, List.foldl_map]
  set ms := (List.finRange h).map (fun i j => selectMask (a j) (b j) (pick i.succ j))
  have htail : ms.foldl (advance t) (0, st1.2) = tail := by
    simp only [ms, tail, List.foldl_map]
  have hhead : ms.foldl (advance t) (st1.1 + 0, st1.2) =
      (List.finRange h).foldl (fun st i =>
        advance t st (fun j => selectMask (a j) (b j) (pick i.succ j))) st1 := by
    simp only [ms, List.foldl_map, Nat.add_zero]
  rw [← hhead, foldl_advance_add t st1.1 ms (0, st1.2), htail]

private lemma costFrom_succ {t : ℕ} (a b : Fin t → Fin 32) (S : Finset ℕ)
    (h : ℕ) (pick : Fin (h + 1) → Fin t → Fin 3) :
    let st1 := advance t (0, S) (fun j => selectMask (a j) (b j) (pick 0 j))
    costFrom a b S (h + 1) pick = st1.1 + costFrom a b st1.2 h (fun i => pick i.succ) := by
  intro st1
  unfold costFrom
  dsimp only
  rw [foldl_succ_eq]
  exact Nat.add_assoc _ _ _

private abbrev XSub := { S : Finset ℕ // IsXorSub S ∧ S ⊆ Finset.range 16 }

private lemma xsub_isXorSub (S : XSub) : IsXorSub S.val := S.property.1

private lemma xsub_subset_16 (S : XSub) : S.val ⊆ Finset.range 16 := S.property.2

private lemma xsub_finite : Finite XSub := by
  refine Finite.of_injective (fun (S : XSub) (k : Fin 16) => decide (k.val ∈ S.val)) ?_
  intro S1 S2 h
  apply Subtype.ext
  ext x
  by_cases hx : x < 16
  · have hk := congrFun h ⟨x, hx⟩
    simpa using hk
  · constructor
    · intro h1
      have := Finset.mem_range.mp (S1.property.2 h1)
      omega
    · intro h2
      have := Finset.mem_range.mp (S2.property.2 h2)
      omega

private def S0 : XSub :=
  ⟨{0}, by
    constructor
    · refine ⟨by simp, ?_⟩
      intro x hx y hy
      simp only [Finset.mem_singleton] at hx hy ⊢
      rw [hx, hy]
      rfl
    · intro x hx
      simp only [Finset.mem_singleton] at hx
      rw [hx, Finset.mem_range]
      omega⟩

private def nextX {t : ℕ} (a b : Fin t → Fin 32) (S : XSub) (c0 : Fin t → Fin 3) : XSub :=
  ⟨(advance t (0, S.val) (fun j => selectMask (a j) (b j) (c0 j))).2, by
    have hms : ∀ m ∈ [(fun j => selectMask (a j) (b j) (c0 j))], ∀ j, m j < 32 := by
      intro m hm j
      simp only [List.mem_singleton] at hm
      rw [hm]
      exact selectMask_lt_32 (a j) (b j) (c0 j)
    have hinv := runW_runSt_inv t S.val (xsub_isXorSub S) (xsub_subset_16 S)
      [(fun j => selectMask (a j) (b j) (c0 j))] hms
    exact ⟨hinv.2.2.1, hinv.2.2.2.1⟩⟩

private def incX {t : ℕ} (a b : Fin t → Fin 32) (S : XSub) (c0 : Fin t → Fin 3) : ℕ :=
  (advance t (0, S.val) (fun j => selectMask (a j) (b j) (c0 j))).1

private def minVal {α : Type*} (s : Finset α) (hs : s.Nonempty) (f : α → ℕ) : ℕ :=
  (s.image f).min' (hs.image f)

private lemma minVal_le {α : Type*} (s : Finset α) (hs : s.Nonempty) (f : α → ℕ)
    {a : α} (ha : a ∈ s) : minVal s hs f ≤ f a :=
  Finset.min'_le (s.image f) (f a) (Finset.mem_image_of_mem f ha)

private lemma exists_eq_minVal {α : Type*} (s : Finset α) (hs : s.Nonempty) (f : α → ℕ) :
    ∃ a ∈ s, f a = minVal s hs f :=
  Finset.mem_image.mp (Finset.min'_mem (s.image f) (hs.image f))

private lemma le_minVal {α : Type*} (s : Finset α) (hs : s.Nonempty) (f : α → ℕ) {d : ℕ}
    (hd : ∀ a ∈ s, d ≤ f a) : d ≤ minVal s hs f := by
  apply Finset.le_min'
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨a, ha, rfl⟩
  exact hd a ha

private lemma minVal_add_right {α : Type*} (s : Finset α) (hs : s.Nonempty) (f : α → ℕ) (r : ℕ) :
    minVal s hs (fun a => f a + r) = minVal s hs f + r := by
  apply le_antisymm
  · rcases exists_eq_minVal s hs f with ⟨a, ha, hfa⟩
    rw [← hfa]
    exact minVal_le s hs (fun x => f x + r) ha
  · apply le_minVal
    intro a ha
    exact Nat.add_le_add_right (minVal_le s hs f ha) r

private def M {t : ℕ} (a b : Fin t → Fin 32) : ℕ → XSub → ℕ
  | 0, S => Nat.log2 S.val.card
  | h + 1, S =>
    minVal (Finset.univ : Finset (Fin t → Fin 3))
      ⟨fun _ => 0, Finset.mem_univ _⟩
      (fun c0 => incX a b S c0 + M a b h (nextX a b S c0))

private lemma M_spec {t : ℕ} (a b : Fin t → Fin 32) :
    ∀ h (S : XSub),
      (∀ pick : Fin h → Fin t → Fin 3, M a b h S ≤ costFrom a b S.val h pick) ∧
      (∃ pick : Fin h → Fin t → Fin 3, costFrom a b S.val h pick = M a b h S) := by
  intro h
  induction h with
  | zero =>
    intro S
    refine ⟨?_, ⟨fun _ _ => 0, ?_⟩⟩
    · intro pick
      simp [M, costFrom]
    · simp [M, costFrom]
  | succ h ih =>
    intro S
    constructor
    · intro pick
      rw [costFrom_succ]
      have h1 : M a b (h + 1) S ≤ incX a b S (pick 0) + M a b h (nextX a b S (pick 0)) :=
        minVal_le _ _ _ (Finset.mem_univ (pick 0))
      have h2 := (ih (nextX a b S (pick 0))).1 (fun i => pick i.succ)
      exact le_trans h1 (Nat.add_le_add_left h2 _)
    · rcases exists_eq_minVal (Finset.univ : Finset (Fin t → Fin 3))
        ⟨fun _ => 0, Finset.mem_univ _⟩
        (fun c0 => incX a b S c0 + M a b h (nextX a b S c0)) with ⟨c0, _, hc0⟩
      rcases (ih (nextX a b S c0)).2 with ⟨rest, hrest⟩
      refine ⟨Fin.cases c0 rest, ?_⟩
      rw [costFrom_succ]
      simp only [Fin.cases_zero, Fin.cases_succ]
      change incX a b S c0 + costFrom a b (nextX a b S c0).val h rest = M a b (h + 1) S
      rw [hrest]
      exact hc0

private lemma M_bounds {t : ℕ} (a b : Fin t → Fin 32) (h : ℕ) (S : XSub) :
    M a b h S0 ≤ M a b h S ∧ M a b h S ≤ M a b h S0 + 4 := by
  have hS0 : S0.val = {0} := rfl
  constructor
  · rcases (M_spec a b h S).2 with ⟨p, hp⟩
    have h1 := (M_spec a b h S0).1 p
    rw [hS0] at h1
    have h2 := (costFrom_discrepancy a b S.val (xsub_isXorSub S) (xsub_subset_16 S) h p).1
    omega
  · rcases (M_spec a b h S0).2 with ⟨p, hp⟩
    rw [hS0] at hp
    have h1 := (M_spec a b h S).1 p
    have h2 := (costFrom_discrepancy a b S.val (xsub_isXorSub S) (xsub_subset_16 S) h p).2
    omega

private lemma M_mono_succ {t : ℕ} (a b : Fin t → Fin 32) (h : ℕ) :
    M a b h S0 ≤ M a b (h + 1) S0 := by
  have hS0 : S0.val = {0} := rfl
  rcases (M_spec a b (h + 1) S0).2 with ⟨p, hp⟩
  rw [costFrom_succ] at hp
  have h1 := (M_spec a b h S0).1 (fun i => p i.succ)
  rw [hS0] at h1
  have h2 := (costFrom_discrepancy a b (nextX a b S0 (p 0)).val
    (xsub_isXorSub (nextX a b S0 (p 0))) (xsub_subset_16 (nextX a b S0 (p 0)))
    h (fun i => p i.succ)).1
  change incX a b S0 (p 0) + costFrom a b (nextX a b S0 (p 0)).val h (fun i => p i.succ) =
    M a b (h + 1) S0 at hp
  omega

private lemma M_mono {t : ℕ} (a b : Fin t → Fin 32) {h1 h2 : ℕ} (hle : h1 ≤ h2) :
    M a b h1 S0 ≤ M a b h2 S0 := by
  induction hle with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (M_mono_succ a b _)

private lemma main_result (t : ℕ) (a b : Fin t → Fin 32) :
    let minimum := fun (h d : ℕ) =>
      (∃ p : Fin h → Fin t → Fin 3, costFrom a b {0} h p = d) ∧
      ∀ p : Fin h → Fin t → Fin 3, d ≤ costFrom a b {0} h p
    ∃ H q r : ℕ, 0 < q ∧
      (∀ h d : ℕ, H ≤ h → minimum h d → minimum (h + q) (d + r)) ∧
      ((∃ B : ℕ, ∀ h d : ℕ, minimum h d → 2 * h ≤ 3 * d + B ∧ 3 * d ≤ 2 * h + B) →
        3 * r = 2 * q) := by
  intro minimum
  have hmin_iff : ∀ h d, minimum h d ↔ d = M a b h S0 := by
    intro h d
    constructor
    · rintro ⟨⟨p, hp⟩, hle⟩
      apply le_antisymm
      · rcases (M_spec a b h S0).2 with ⟨p0, hp0⟩
        rw [← hp0]
        exact hle p0
      · rw [← hp]
        exact (M_spec a b h S0).1 p
    · rintro rfl
      exact ⟨(M_spec a b h S0).2, (M_spec a b h S0).1⟩
  let prof : ℕ → (XSub → Fin 5) := fun h S =>
    ⟨M a b h S - M a b h S0, by
      have hb := M_bounds a b h S
      omega⟩
  haveI : Finite XSub := xsub_finite
  rcases Finite.exists_ne_map_eq_of_infinite prof with ⟨h1, h2, hne, hprof_eq⟩
  have hex : ∃ H q : ℕ, 0 < q ∧ prof (H + q) = prof H := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · refine ⟨h1, h2 - h1, by omega, ?_⟩
      have heq : h1 + (h2 - h1) = h2 := by omega
      rw [heq]
      exact hprof_eq.symm
    · refine ⟨h2, h1 - h2, by omega, ?_⟩
      have heq : h2 + (h1 - h2) = h1 := by omega
      rw [heq]
      exact hprof_eq
  rcases hex with ⟨H, q, hq_pos, hprof⟩
  let r := M a b (H + q) S0 - M a b H S0
  have hr_eq : M a b (H + q) S0 = M a b H S0 + r := by
    have hm := M_mono a b (by omega : H ≤ H + q)
    omega
  have hper : ∀ k (S : XSub), M a b (H + k + q) S = M a b (H + k) S + r := by
    intro k
    induction k with
    | zero =>
      intro S
      simp only [Nat.add_zero]
      have hS_eq : (prof (H + q) S).val = (prof H S).val :=
        congrArg Fin.val (congrFun hprof S)
      have hb1 := M_bounds a b H S
      have hb2 := M_bounds a b (H + q) S
      dsimp only [prof] at hS_eq
      omega
    | succ k ih =>
      intro S
      have hidx : H + (k + 1) + q = (H + k + q) + 1 := by omega
      have hidx2 : H + (k + 1) = (H + k) + 1 := by omega
      rw [hidx, hidx2]
      unfold M
      have hfun : (fun c0 : Fin t → Fin 3 => incX a b S c0 + M a b (H + k + q) (nextX a b S c0)) =
          (fun c0 : Fin t → Fin 3 => (incX a b S c0 + M a b (H + k) (nextX a b S c0)) + r) := by
        funext c0
        rw [ih (nextX a b S c0), Nat.add_assoc]
      rw [hfun]
      exact minVal_add_right _ _ (fun c0 => incX a b S c0 + M a b (H + k) (nextX a b S c0)) r
  refine ⟨H, q, r, hq_pos, ?_, ?_⟩
  · intro h d hHh hmd
    rw [hmin_iff] at hmd ⊢
    subst hmd
    have hk : H + (h - H) = h := by omega
    have hstep := hper (h - H) S0
    rw [hk] at hstep
    exact hstep.symm
  · rintro ⟨B, hB⟩
    have hiter : ∀ m : ℕ, M a b (H + m * q) S0 = M a b H S0 + m * r := by
      intro m
      induction m with
      | zero => simp
      | succ m ihm =>
        have hstep := hper (m * q) S0
        have heq1 : H + (m + 1) * q = H + m * q + q := by ring
        rw [heq1, hstep, ihm]
        ring
    have hbound : ∀ m : ℕ,
        2 * (H + m * q) ≤ 3 * (M a b H S0 + m * r) + B ∧
        3 * (M a b H S0 + m * r) ≤ 2 * (H + m * q) + B := by
      intro m
      exact hB (H + m * q) (M a b H S0 + m * r) ((hmin_iff _ _).mpr (hiter m).symm)
    by_contra hne_slope
    rcases lt_or_gt_of_ne hne_slope with hlt | hgt
    · let m := 3 * M a b H S0 + B + 1
      have hb := (hbound m).1
      have hstep : 3 * r + 1 ≤ 2 * q := by omega
      have hmul : m * (3 * r + 1) ≤ m * (2 * q) := Nat.mul_le_mul_left m hstep
      have h1 : 2 * (H + m * q) = 2 * H + m * (2 * q) := by ring
      have h2 : 3 * (M a b H S0 + m * r) + B = 3 * M a b H S0 + B + m * (3 * r) := by ring
      have h3 : m * (3 * r + 1) = m * (3 * r) + m := by ring
      omega
    · let m := 2 * H + B + 1
      have hb := (hbound m).2
      have hstep : 2 * q + 1 ≤ 3 * r := by omega
      have hmul : m * (2 * q + 1) ≤ m * (3 * r) := Nat.mul_le_mul_left m hstep
      have h1 : 3 * (M a b H S0 + m * r) = 3 * M a b H S0 + m * (3 * r) := by ring
      have h2 : 2 * (H + m * q) + B = 2 * H + B + m * (2 * q) := by ring
      have h3 : m * (2 * q + 1) = m * (2 * q) + m := by ring
      omega

end PEqualNP.Outside.L_lib_779_aux

theorem PEqualNP.Outside.L_lib_779 : (∀ (t : ℕ) (a b : Fin t → Fin 32),
  let advance := fun (st : ℕ × Finset ℕ) (atSite : Fin t → ℕ) =>
    let extended := (List.finRange t).foldl (fun (s : Finset ℕ) j =>
      s ∪ s.image (fun v => v ^^^ atSite j)) st.2
    let even := extended.filter (fun v => v % 2 = 0)
    (st.1 + (if even = extended then 0 else 1), even.image (fun v => v / 2))
  let selectMask := fun (u v : Fin 32) (c : Fin 3) =>
    if c.val = 0 then u.val else if c.val = 1 then v.val else u.val ^^^ v.val
  let cost := fun (h : ℕ) (pick : Fin h → Fin t → Fin 3) =>
    let last := (List.finRange h).foldl (fun st i =>
      advance st (fun j => selectMask (a j) (b j) (pick i j))) ((0, {0}) : ℕ × Finset ℕ)
    last.1 + Nat.log2 last.2.card
  let minimum := fun (h d : ℕ) =>
    (∃ p : Fin h → Fin t → Fin 3, cost h p = d) ∧
    ∀ p : Fin h → Fin t → Fin 3, d ≤ cost h p
  ∃ H q r : ℕ, 0 < q ∧
    (∀ h d : ℕ, H ≤ h → minimum h d → minimum (h+q) (d+r)) ∧
    ((∃ B : ℕ, ∀ h d : ℕ, minimum h d → 2*h ≤ 3*d+B ∧ 3*d ≤ 2*h+B) →
      3*r = 2*q)) := by
  intro t a b
  exact PEqualNP.Outside.L_lib_779_aux.main_result t a b
