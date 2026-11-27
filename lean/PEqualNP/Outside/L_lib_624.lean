import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.Rank

namespace PEqualNP.Outside.L_lib_624

private def totW {α : Type*} (w : α → ℕ) (U : Finset α) : ℚ :=
  ∑ x ∈ U, (w x : ℚ)

private lemma totW_pos {α : Type*} (w : α → ℕ) {U : Finset α}
    (hU : U.Nonempty) (hw : ∀ x ∈ U, 0 < w x) : 0 < totW w U :=
  Finset.sum_pos (fun x hx => Nat.cast_pos.mpr (hw x hx)) hU

private lemma totW_ne_zero {α : Type*} (w : α → ℕ) {U : Finset α}
    (hU : U.Nonempty) (hw : ∀ x ∈ U, 0 < w x) : totW w U ≠ 0 :=
  ne_of_gt (totW_pos w hU hw)

private def IsOrder {α : Type*} (U : Finset α) (L : List α) : Prop :=
  L.Nodup ∧ ∀ x, x ∈ L ↔ x ∈ U

private lemma isOrder_nil {α : Type*} : IsOrder (∅ : Finset α) [] :=
  ⟨List.nodup_nil, fun x => by simp⟩

private lemma eq_nil_of_isOrder_empty {α : Type*} {L : List α} (h : IsOrder (∅ : Finset α) L) :
    L = [] := by
  cases L with
  | nil => rfl
  | cons a t =>
    exact absurd ((h.2 a).mp List.mem_cons_self) (Finset.notMem_empty a)

private lemma isOrder_cons {α : Type*} [DecidableEq α] {U : Finset α} {x : α} {L : List α}
    (hx : x ∈ U) (hL : IsOrder (U.erase x) L) : IsOrder U (x :: L) := by
  refine ⟨List.nodup_cons.mpr ⟨?_, hL.1⟩, fun y => ?_⟩
  · intro hxL
    exact (Finset.notMem_erase x U) ((hL.2 x).mp hxL)
  · simp only [List.mem_cons, hL.2 y, Finset.mem_erase]
    constructor
    · rintro (rfl | ⟨_, hyU⟩)
      · exact hx
      · exact hyU
    · intro hyU
      by_cases h : y = x
      · exact Or.inl h
      · exact Or.inr ⟨h, hyU⟩

private lemma isOrder_of_cons {α : Type*} [DecidableEq α] {U : Finset α} {x : α} {L : List α}
    (h : IsOrder U (x :: L)) : x ∈ U ∧ IsOrder (U.erase x) L := by
  have hxU : x ∈ U := (h.2 x).mp List.mem_cons_self
  rcases List.nodup_cons.mp h.1 with ⟨hxL, hnodup⟩
  refine ⟨hxU, hnodup, fun y => ?_⟩
  rw [Finset.mem_erase]
  constructor
  · intro hyL
    refine ⟨fun hyx => hxL (hyx ▸ hyL), (h.2 y).mp (List.mem_cons_of_mem x hyL)⟩
  · rintro ⟨hyx, hyU⟩
    rcases List.mem_cons.mp ((h.2 y).mpr hyU) with rfl | hyL
    · exact absurd rfl hyx
    · exact hyL

private lemma isOrder_toList {α : Type*} (S : Finset α) : IsOrder S S.toList :=
  ⟨Finset.nodup_toList S, fun _ => Finset.mem_toList⟩

private def plExpect {α : Type*} [DecidableEq α] (w : α → ℕ) (U : Finset α)
    (f : List α → ℚ) : ℚ :=
  if U = ∅ then f []
  else
    ∑ x ∈ U.attach, ((w x.1 : ℚ) / totW w U) *
      plExpect w (U.erase x.1) (fun L => f (x.1 :: L))
termination_by U.card
decreasing_by
  exact Finset.card_erase_lt_of_mem x.2

private lemma plExpect_empty {α : Type*} [DecidableEq α] (w : α → ℕ) (f : List α → ℚ) :
    plExpect w ∅ f = f [] := by
  rw [plExpect]
  simp only [↓reduceIte]

private lemma plExpect_nonempty {α : Type*} [DecidableEq α] (w : α → ℕ) {U : Finset α}
    (hU : U.Nonempty) (f : List α → ℚ) :
    plExpect w U f =
      ∑ x ∈ U, ((w x : ℚ) / totW w U) * plExpect w (U.erase x) (fun L => f (x :: L)) := by
  have hne : U ≠ ∅ := hU.ne_empty
  rw [plExpect]
  simp only [hne, ↓reduceIte]
  exact Finset.sum_attach U (fun x =>
    ((w x : ℚ) / totW w U) * plExpect w (U.erase x) (fun L => f (x :: L)))

private lemma sum_div_const {α : Type*} (s : Finset α) (f : α → ℚ) (d : ℚ) :
    (∑ x ∈ s, f x / d) = (∑ x ∈ s, f x) / d := by
  simp only [div_eq_mul_inv, ← Finset.sum_mul]

private lemma plExpect_const_aux {α : Type*} [DecidableEq α] (w : α → ℕ) (c : ℚ) :
    ∀ (k : ℕ) (U : Finset α), U.card = k → (∀ x ∈ U, 0 < w x) →
      plExpect w U (fun _ => c) = c
  | 0, U, hk, _ => by
      rw [Finset.card_eq_zero.mp hk, plExpect_empty]
  | k + 1, U, hk, hw => by
      have hU : U.Nonempty := Finset.card_pos.mp (hk ▸ Nat.succ_pos k)
      rw [plExpect_nonempty w hU]
      have hterm : ∀ x ∈ U,
          ((w x : ℚ) / totW w U) * plExpect w (U.erase x) (fun _ => c) =
            ((w x : ℚ) / totW w U) * c := by
        intro x hx
        have hcard : (U.erase x).card = k := by
          rw [Finset.card_erase_of_mem hx, hk]
          rfl
        rw [plExpect_const_aux w c k (U.erase x) hcard
          (fun y hy => hw y (Finset.mem_of_mem_erase hy))]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, sum_div_const]
      change (totW w U / totW w U) * c = c
      rw [div_self (totW_ne_zero w hU hw), one_mul]

private lemma plExpect_const {α : Type*} [DecidableEq α] (w : α → ℕ) (U : Finset α) (c : ℚ)
    (hw : ∀ x ∈ U, 0 < w x) : plExpect w U (fun _ => c) = c :=
  plExpect_const_aux w c U.card U rfl hw

private lemma plExpect_sum_aux {α β : Type*} [DecidableEq α] (w : α → ℕ) (T : Finset β) :
    ∀ (k : ℕ) (U : Finset α) (f : β → List α → ℚ), U.card = k →
      plExpect w U (fun L => ∑ i ∈ T, f i L) = ∑ i ∈ T, plExpect w U (f i)
  | 0, U, f, hk => by
      rw [Finset.card_eq_zero.mp hk]
      simp only [plExpect_empty]
  | k + 1, U, f, hk => by
      have hU : U.Nonempty := Finset.card_pos.mp (hk ▸ Nat.succ_pos k)
      rw [plExpect_nonempty w hU]
      have hterm : ∀ x ∈ U,
          ((w x : ℚ) / totW w U) *
              plExpect w (U.erase x) (fun L => ∑ i ∈ T, f i (x :: L)) =
            ∑ i ∈ T, ((w x : ℚ) / totW w U) * plExpect w (U.erase x) (fun L => f i (x :: L)) := by
        intro x hx
        have hcard : (U.erase x).card = k := by
          rw [Finset.card_erase_of_mem hx, hk]
          rfl
        rw [plExpect_sum_aux w T k (U.erase x) (fun i L => f i (x :: L)) hcard, Finset.mul_sum]
      rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [plExpect_nonempty w hU]

private lemma plExpect_sum {α β : Type*} [DecidableEq α] (w : α → ℕ) (U : Finset α)
    (T : Finset β) (f : β → List α → ℚ) :
    plExpect w U (fun L => ∑ i ∈ T, f i L) = ∑ i ∈ T, plExpect w U (f i) :=
  plExpect_sum_aux w T U.card U f rfl

private lemma plExpect_le_and_eq_aux {α : Type*} [DecidableEq α] (w : α → ℕ) :
    ∀ (k : ℕ) (U : Finset α) (f g : List α → ℚ), U.card = k →
      (∀ x ∈ U, 0 < w x) → (∀ L, IsOrder U L → f L ≤ g L) →
      plExpect w U f ≤ plExpect w U g ∧
        (plExpect w U f = plExpect w U g → ∀ L, IsOrder U L → f L = g L)
  | 0, U, f, g, hk, _, hle => by
      have hU : U = ∅ := Finset.card_eq_zero.mp hk
      subst hU
      rw [plExpect_empty, plExpect_empty]
      refine ⟨hle [] isOrder_nil, fun heq L hL => ?_⟩
      rw [eq_nil_of_isOrder_empty hL]
      exact heq
  | k + 1, U, f, g, hk, hw, hle => by
      have hU : U.Nonempty := Finset.card_pos.mp (hk ▸ Nat.succ_pos k)
      have htot : 0 < totW w U := totW_pos w hU hw
      have hih : ∀ x ∈ U,
          plExpect w (U.erase x) (fun L => f (x :: L)) ≤
            plExpect w (U.erase x) (fun L => g (x :: L)) ∧
          (plExpect w (U.erase x) (fun L => f (x :: L)) =
            plExpect w (U.erase x) (fun L => g (x :: L)) →
            ∀ L, IsOrder (U.erase x) L → f (x :: L) = g (x :: L)) := by
        intro x hx
        have hcard : (U.erase x).card = k := by
          rw [Finset.card_erase_of_mem hx, hk]
          rfl
        exact plExpect_le_and_eq_aux w k (U.erase x) (fun L => f (x :: L)) (fun L => g (x :: L))
          hcard (fun y hy => hw y (Finset.mem_of_mem_erase hy))
          (fun L hL => hle (x :: L) (isOrder_cons hx hL))
      have hterm_le : ∀ x ∈ U,
          ((w x : ℚ) / totW w U) * plExpect w (U.erase x) (fun L => f (x :: L)) ≤
            ((w x : ℚ) / totW w U) * plExpect w (U.erase x) (fun L => g (x :: L)) := by
        intro x hx
        have hpos : 0 ≤ (w x : ℚ) / totW w U :=
          le_of_lt (div_pos (Nat.cast_pos.mpr (hw x hx)) htot)
        exact mul_le_mul_of_nonneg_left (hih x hx).1 hpos
      rw [plExpect_nonempty w hU f, plExpect_nonempty w hU g]
      refine ⟨Finset.sum_le_sum hterm_le, fun heq L hL => ?_⟩
      cases L with
      | nil =>
        rcases hU with ⟨a, ha⟩
        exact absurd ((hL.2 a).mpr ha) List.not_mem_nil
      | cons x xs =>
        rcases isOrder_of_cons hL with ⟨hxU, hxs⟩
        have hall := (Finset.sum_eq_sum_iff_of_le hterm_le).mp heq
        have hxeq := hall x hxU
        have hpos : (w x : ℚ) / totW w U ≠ 0 :=
          ne_of_gt (div_pos (Nat.cast_pos.mpr (hw x hxU)) htot)
        exact (hih x hxU).2 (mul_left_cancel₀ hpos hxeq) xs hxs

private lemma plExpect_le_and_eq {α : Type*} [DecidableEq α] (w : α → ℕ) (U : Finset α)
    (f g : List α → ℚ) (hw : ∀ x ∈ U, 0 < w x) (hle : ∀ L, IsOrder U L → f L ≤ g L) :
    plExpect w U f ≤ plExpect w U g ∧
      (plExpect w U f = plExpect w U g → ∀ L, IsOrder U L → f L = g L) :=
  plExpect_le_and_eq_aux w U.card U f g rfl hw hle

private def isFirstIn {α : Type*} [DecidableEq α] (S : Finset α) (i : α) : List α → Bool
  | [] => false
  | x :: xs => if x = i then true else if x ∈ S then false else isFirstIn S i xs

private lemma plExpect_firstIn_aux {α : Type*} [DecidableEq α] (w : α → ℕ) (S : Finset α) (i : α) :
    ∀ (k : ℕ) (U : Finset α), U.card = k → (∀ x ∈ U, 0 < w x) → S ⊆ U → i ∈ S →
      plExpect w U (fun L => if isFirstIn S i L then (1 : ℚ) else 0) =
        (w i : ℚ) / totW w S
  | 0, U, hk, _, hSU, hiS => by
      have hU : U = ∅ := Finset.card_eq_zero.mp hk
      subst hU
      exact absurd (hSU hiS) (Finset.notMem_empty i)
  | k + 1, U, hk, hw, hSU, hiS => by
      have hU : U.Nonempty := Finset.card_pos.mp (hk ▸ Nat.succ_pos k)
      have hS : S.Nonempty := ⟨i, hiS⟩
      have htotU : totW w U ≠ 0 := totW_ne_zero w hU hw
      have htotS : totW w S ≠ 0 := totW_ne_zero w hS (fun x hx => hw x (hSU hx))
      rw [plExpect_nonempty w hU, ← Finset.sum_sdiff hSU]
      have hsumS :
          ∑ x ∈ S, ((w x : ℚ) / totW w U) *
              plExpect w (U.erase x) (fun L => if isFirstIn S i (x :: L) then (1 : ℚ) else 0) =
            (w i : ℚ) / totW w U := by
        rw [Finset.sum_eq_single i]
        · have hfun : (fun L => if isFirstIn S i (i :: L) then (1 : ℚ) else 0) = fun _ => 1 := by
            funext L
            simp only [isFirstIn, ↓reduceIte]
          rw [hfun, plExpect_const w (U.erase i) 1
            (fun y hy => hw y (Finset.mem_of_mem_erase hy)), mul_one]
        · intro x hxS hxi
          have hfun : (fun L => if isFirstIn S i (x :: L) then (1 : ℚ) else 0) = fun _ => 0 := by
            funext L
            simp only [isFirstIn, hxi, hxS, ↓reduceIte, Bool.false_eq_true]
          rw [hfun, plExpect_const w (U.erase x) 0
            (fun y hy => hw y (Finset.mem_of_mem_erase hy)), mul_zero]
        · intro hi
          exact absurd hiS hi
      have hsumDiff :
          ∑ x ∈ U \ S, ((w x : ℚ) / totW w U) *
              plExpect w (U.erase x) (fun L => if isFirstIn S i (x :: L) then (1 : ℚ) else 0) =
            (totW w (U \ S) / totW w U) * ((w i : ℚ) / totW w S) := by
        have hterm : ∀ x ∈ U \ S,
            ((w x : ℚ) / totW w U) *
                plExpect w (U.erase x) (fun L => if isFirstIn S i (x :: L) then (1 : ℚ) else 0) =
              ((w x : ℚ) / totW w U) * ((w i : ℚ) / totW w S) := by
          intro x hx
          rcases Finset.mem_sdiff.mp hx with ⟨hxU, hxS⟩
          have hxi : x ≠ i := fun h => hxS (h ▸ hiS)
          have hfun : (fun L => if isFirstIn S i (x :: L) then (1 : ℚ) else 0) =
              (fun L => if isFirstIn S i L then (1 : ℚ) else 0) := by
            funext L
            simp only [isFirstIn, hxi, hxS, ↓reduceIte]
          have hcard : (U.erase x).card = k := by
            rw [Finset.card_erase_of_mem hxU, hk]
            rfl
          rw [hfun, plExpect_firstIn_aux w S i k (U.erase x) hcard
            (fun y hy => hw y (Finset.mem_of_mem_erase hy))
            (Finset.subset_erase.mpr ⟨hSU, hxS⟩) hiS]
        rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, sum_div_const]
        rfl
      rw [hsumS, hsumDiff]
      have hsplit : totW w (U \ S) + totW w S = totW w U := Finset.sum_sdiff hSU
      calc
        (totW w (U \ S) / totW w U) * ((w i : ℚ) / totW w S) + (w i : ℚ) / totW w U
            = (totW w (U \ S) * (w i : ℚ)) / (totW w U * totW w S) +
                ((w i : ℚ) * totW w S) / (totW w U * totW w S) := by
              rw [div_mul_div_comm, mul_div_mul_right _ _ htotS]
        _ = (totW w (U \ S) * (w i : ℚ) + totW w S * (w i : ℚ)) / (totW w U * totW w S) := by
              rw [← add_div, mul_comm (w i : ℚ) (totW w S)]
        _ = ((totW w (U \ S) + totW w S) * (w i : ℚ)) / (totW w U * totW w S) := by
              rw [← add_mul]
        _ = (totW w U * (w i : ℚ)) / (totW w U * totW w S) := by
              rw [hsplit]
        _ = (w i : ℚ) / totW w S := mul_div_mul_left (w i : ℚ) (totW w S) htotU

private lemma plExpect_firstIn {α : Type*} [DecidableEq α] (w : α → ℕ) (U S : Finset α) (i : α)
    (hw : ∀ x ∈ U, 0 < w x) (hSU : S ⊆ U) (hiS : i ∈ S) :
    plExpect w U (fun L => if isFirstIn S i L then (1 : ℚ) else 0) =
      (w i : ℚ) / totW w S :=
  plExpect_firstIn_aux w S i U.card U rfl hw hSU hiS

private def rowSet {n : ℕ} (G : Fin n → Fin n → Bool) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun b => G i b = true)

private lemma mem_rowSet {n : ℕ} (G : Fin n → Fin n → Bool) (i b : Fin n) :
    b ∈ rowSet G i ↔ G i b = true := by
  simp only [rowSet, Finset.mem_filter, Finset.mem_univ, true_and]

private def goodSet {n : ℕ} (G : Fin n → Fin n → Bool) (L : List (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => isFirstIn (rowSet G i) i L = true)

private lemma triangular_mulVec_zero {n : ℕ} (G : Fin n → Fin n → Bool)
    (hdiag : ∀ i, G i i = true) :
    ∀ (L : List (Fin n)) (I : Finset (Fin n)) (x : Fin n → ZMod 2),
      (∀ i ∈ I, isFirstIn (rowSet G i) i L = true) →
      (∀ j, j ∉ I → x j = 0) →
      (∀ i ∈ I, ∑ j : Fin n, (if G i j then (1 : ZMod 2) else 0) * x j = 0) →
      ∀ j : Fin n, x j = 0
  | [], I, x, hgood, hsupp, _ => fun j => by
      have hj : j ∉ I := fun hjI => by
        have h := hgood j hjI
        simp only [isFirstIn, Bool.false_eq_true] at h
      exact hsupp j hj
  | a :: L', I, x, hgood, hsupp, hzero => by
      let I' : Finset (Fin n) := I.erase a
      let x' : Fin n → ZMod 2 := fun j => if j = a then 0 else x j
      have hstep : ∀ i ∈ I',
          G i a = false ∧ isFirstIn (rowSet G i) i L' = true := by
        intro i hi
        rcases Finset.mem_erase.mp hi with ⟨hia, hiI⟩
        have h := hgood i hiI
        have hai : a ≠ i := Ne.symm hia
        simp only [isFirstIn, hai, ↓reduceIte] at h
        by_cases ha : a ∈ rowSet G i
        · simp only [ha, ↓reduceIte, Bool.false_eq_true] at h
        · simp only [ha, ↓reduceIte] at h
          have hfalse : G i a = false := by
            cases hG : G i a
            · rfl
            · exact absurd ((mem_rowSet G i a).mpr hG) ha
          exact ⟨hfalse, h⟩
      have hx'zero : ∀ j : Fin n, x' j = 0 := by
        refine triangular_mulVec_zero G hdiag L' I' x'
          (fun i hi => (hstep i hi).2) ?_ ?_
        · intro j hj
          by_cases hja : j = a
          · simp only [x', hja, ↓reduceIte]
          · have hjI : j ∉ I := fun hjI => hj (Finset.mem_erase.mpr ⟨hja, hjI⟩)
            simp only [x', hja, ↓reduceIte, hsupp j hjI]
        · intro i hi
          have hiI : i ∈ I := Finset.mem_of_mem_erase hi
          have hGia : G i a = false := (hstep i hi).1
          refine (Finset.sum_congr rfl fun j _ => ?_).trans (hzero i hiI)
          by_cases hja : j = a
          · subst hja
            simp only [x', hGia, Bool.false_eq_true, ↓reduceIte, zero_mul]
          · simp only [x', hja, ↓reduceIte]
      have hne : ∀ j : Fin n, j ≠ a → x j = 0 := by
        intro j hja
        have h := hx'zero j
        simp only [x', hja, ↓reduceIte] at h
        exact h
      have hxa : x a = 0 := by
        by_cases haI : a ∈ I
        · have h0 := hzero a haI
          rw [Finset.sum_eq_single a] at h0
          · simp only [hdiag a, ↓reduceIte, one_mul] at h0
            exact h0
          · intro j _ hja
            rw [hne j hja, mul_zero]
          · intro ha
            exact absurd (Finset.mem_univ a) ha
        · exact hsupp a haI
      intro j
      by_cases hja : j = a
      · exact hja ▸ hxa
      · exact hne j hja

private lemma goodSet_card_le_rank {n : ℕ} (G : Fin n → Fin n → Bool)
    (hdiag : ∀ i, G i i = true) (L : List (Fin n)) :
    let M : Matrix (Fin n) (Fin n) (ZMod 2) := fun a b => if G a b then 1 else 0
    (goodSet G L).card ≤ M.rank := by
  intro M
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let I : Finset (Fin n) := goodSet G L
  let A : Matrix I I (ZMod 2) := M.submatrix Subtype.val Subtype.val
  have hinj : Function.Injective A.mulVecLin := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    let x : Fin n → ZMod 2 := fun j => if hj : j ∈ I then y ⟨j, hj⟩ else 0
    have hxzero : ∀ j : Fin n, x j = 0 := by
      refine triangular_mulVec_zero G hdiag L I x
        (fun i hi => (Finset.mem_filter.mp hi).2)
        (fun j hj => by simp only [x, hj, ↓reduceDIte]) ?_
      intro i hi
      have hyi : (A.mulVecLin y) ⟨i, hi⟩ = 0 := congrFun hy ⟨i, hi⟩
      refine Eq.trans ?_ hyi
      change (∑ j : Fin n, M i j * x j) = ∑ j : I, M i j.1 * y j
      have hsub : (∑ j : Fin n, M i j * x j) = ∑ j ∈ I, M i j * x j := by
        symm
        refine Finset.sum_subset (Finset.subset_univ I) fun j _ hjI => ?_
        simp only [x, hjI, ↓reduceDIte, mul_zero]
      rw [hsub, ← Finset.sum_attach I (fun j => M i j * x j)]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [x, j.2, ↓reduceDIte]
    funext j
    have h := hxzero j.1
    simp only [x, j.2, ↓reduceDIte] at h
    exact h
  calc
    I.card = Fintype.card I := (Fintype.card_coe I).symm
    _ = Module.finrank (ZMod 2) (I → ZMod 2) := (Module.finrank_fintype_fun_eq_card (ZMod 2)).symm
    _ = A.rank := (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ M.rank := Matrix.rank_submatrix_le M Subtype.val Subtype.val

private lemma pair_eq_of_goodSet_eq {n : ℕ} (G : Fin n → Fin n → Bool)
    {L₁ L₂ : List (Fin n)} {i j : Fin n} (hij : i ≠ j)
    (hcard : (goodSet G L₁).card = (goodSet G L₂).card)
    (hother : ∀ k, k ≠ i → k ≠ j →
      isFirstIn (rowSet G k) k L₁ = isFirstIn (rowSet G k) k L₂) :
    (if isFirstIn (rowSet G i) i L₁ then (1 : ℕ) else 0) +
      (if isFirstIn (rowSet G j) j L₁ then (1 : ℕ) else 0) =
    (if isFirstIn (rowSet G i) i L₂ then (1 : ℕ) else 0) +
      (if isFirstIn (rowSet G j) j L₂ then (1 : ℕ) else 0) := by
  have h1 : (goodSet G L₁).card =
      ∑ k : Fin n, if isFirstIn (rowSet G k) k L₁ = true then (1 : ℕ) else 0 :=
    Finset.card_filter _ _
  have h2 : (goodSet G L₂).card =
      ∑ k : Fin n, if isFirstIn (rowSet G k) k L₂ = true then (1 : ℕ) else 0 :=
    Finset.card_filter _ _
  rw [h1, h2] at hcard
  have hji : j ∈ (Finset.univ : Finset (Fin n)).erase i :=
    Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ hji, ← Nat.add_assoc] at hcard
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ hji, ← Nat.add_assoc] at hcard
  have hrest :
      (∑ k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase j,
          if isFirstIn (rowSet G k) k L₁ = true then (1 : ℕ) else 0) =
      (∑ k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase j,
          if isFirstIn (rowSet G k) k L₂ = true then (1 : ℕ) else 0) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rcases Finset.mem_erase.mp hk with ⟨hkj, hki'⟩
    rcases Finset.mem_erase.mp hki' with ⟨hki, _⟩
    rw [hother k hki hkj]
  rw [hrest] at hcard
  exact Nat.add_right_cancel hcard

private lemma isFirstIn_swap2 {α : Type*} [DecidableEq α] (S : Finset α) {a b k : α}
    (R : List α) (hka : k ≠ a) (hkb : k ≠ b) :
    isFirstIn S k (a :: b :: R) = isFirstIn S k (b :: a :: R) := by
  have hak : a ≠ k := Ne.symm hka
  have hbk : b ≠ k := Ne.symm hkb
  simp only [isFirstIn, hak, hbk, ↓reduceIte]
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp only [ha, hb, ↓reduceIte]

private lemma symm_of_const_good {n : ℕ} (G : Fin n → Fin n → Bool)
    (hconst : ∀ L₁ L₂, IsOrder Finset.univ L₁ → IsOrder Finset.univ L₂ →
      (goodSet G L₁).card = (goodSet G L₂).card)
    {i j : Fin n} (hij : G i j = true) : G j i = true := by
  by_cases heq : i = j
  · subst heq
    exact hij
  · let R := ((Finset.univ : Finset (Fin n)).erase i |>.erase j).toList
    have hR1 : IsOrder ((Finset.univ.erase i).erase j) R := isOrder_toList _
    have hR2 : IsOrder ((Finset.univ.erase j).erase i) R := by
      rw [Finset.erase_right_comm]
      exact hR1
    have hL1 : IsOrder Finset.univ (i :: j :: R) :=
      isOrder_cons (Finset.mem_univ i)
        (isOrder_cons (Finset.mem_erase.mpr ⟨Ne.symm heq, Finset.mem_univ j⟩) hR1)
    have hL2 : IsOrder Finset.univ (j :: i :: R) :=
      isOrder_cons (Finset.mem_univ j)
        (isOrder_cons (Finset.mem_erase.mpr ⟨heq, Finset.mem_univ i⟩) hR2)
    have hpair := pair_eq_of_goodSet_eq G heq (hconst _ _ hL1 hL2)
      (fun k hki hkj => isFirstIn_swap2 (rowSet G k) R hki hkj)
    have h1i : isFirstIn (rowSet G i) i (i :: j :: R) = true := by
      simp only [isFirstIn, ↓reduceIte]
    have h2i : isFirstIn (rowSet G i) i (j :: i :: R) = false := by
      have hji : j ≠ i := Ne.symm heq
      have hmem : j ∈ rowSet G i := (mem_rowSet G i j).mpr hij
      simp only [isFirstIn, hji, hmem, ↓reduceIte]
    have h2j : isFirstIn (rowSet G j) j (j :: i :: R) = true := by
      simp only [isFirstIn, ↓reduceIte]
    have h1j : isFirstIn (rowSet G j) j (i :: j :: R) = !G j i := by
      simp only [isFirstIn, heq, ↓reduceIte, mem_rowSet]
      cases G j i <;> rfl
    rw [h1i, h2i, h2j, h1j] at hpair
    cases hGji : G j i
    · simp only [hGji, Bool.not_false, ↓reduceIte, Bool.false_eq_true] at hpair
      exact absurd hpair (by decide)
    · rfl

private lemma row_eq_of_const_good {n : ℕ} (G : Fin n → Fin n → Bool)
    (hdiag : ∀ i, G i i = true)
    (hconst : ∀ L₁ L₂, IsOrder Finset.univ L₁ → IsOrder Finset.univ L₂ →
      (goodSet G L₁).card = (goodSet G L₂).card)
    {i j : Fin n} (hij : G i j = true) (z : Fin n) : G i z = G j z := by
  have hji : G j i = true := symm_of_const_good G hconst hij
  by_cases hije : i = j
  · subst hije
    rfl
  · by_cases hzi : z = i
    · subst hzi
      rw [hdiag z, hji]
    · by_cases hzj : z = j
      · subst hzj
        rw [hij, hdiag z]
      · let R := (((Finset.univ : Finset (Fin n)).erase z |>.erase i).erase j).toList
        have hR1 : IsOrder (((Finset.univ.erase z).erase i).erase j) R := isOrder_toList _
        have hR2 : IsOrder (((Finset.univ.erase z).erase j).erase i) R := by
          rw [Finset.erase_right_comm]
          exact hR1
        have hi_z : i ∈ (Finset.univ : Finset (Fin n)).erase z :=
          Finset.mem_erase.mpr ⟨Ne.symm hzi, Finset.mem_univ i⟩
        have hj_z : j ∈ (Finset.univ : Finset (Fin n)).erase z :=
          Finset.mem_erase.mpr ⟨Ne.symm hzj, Finset.mem_univ j⟩
        have hL1 : IsOrder Finset.univ (z :: i :: j :: R) :=
          isOrder_cons (Finset.mem_univ z)
            (isOrder_cons hi_z
              (isOrder_cons (Finset.mem_erase.mpr ⟨Ne.symm hije, hj_z⟩) hR1))
        have hL2 : IsOrder Finset.univ (z :: j :: i :: R) :=
          isOrder_cons (Finset.mem_univ z)
            (isOrder_cons hj_z
              (isOrder_cons (Finset.mem_erase.mpr ⟨hije, hi_z⟩) hR2))
        have hother : ∀ k, k ≠ i → k ≠ j →
            isFirstIn (rowSet G k) k (z :: i :: j :: R) =
              isFirstIn (rowSet G k) k (z :: j :: i :: R) := by
          intro k hki hkj
          by_cases hkz : k = z
          · subst hkz
            simp only [isFirstIn, ↓reduceIte]
          · have hzk : z ≠ k := Ne.symm hkz
            simp only [isFirstIn, hzk, ↓reduceIte]
            by_cases hzS : z ∈ rowSet G k
            · simp only [hzS, ↓reduceIte]
            · simp only [hzS, ↓reduceIte]
              exact isFirstIn_swap2 (rowSet G k) R hki hkj
        have hpair := pair_eq_of_goodSet_eq G hije (hconst _ _ hL1 hL2) hother
        have h1i : isFirstIn (rowSet G i) i (z :: i :: j :: R) = !G i z := by
          simp only [isFirstIn, hzi, ↓reduceIte, mem_rowSet]
          cases G i z <;> rfl
        have h2i : isFirstIn (rowSet G i) i (z :: j :: i :: R) = false := by
          have hji_ne : j ≠ i := Ne.symm hije
          have hjmem : j ∈ rowSet G i := (mem_rowSet G i j).mpr hij
          simp only [isFirstIn, hzi, hji_ne, hjmem, ↓reduceIte]
          by_cases hzS : z ∈ rowSet G i <;> simp only [hzS, ↓reduceIte]
        have h1j : isFirstIn (rowSet G j) j (z :: i :: j :: R) = false := by
          have himem : i ∈ rowSet G j := (mem_rowSet G j i).mpr hji
          simp only [isFirstIn, hzj, hije, himem, ↓reduceIte]
          by_cases hzS : z ∈ rowSet G j <;> simp only [hzS, ↓reduceIte]
        have h2j : isFirstIn (rowSet G j) j (z :: j :: i :: R) = !G j z := by
          simp only [isFirstIn, hzj, ↓reduceIte, mem_rowSet]
          cases G j z <;> rfl
        rw [h1i, h2i, h1j, h2j] at hpair
        cases hGiz : G i z <;> cases hGjz : G j z
        · rfl
        · simp only [hGiz, hGjz, Bool.not_false, Bool.not_true, ↓reduceIte,
            Bool.false_eq_true] at hpair
          exact absurd hpair (by decide)
        · simp only [hGiz, hGjz, Bool.not_false, Bool.not_true, ↓reduceIte,
            Bool.false_eq_true] at hpair
          exact absurd hpair (by decide)
        · rfl

private lemma rank_le_and_score_eq_of_blocks {n : ℕ} (G : Fin n → Fin n → Bool) (w : Fin n → ℕ)
    (hdiag : ∀ i, G i i = true) (hw : ∀ i, 0 < w i)
    (hblocks : ∀ i j, G i j = true → ∀ z, G i z = G j z) :
    let M : Matrix (Fin n) (Fin n) (ZMod 2) := fun a b => if G a b then 1 else 0
    let mass := fun (a : Fin n) => ∑ b : Fin n, if G a b then w b else 0
    let score : ℚ := ∑ i : Fin n, (w i : ℚ) / (mass i : ℚ)
    (M.rank : ℚ) ≤ score := by
  intro M mass score
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Finset (Finset (Fin n)) := Finset.univ.image (rowSet G)
  have hmass : ∀ i : Fin n, (mass i : ℚ) = totW w (rowSet G i) := by
    intro i
    dsimp only [mass, totW, rowSet]
    rw [Nat.cast_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    cases G i b <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_zero]
  have hscore : score = (S.card : ℚ) := by
    dsimp only [score]
    rw [← Finset.sum_fiberwise_of_maps_to
      (fun i _ => Finset.mem_image_of_mem (rowSet G) (Finset.mem_univ i))]
    have hfiber : ∀ C ∈ S,
        ∑ i ∈ Finset.univ.filter (fun i => rowSet G i = C),
          (w i : ℚ) / (mass i : ℚ) = 1 := by
      intro C hC
      rcases Finset.mem_image.mp hC with ⟨a, _, rfl⟩
      have hfilt : Finset.univ.filter (fun i => rowSet G i = rowSet G a) = rowSet G a := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro heq
          rw [← heq, mem_rowSet]
          exact hdiag i
        · intro hi
          have hai : G a i = true := (mem_rowSet G a i).mp hi
          ext z
          simp only [mem_rowSet, hblocks a i hai z]
      rw [hfilt]
      have hcongr :
          ∑ i ∈ rowSet G a, (w i : ℚ) / (mass i : ℚ) =
            ∑ i ∈ rowSet G a, (w i : ℚ) / totW w (rowSet G a) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hia : rowSet G i = rowSet G a := by
          have hai : G a i = true := (mem_rowSet G a i).mp hi
          ext z
          simp only [mem_rowSet, hblocks a i hai z]
        rw [hmass i, hia]
      rw [hcongr, sum_div_const]
      have hne : totW w (rowSet G a) ≠ 0 :=
        totW_ne_zero w ⟨a, (mem_rowSet G a a).mpr (hdiag a)⟩ (fun x _ => hw x)
      exact div_self hne
    rw [Finset.sum_congr rfl hfiber, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hrank : M.rank ≤ S.card := by
    let e : Finset (Fin n) → (Fin n → ZMod 2) :=
      fun C i => if rowSet G i = C then 1 else 0
    have hrange : LinearMap.range M.mulVecLin ≤
        Submodule.span (ZMod 2) ((S.image e : Finset (Fin n → ZMod 2)) : Set (Fin n → ZMod 2)) := by
      rintro y ⟨x, rfl⟩
      have hdecomp : M.mulVecLin x = ∑ C ∈ S, (∑ b ∈ C, x b) • e C := by
        funext i
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply, smul_eq_mul, e]
        have hiS : rowSet G i ∈ S := Finset.mem_image_of_mem (rowSet G) (Finset.mem_univ i)
        rw [Finset.sum_eq_single (rowSet G i)]
        · simp only [↓reduceIte, mul_one]
          change (∑ b : Fin n, (if G i b then (1 : ZMod 2) else 0) * x b) = ∑ b ∈ rowSet G i, x b
          rw [rowSet, Finset.sum_filter]
          refine Finset.sum_congr rfl fun b _ => ?_
          cases G i b <;> simp only [Bool.false_eq_true, ↓reduceIte, one_mul, zero_mul]
        · intro C _ hCne
          have hne : rowSet G i ≠ C := Ne.symm hCne
          simp only [hne, ↓reduceIte, mul_zero]
        · intro hnot
          exact absurd hiS hnot
      rw [hdecomp]
      refine Submodule.sum_mem _ fun C hC => ?_
      exact Submodule.smul_mem _ _
        (Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem e hC)))
    calc
      M.rank = Module.finrank (ZMod 2) (LinearMap.range M.mulVecLin) := rfl
      _ ≤ Module.finrank (ZMod 2)
            (Submodule.span (ZMod 2)
              ((S.image e : Finset (Fin n → ZMod 2)) : Set (Fin n → ZMod 2))) :=
          Submodule.finrank_mono hrange
      _ ≤ ((S.image e : Finset (Fin n → ZMod 2)) : Set (Fin n → ZMod 2)).toFinset.card :=
          finrank_span_le_card _
      _ = (S.image e).card := by
          have htf :
              ((S.image e : Finset (Fin n → ZMod 2)) : Set (Fin n → ZMod 2)).toFinset =
                S.image e := by
            ext v
            simp only [Set.mem_toFinset, Finset.mem_coe]
          rw [htf]
      _ ≤ S.card := Finset.card_image_le
  rw [hscore]
  exact Nat.cast_le.mpr hrank

end PEqualNP.Outside.L_lib_624

theorem PEqualNP.Outside.L_lib_624 : ∀ (n : ℕ) (G : Fin n → Fin n → Bool) (w : Fin n → ℕ),
  (∀ i, G i i = true) → (∀ i, 0 < w i) →
  let M : Matrix (Fin n) (Fin n) (ZMod 2) :=
    fun a b => if G a b then 1 else 0
  let mass := fun (a : Fin n) => ∑ b : Fin n, if G a b then w b else 0
  let score : ℚ := ∑ i : Fin n, (w i : ℚ) / (mass i : ℚ)
  score ≤ (M.rank : ℚ) ∧
  (score = (M.rank : ℚ) ↔ ∀ i j, G i j = true → ∀ z, G i z = G j z) := by
  intro n G w hdiag hw M mass score
  let f : List (Fin n) → ℚ := fun L => ((PEqualNP.Outside.L_lib_624.goodSet G L).card : ℚ)
  have hf_sum : ∀ L : List (Fin n),
      f L = ∑ i : Fin n,
        if PEqualNP.Outside.L_lib_624.isFirstIn
            (PEqualNP.Outside.L_lib_624.rowSet G i) i L then (1 : ℚ) else 0 := by
    intro L
    dsimp only [f, PEqualNP.Outside.L_lib_624.goodSet]
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases PEqualNP.Outside.L_lib_624.isFirstIn (PEqualNP.Outside.L_lib_624.rowSet G i) i L <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_one, Nat.cast_zero]
  have hmass : ∀ i : Fin n,
      (mass i : ℚ) = PEqualNP.Outside.L_lib_624.totW w (PEqualNP.Outside.L_lib_624.rowSet G i) := by
    intro i
    dsimp only [mass, PEqualNP.Outside.L_lib_624.totW, PEqualNP.Outside.L_lib_624.rowSet]
    rw [Nat.cast_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    cases G i b <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_zero]
  have hexp : PEqualNP.Outside.L_lib_624.plExpect w Finset.univ f = score := by
    have hfun : f = fun L => ∑ i : Fin n,
        if PEqualNP.Outside.L_lib_624.isFirstIn
            (PEqualNP.Outside.L_lib_624.rowSet G i) i L then (1 : ℚ) else 0 :=
      funext hf_sum
    rw [hfun, PEqualNP.Outside.L_lib_624.plExpect_sum]
    dsimp only [score]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PEqualNP.Outside.L_lib_624.plExpect_firstIn w Finset.univ
      (PEqualNP.Outside.L_lib_624.rowSet G i) i (fun x _ => hw x)
      (Finset.subset_univ _) ((PEqualNP.Outside.L_lib_624.mem_rowSet G i i).mpr (hdiag i)),
      hmass i]
  have hle_const :=
    PEqualNP.Outside.L_lib_624.plExpect_le_and_eq w Finset.univ f (fun _ => (M.rank : ℚ))
      (fun x _ => hw x)
      (fun L _ => Nat.cast_le.mpr (PEqualNP.Outside.L_lib_624.goodSet_card_le_rank G hdiag L))
  have hconst_exp :
      PEqualNP.Outside.L_lib_624.plExpect w Finset.univ (fun _ => (M.rank : ℚ)) = (M.rank : ℚ) :=
    PEqualNP.Outside.L_lib_624.plExpect_const w Finset.univ (M.rank : ℚ) (fun x _ => hw x)
  rw [hexp, hconst_exp] at hle_const
  refine ⟨hle_const.1, ?_⟩
  constructor
  · intro heq i j hij z
    have hgood_eq : ∀ L, PEqualNP.Outside.L_lib_624.IsOrder Finset.univ L →
        (PEqualNP.Outside.L_lib_624.goodSet G L).card = M.rank := by
      intro L hL
      exact Nat.cast_injective (hle_const.2 heq L hL)
    exact PEqualNP.Outside.L_lib_624.row_eq_of_const_good G hdiag
      (fun L₁ L₂ hL₁ hL₂ => (hgood_eq L₁ hL₁).trans (hgood_eq L₂ hL₂).symm) hij z
  · intro hblocks
    exact le_antisymm hle_const.1
      (PEqualNP.Outside.L_lib_624.rank_le_and_score_eq_of_blocks G w hdiag hw hblocks)
