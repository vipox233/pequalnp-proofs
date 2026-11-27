import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25746

def tab (a b c d e f g h k : Bool) : Fin 4 → Fin 4 → Bool :=
  ![![false, false, false, false], ![false, a, b, c], ![false, d, e, f], ![false, g, h, k]]

def par (H : Fin 4 → Fin 4 → Bool) (π : Equiv.Perm (Fin 4)) (i j : Fin 4) : Bool :=
  Bool.xor (Bool.xor (H i (π i)) (H j (π j))) (Bool.xor (H i (π j)) (H j (π i)))

def am (H : Fin 4 → Fin 4 → Bool) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  fun i j => if H i.succ j.succ then 1 else 0

def tot (H : Fin 4 → Fin 4 → Bool) : ZMod 2 := ∑ i : Fin 3, ∑ j : Fin 3, am H i j

set_option maxRecDepth 100000 in
lemma fa : ∀ a b c d e f g h k : Bool, (am (tab a b c d e f g h k)).det ≠ 0 →
    ∃ (π : Equiv.Perm (Fin 4)) (K : Finset (Fin 4)), K.card = 3 ∧
      ∀ i ∈ K, ∀ j ∈ K, par (tab a b c d e f g h k) π i j = false := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma fb : ∀ a b c d e f g h k : Bool, (am (tab a b c d e f g h k)).det ≠ 0 →
    ∃ (π : Equiv.Perm (Fin 4)) (L : Finset (Fin 4)), L.card ≤ 2 ∧
      ∀ i j : Fin 4, par (tab a b c d e f g h k) π i j = Bool.xor (decide (i ∈ L)) (decide (j ∈ L)) := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma fc : ∀ a b c d e f g h k : Bool, (am (tab a b c d e f g h k)).det ≠ 0 →
    tot (tab a b c d e f g h k) ≠ 0 →
    ∃ (π : Equiv.Perm (Fin 4)) (L : Finset (Fin 4)), L.card ≤ 1 ∧
      ∀ i j : Fin 4, par (tab a b c d e f g h k) π i j = Bool.xor (decide (i ∈ L)) (decide (j ∈ L)) := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma fd : ∀ a b c d e f g h k : Bool, (am (tab a b c d e f g h k)).det ≠ 0 →
    tot (tab a b c d e f g h k) = 0 →
    ∀ (π : Equiv.Perm (Fin 4)) (L : Finset (Fin 4)), L.card ≤ 1 →
      ¬ ∀ i j : Fin 4, par (tab a b c d e f g h k) π i j = Bool.xor (decide (i ∈ L)) (decide (j ∈ L)) := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma fe : ∀ a b c d e f g h k : Bool, (am (tab a b c d e f g h k)).det ≠ 0 →
    ∀ (π : Equiv.Perm (Fin 4)),
      ¬ ∀ i j : Fin 4, par (tab a b c d e f g h k) π i j = false := by
  decide +kernel


def N (G : Fin 4 → Fin 4 → Bool) : Fin 4 → Fin 4 → Bool :=
  fun i j => Bool.xor (Bool.xor (G i j) (G i 0)) (Bool.xor (G 0 j) (G 0 0))

lemma bx : ∀ a b c d p q r s z : Bool,
    Bool.xor (Bool.xor (Bool.xor (Bool.xor a p) (Bool.xor r z)) (Bool.xor (Bool.xor d q) (Bool.xor s z)))
      (Bool.xor (Bool.xor (Bool.xor b p) (Bool.xor s z)) (Bool.xor (Bool.xor c q) (Bool.xor r z))) =
    Bool.xor (Bool.xor a d) (Bool.xor b c) := by
  decide

lemma par_N (G : Fin 4 → Fin 4 → Bool) (π : Equiv.Perm (Fin 4)) (i j : Fin 4) :
    par (N G) π i j = par G π i j :=
  bx (G i (π i)) (G i (π j)) (G j (π i)) (G j (π j)) (G i 0) (G j 0) (G 0 (π i)) (G 0 (π j)) (G 0 0)

lemma bz : ∀ a b c d : Bool, (if Bool.xor (Bool.xor a b) (Bool.xor c d) then (1 : ZMod 2) else 0) =
    (if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0) + (if d then 1 else 0) := by
  decide

lemma eq_tab (H : Fin 4 → Fin 4 → Bool) (h0 : ∀ j, H 0 j = false) (h1 : ∀ i, H i 0 = false) :
    H = tab (H 1 1) (H 1 2) (H 1 3) (H 2 1) (H 2 2) (H 2 3) (H 3 1) (H 3 2) (H 3 3) := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [tab, h0, h1]

lemma N0 (G : Fin 4 → Fin 4 → Bool) (j : Fin 4) : N G 0 j = false := by simp [N]

lemma N1 (G : Fin 4 → Fin 4 → Bool) (i : Fin 4) : N G i 0 = false := by simp [N]

lemma sumlem (b : Fin 4 → Fin 4 → ZMod 2) :
    ∑ i : Fin 3, ∑ j : Fin 3, (b i.succ j.succ + b i.succ 0 + b 0 j.succ + b 0 0) =
      ∑ i : Fin 4, ∑ j : Fin 4, b i j := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  have s0 : Fin.succ (0 : Fin 3) = 1 := rfl
  have s1 : Fin.succ (1 : Fin 3) = 2 := rfl
  have s2 : Fin.succ (2 : Fin 3) = 3 := rfl
  simp only [Fin.sum_univ_four, Fin.sum_univ_three, s0, s1, s2]
  linear_combination (b 1 0 + b 2 0 + b 3 0 + b 0 1 + b 0 2 + b 0 3 + 4 * b 0 0) * h2

theorem core (G : Fin 4 → Fin 4 → Bool) (u t : ℕ) (hdet : (am (N G)).det ≠ 0) :
    ((∃ (π : Equiv.Perm (Fin 4)) (K L : Finset (Fin 4)),
      L ⊆ K ∧ L.card ≤ u ∧ 4 ≤ K.card + t ∧
      ∀ i ∈ K, ∀ j ∈ K, par G π i j = Bool.xor (decide (i ∈ L)) (decide (j ∈ L))) ↔
      (if u = 0 ∨ (u = 1 ∧ tot (N G) = 0) then 1 else 0) ≤ t) := by
  have e := eq_tab (N G) (N0 G) (N1 G)
  have ha : ∃ (π : Equiv.Perm (Fin 4)) (K : Finset (Fin 4)), K.card = 3 ∧
      ∀ i ∈ K, ∀ j ∈ K, par (N G) π i j = false := by
    rw [e] at hdet ⊢
    exact fa _ _ _ _ _ _ _ _ _ hdet
  have hb : ∃ (π : Equiv.Perm (Fin 4)) (L : Finset (Fin 4)), L.card ≤ 2 ∧
      ∀ i j : Fin 4, par (N G) π i j = Bool.xor (decide (i ∈ L)) (decide (j ∈ L)) := by
    rw [e] at hdet ⊢
    exact fb _ _ _ _ _ _ _ _ _ hdet
  have hc : tot (N G) ≠ 0 → ∃ (π : Equiv.Perm (Fin 4)) (L : Finset (Fin 4)), L.card ≤ 1 ∧
      ∀ i j : Fin 4, par (N G) π i j = Bool.xor (decide (i ∈ L)) (decide (j ∈ L)) := by
    rw [e] at hdet ⊢
    exact fc _ _ _ _ _ _ _ _ _ hdet
  have hd : tot (N G) = 0 → ∀ (π : Equiv.Perm (Fin 4)) (L : Finset (Fin 4)), L.card ≤ 1 →
      ¬ ∀ i j : Fin 4, par (N G) π i j = Bool.xor (decide (i ∈ L)) (decide (j ∈ L)) := by
    rw [e] at hdet ⊢
    exact fd _ _ _ _ _ _ _ _ _ hdet
  have he : ∀ (π : Equiv.Perm (Fin 4)), ¬ ∀ i j : Fin 4, par (N G) π i j = false := by
    rw [e] at hdet ⊢
    exact fe _ _ _ _ _ _ _ _ _ hdet
  simp only [par_N] at ha hb hc hd he
  constructor
  · rintro ⟨π, K, L, hLK, hLu, hKt, hP⟩
    by_cases ht : t = 0
    · subst ht
      have hK4 : K.card ≤ 4 := by
        have := Finset.card_le_univ K
        simpa using this
      have hK : K = Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [Fintype.card_fin]
        omega
      subst hK
      have hP' : ∀ i j : Fin 4, par G π i j = Bool.xor (decide (i ∈ L)) (decide (j ∈ L)) :=
        fun i j => hP i (Finset.mem_univ i) j (Finset.mem_univ j)
      have hcond : ¬ (u = 0 ∨ (u = 1 ∧ tot (N G) = 0)) := by
        rintro (hu | ⟨hu, htot⟩)
        · have hL : L = ∅ := Finset.card_eq_zero.mp (by omega)
          subst hL
          exact he π (fun i j => by simpa using hP' i j)
        · exact hd htot π L (by omega) hP'
      simp [hcond]
    · split_ifs <;> omega
  · intro hc'
    by_cases ht : t = 0
    · subst ht
      have hcond : ¬ (u = 0 ∨ (u = 1 ∧ tot (N G) = 0)) := by
        intro h
        simp [h] at hc'
      by_cases hu : u = 1
      · have htot : tot (N G) ≠ 0 := fun h => hcond (Or.inr ⟨hu, h⟩)
        obtain ⟨π, L, hL, hP⟩ := hc htot
        exact ⟨π, Finset.univ, L, Finset.subset_univ _, by omega, by simp, fun i _ j _ => hP i j⟩
      · have hu0 : u ≠ 0 := fun h => hcond (Or.inl h)
        obtain ⟨π, L, hL, hP⟩ := hb
        exact ⟨π, Finset.univ, L, Finset.subset_univ _, by omega, by simp, fun i _ j _ => hP i j⟩
    · obtain ⟨π, K, hK, hP⟩ := ha
      exact ⟨π, K, ∅, Finset.empty_subset _, by simp, by omega,
        fun i hi j hj => by simpa using hP i hi j hj⟩

end PEqualNP.Outside.L_meta_25746

theorem PEqualNP.Outside.L_meta_25746 : ∀ (G : Fin 4 → Fin 4 → Bool) (u t : ℕ),
  let bit := fun (i j : Fin 4) => (if G i j then 1 else 0 : ZMod 2)
  let anchored : Matrix (Fin 3) (Fin 3) (ZMod 2) := fun i j =>
    bit i.succ j.succ + bit i.succ 0 + bit 0 j.succ + bit 0 0
  let total := ∑ i : Fin 4, ∑ j : Fin 4, bit i j
  let cost : ℕ := if u = 0 ∨ (u = 1 ∧ total = 0) then 1 else 0
  anchored.det ≠ 0 →
  ((∃ (π : Equiv.Perm (Fin 4)) (K L : Finset (Fin 4)),
    L ⊆ K ∧ L.card ≤ u ∧ 4 ≤ K.card + t ∧
    ∀ i ∈ K, ∀ j ∈ K,
      Bool.xor (Bool.xor (G i (π i)) (G j (π j))) (Bool.xor (G i (π j)) (G j (π i))) =
      Bool.xor (decide (i ∈ L)) (decide (j ∈ L))) ↔ cost ≤ t) := by
  intro G u t bit anchored total cost hdet
  have e1 : anchored = PEqualNP.Outside.L_meta_25746.am (PEqualNP.Outside.L_meta_25746.N G) := by
    funext i j
    exact (PEqualNP.Outside.L_meta_25746.bz (G i.succ j.succ) (G i.succ 0) (G 0 j.succ) (G 0 0)).symm
  have e2 : PEqualNP.Outside.L_meta_25746.tot (PEqualNP.Outside.L_meta_25746.N G) = total := by
    have h := PEqualNP.Outside.L_meta_25746.sumlem bit
    refine Eq.trans ?_ h
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      PEqualNP.Outside.L_meta_25746.bz (G i.succ j.succ) (G i.succ 0) (G 0 j.succ) (G 0 0)
  rw [e1] at hdet
  have key := PEqualNP.Outside.L_meta_25746.core G u t hdet
  rw [e2] at key
  exact key
