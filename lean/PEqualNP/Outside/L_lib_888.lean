import PEqualNP.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

namespace PEqualNP.Outside.L_lib_888_aux

open scoped Classical

abbrev F2 := ZMod 2
abbrev V2 := Fin 2 → F2
abbrev V4 := Fin 4 → F2

section Graph

variable {X : Type*} [DecidableEq X]
variable (f : X → X) (S : Finset X)

def edge (x y : X) : Prop := x ∈ S ∧ y ∈ S ∧ (f x = y ∨ f y = x)

noncomputable def cc (x : X) : Finset X := S.filter (Relation.ReflTransGen (edge f S) x)
noncomputable def pcs : Finset (Finset X) := S.image (cc f S)
def halo (C : Finset X) : Finset X := C ∪ C.image f

omit [DecidableEq X] in
lemma selfMem {x : X} (hx : x ∈ S) : x ∈ cc f S x :=
  Finset.mem_filter.mpr ⟨hx, .refl⟩

omit [DecidableEq X] in
lemma same {x y : X} (h : Relation.ReflTransGen (edge f S) x y) :
    cc f S x = cc f S y := by
  let : Std.Symm (edge f S) := ⟨fun _ _ e => ⟨e.2.1, e.1, e.2.2.symm⟩⟩
  have back := Std.Symm.symm (r := Relation.ReflTransGen (edge f S)) _ _ h
  ext z
  simp only [cc, Finset.mem_filter]
  exact and_congr_right fun _ => ⟨fun p => back.trans p, fun p => h.trans p⟩

lemma center {C : Finset X} (hC : C ∈ pcs f S) {x : X} (hx : x ∈ C) :
    x ∈ S ∧ cc f S x = C := by
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨hx, p⟩ := Finset.mem_filter.mp hx
  exact ⟨hx, (same f S p).symm⟩

lemma populated {C : Finset X} (hC : C ∈ pcs f S) : C.Nonempty := by
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hC
  exact ⟨w, selfMem f S hw⟩

lemma joined {C D : Finset X} (hc : C ∈ pcs f S) (hd : D ∈ pcs f S)
    {x y : X} (hx : x ∈ C) (hy : y ∈ D) (h : x = y ∨ f x = y ∨ f y = x) : C = D := by
  obtain ⟨xs, xc⟩ := center f S hc hx
  obtain ⟨ys, yc⟩ := center f S hd hy
  rw [← xc, ← yc]
  rcases h with rfl | h
  · rfl
  · exact same f S (.single ⟨xs, ys, h⟩)

lemma separate (inj : Function.Injective f) :
    (↑(pcs f S) : Set (Finset X)).PairwiseDisjoint (halo f) := by
  intro C hc D hd ne
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  simp only [halo, Finset.mem_union, Finset.mem_image] at hz hz'
  rcases hz with h | ⟨x, h, rfl⟩ <;> rcases hz' with h' | ⟨y, h', eq⟩
  · exact ne (joined f S hc hd h h' (Or.inl rfl))
  · exact ne (joined f S hc hd h h' (Or.inr (Or.inr eq)))
  · exact ne (joined f S hc hd h h' (Or.inr (Or.inl rfl)))
  · exact ne (joined f S hc hd h h' (Or.inl (inj eq).symm))

lemma pcs_pairwiseDisjoint :
    (↑(pcs f S) : Set (Finset X)).PairwiseDisjoint id := by
  intro C hc D hd ne
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  exact ne (joined f S hc hd hz hz' (Or.inl rfl))

lemma pcs_biUnion_eq : (pcs f S).biUnion id = S := by
  ext x
  simp only [Finset.mem_biUnion, id_eq]
  constructor
  · rintro ⟨C, hC, hx⟩
    exact (center f S hC hx).1
  · intro hx
    exact ⟨cc f S x, Finset.mem_image_of_mem _ hx, selfMem f S hx⟩

end Graph

section Cycle

variable {t : ℕ} (ht : 0 < t)

def idx (k : ℕ) : Fin (6 * t) := ⟨k % (6 * t), Nat.mod_lt _ (by omega)⟩
def nxt (i : Fin (6 * t)) : Fin (6 * t) := ⟨(i.val + 1) % (6 * t), Nat.mod_lt _ (by omega)⟩
def prv (i : Fin (6 * t)) : Fin (6 * t) := ⟨(i.val + 6 * t - 1) % (6 * t), Nat.mod_lt _ (by omega)⟩

lemma mod_eq_sub_of_lt2 {a m : ℕ} (h1 : m ≤ a) (h2 : a < 2 * m) : a % m = a - m := by
  have e : a = (a - m) + m := by omega
  conv_lhs => rw [e]
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

lemma idx_val (k : ℕ) : (idx ht k).val = k % (6 * t) := rfl

lemma idx_self (i : Fin (6 * t)) : idx ht i.val = i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

lemma nxt_val (i : Fin (6 * t)) :
    (nxt ht i).val = if i.val + 1 < 6 * t then i.val + 1 else 0 := by
  have hi := i.isLt
  unfold nxt
  dsimp only
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have e : i.val + 1 = 6 * t := by omega
    simp [e]

lemma prv_val (i : Fin (6 * t)) :
    (prv ht i).val = if i.val = 0 then 6 * t - 1 else i.val - 1 := by
  have hi := i.isLt
  unfold prv
  dsimp only
  split_ifs with h
  · simp [h, Nat.mod_eq_of_lt (by omega : 6 * t - 1 < 6 * t)]
  · have e : i.val + 6 * t - 1 = (i.val - 1) + 6 * t := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

lemma nxt_idx (k : ℕ) : nxt ht (idx ht k) = idx ht (k + 1) := by
  apply Fin.ext
  change (k % (6 * t) + 1) % (6 * t) = (k + 1) % (6 * t)
  rw [Nat.mod_add_mod]

lemma nxt_prv (i : Fin (6 * t)) : nxt ht (prv ht i) = i := by
  have hi := i.isLt
  apply Fin.ext
  by_cases h : i.val = 0
  · rw [nxt_val, prv_val, if_pos h, if_neg (by omega)]; omega
  · rw [nxt_val, prv_val, if_neg h, if_pos (by omega)]; omega

lemma prv_nxt (i : Fin (6 * t)) : prv ht (nxt ht i) = i := by
  have hi := i.isLt
  apply Fin.ext
  by_cases h : i.val + 1 < 6 * t
  · rw [prv_val, nxt_val, if_pos h, if_neg (by omega)]; omega
  · rw [prv_val, nxt_val, if_neg h, if_pos rfl]; omega

lemma ninj : Function.Injective (nxt ht) := by
  intro i j h
  have := congrArg (prv ht) h
  simpa [prv_nxt] using this

lemma nxt_parity (i : Fin (6 * t)) : (nxt ht i).val % 2 = (i.val + 1) % 2 := by
  have hi := i.isLt
  rw [nxt_val]
  split_ifs <;> omega

lemma idx_mod6 (k : ℕ) : (idx ht k).val % 6 = k % 6 := by
  change (k % (6 * t)) % 6 = k % 6
  exact Nat.mod_mod_of_dvd k ⟨t, rfl⟩

lemma idx_mod2 (k : ℕ) : (idx ht k).val % 2 = k % 2 := by
  change (k % (6 * t)) % 2 = k % 2
  exact Nat.mod_mod_of_dvd k ⟨3 * t, by ring⟩

lemma idx_div2_mod3 (k : ℕ) : (idx ht k).val / 2 % 3 = k / 2 % 3 := by
  have h6 := idx_mod6 ht k
  omega

lemma idx_add_dist (x y : Fin (6 * t)) :
    idx ht (x.val + (y.val + 6 * t - x.val) % (6 * t)) = y := by
  apply Fin.ext
  change (x.val + (y.val + 6 * t - x.val) % (6 * t)) % (6 * t) = y.val
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have h1 : x.val + (y.val + 6 * t - x.val) = y.val + 6 * t := by have := x.isLt; omega
  rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt y.isLt]

lemma idx_inj_range (s : Fin (6 * t)) {m : ℕ} (hm : m ≤ 6 * t)
    {j₁ j₂ : ℕ} (h1 : j₁ < m) (h2 : j₂ < m)
    (heq : idx ht (s.val + j₁) = idx ht (s.val + j₂)) : j₁ = j₂ := by
  have hv := congrArg Fin.val heq
  change (s.val + j₁) % (6 * t) = (s.val + j₂) % (6 * t) at hv
  have hs := s.isLt
  by_cases c1 : s.val + j₁ < 6 * t <;> by_cases c2 : s.val + j₂ < 6 * t
  · rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_of_lt c2] at hv; omega
  · rw [Nat.mod_eq_of_lt c1, mod_eq_sub_of_lt2 (by omega) (by omega)] at hv; omega
  · rw [mod_eq_sub_of_lt2 (by omega) (by omega), Nat.mod_eq_of_lt c2] at hv; omega
  · rw [mod_eq_sub_of_lt2 (by omega) (by omega), mod_eq_sub_of_lt2 (by omega) (by omega)] at hv; omega

def arc (s : Fin (6 * t)) (m : ℕ) : Finset (Fin (6 * t)) :=
  (Finset.range m).image (fun k => idx ht (s.val + k))

lemma card_arc (s : Fin (6 * t)) {m : ℕ} (hm : m ≤ 6 * t) : (arc ht s m).card = m := by
  unfold arc
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro j₁ hj₁ j₂ hj₂ heq
  exact idx_inj_range ht s hm (Finset.mem_range.mp hj₁) (Finset.mem_range.mp hj₂) heq

lemma mem_arc_iff (s : Fin (6 * t)) (m : ℕ) (x : Fin (6 * t)) :
    x ∈ arc ht s m ↔ ∃ k < m, idx ht (s.val + k) = x := by
  simp [arc]

lemma start_of_proper {C : Finset (Fin (6 * t))} (ne : C.Nonempty) (pr : C ≠ Finset.univ) :
    ∃ s ∈ C, prv ht s ∉ C := by
  by_contra! h
  obtain ⟨w, hw⟩ : ∃ w : Fin (6 * t), w ∉ C := by
    by_contra! hall
    exact pr (Finset.eq_univ_of_forall hall)
  have hstep : ∀ x : Fin (6 * t), x ∉ C → nxt ht x ∉ C := by
    intro x hx hnx
    exact hx (prv_nxt ht x ▸ h (nxt ht x) hnx)
  have go (k : ℕ) : idx ht (w.val + k) ∉ C := by
    induction k with
    | zero => simpa [idx_self] using hw
    | succ k ih =>
      rw [← add_assoc, ← nxt_idx]
      exact hstep _ ih
  obtain ⟨y, hy⟩ := ne
  have e : idx ht (w.val + (6 * t - w.val + y.val)) = y := by
    apply Fin.ext
    change (w.val + (6 * t - w.val + y.val)) % (6 * t) = y.val
    have h1 : w.val + (6 * t - w.val + y.val) = y.val + 6 * t := by have := w.isLt; omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt y.isLt]
  exact go (6 * t - w.val + y.val) (e.symm ▸ hy)

lemma comp_arc_of_start {S : Finset (Fin (6 * t))} (hS : S ≠ Finset.univ)
    {s : Fin (6 * t)} (hs : s ∈ S) (hp : prv ht s ∉ S) :
    cc (nxt ht) S s = arc ht s (cc (nxt ht) S s).card ∧
      (cc (nxt ht) S s).card < 6 * t ∧
      idx ht (s.val + (cc (nxt ht) S s).card) ∉ S := by
  have hex : ∃ k : ℕ, idx ht (s.val + k) ∉ S := by
    have ⟨y, hy⟩ : ∃ y : Fin (6 * t), y ∉ S := by
      by_contra! hall
      exact hS (Finset.eq_univ_of_forall hall)
    refine ⟨6 * t - s.val + y.val, ?_⟩
    have e : idx ht (s.val + (6 * t - s.val + y.val)) = y := by
      apply Fin.ext
      change (s.val + (6 * t - s.val + y.val)) % (6 * t) = y.val
      have h1 : s.val + (6 * t - s.val + y.val) = y.val + 6 * t := by have := s.isLt; omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt y.isLt]
    rwa [e]
  let k0 := Nat.find hex
  have hk0_out : idx ht (s.val + k0) ∉ S := Nat.find_spec hex
  have hk0_pos : 0 < k0 := by
    by_contra h0
    have : k0 = 0 := by omega
    rw [this, add_zero, idx_self] at hk0_out
    exact hk0_out hs
  have hk0_lt : k0 < 6 * t := by
    by_contra hge
    have hprev : 6 * t - 1 < k0 := by omega
    have hin : idx ht (s.val + (6 * t - 1)) ∈ S := by
      by_contra hout
      exact Nat.find_min hex hprev hout
    have e : idx ht (s.val + (6 * t - 1)) = prv ht s := by
      apply Fin.ext
      change (s.val + (6 * t - 1)) % (6 * t) = (s.val + 6 * t - 1) % (6 * t)
      congr 1; omega
    rw [e] at hin
    exact hp hin
  have hsub1 : arc ht s k0 ⊆ cc (nxt ht) S s := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := (mem_arc_iff ht s k0 x).mp hx
    clear hx
    induction k with
    | zero =>
      rw [add_zero, idx_self]
      exact selfMem (nxt ht) S hs
    | succ k ih =>
      have hk' : k < k0 := by omega
      have hprev := ih hk'
      obtain ⟨hprevS, hpath⟩ := Finset.mem_filter.mp hprev
      have hcurS : idx ht (s.val + (k + 1)) ∈ S := by
        by_contra hout
        exact Nat.find_min hex hk hout
      refine Finset.mem_filter.mpr ⟨hcurS, hpath.tail ⟨hprevS, hcurS, Or.inl ?_⟩⟩
      rw [← add_assoc, nxt_idx]
  have hsub2 : cc (nxt ht) S s ⊆ arc ht s k0 := by
    intro x hx
    obtain ⟨hxS, hpath⟩ := Finset.mem_filter.mp hx
    clear hx hxS
    induction hpath with
    | refl =>
      exact (mem_arc_iff ht s k0 s).mpr ⟨0, hk0_pos, by rw [add_zero, idx_self]⟩
    | @tail y z _ he ih =>
      obtain ⟨k, hk, hka⟩ := (mem_arc_iff ht s k0 y).mp ih
      rcases he.2.2 with hf | hb
      · have hy : idx ht (s.val + (k + 1)) = z := by
          rw [← add_assoc, ← nxt_idx, hka, hf]
        have hne : k + 1 ≠ k0 := by
          intro eq
          rw [eq] at hy
          exact hk0_out (hy.symm ▸ he.2.1)
        exact (mem_arc_iff ht s k0 z).mpr ⟨k + 1, by omega, hy⟩
      · have hprev_eq : z = prv ht (idx ht (s.val + k)) := by
          rw [hka, ← hb, prv_nxt]
        cases k with
        | zero =>
          rw [add_zero, idx_self] at hprev_eq
          exact (hp (hprev_eq ▸ he.2.1)).elim
        | succ k =>
          have hz : idx ht (s.val + k) = z := by
            rw [hprev_eq, ← add_assoc, ← nxt_idx, prv_nxt]
          exact (mem_arc_iff ht s k0 z).mpr ⟨k, by omega, hz⟩
  have heq : cc (nxt ht) S s = arc ht s k0 := Finset.Subset.antisymm hsub2 hsub1
  have hcard : (cc (nxt ht) S s).card = k0 := by
    rw [heq, card_arc ht s (by omega)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hcard]; exact heq
  · rw [hcard]; exact hk0_lt
  · rw [hcard]; exact hk0_out

lemma comp_arc {S : Finset (Fin (6 * t))} (hS : S ≠ Finset.univ)
    {C : Finset (Fin (6 * t))} (hC : C ∈ pcs (nxt ht) S) :
    ∃ s ∈ C, prv ht s ∉ S ∧ C = arc ht s C.card ∧
      0 < C.card ∧ C.card < 6 * t ∧ idx ht (s.val + C.card) ∉ S := by
  have hne := populated (nxt ht) S hC
  have hpr : C ≠ Finset.univ := by
    intro eq
    apply hS
    apply Finset.eq_univ_of_forall
    intro x
    exact (center (nxt ht) S hC (eq.symm ▸ Finset.mem_univ x)).1
  obtain ⟨s, hsC, hpsC⟩ := start_of_proper ht hne hpr
  obtain ⟨hsS, hcs⟩ := center (nxt ht) S hC hsC
  have hpsS : prv ht s ∉ S := by
    intro hpS
    apply hpsC
    rw [← hcs]
    exact Finset.mem_filter.mpr ⟨hpS, .single ⟨hsS, hpS, Or.inr (nxt_prv ht s)⟩⟩
  obtain ⟨harc, hlt, hout⟩ := comp_arc_of_start ht hS hsS hpsS
  rw [hcs] at harc hlt hout
  exact ⟨s, hsC, hpsS, harc, Finset.card_pos.mpr hne, hlt, hout⟩

lemma halo_arc (s : Fin (6 * t)) {m : ℕ} (hm : 0 < m) :
    halo (nxt ht) (arc ht s m) = arc ht s (m + 1) := by
  ext x
  simp only [halo, Finset.mem_union, Finset.mem_image, mem_arc_iff]
  constructor
  · rintro (⟨k, hk, rfl⟩ | ⟨y, ⟨k, hk, rfl⟩, rfl⟩)
    · exact ⟨k, by omega, rfl⟩
    · exact ⟨k + 1, by omega, by rw [← add_assoc, nxt_idx]⟩
  · rintro ⟨k, hk, rfl⟩
    by_cases hk' : k < m
    · exact Or.inl ⟨k, hk', rfl⟩
    · have hk1 : k = m := by omega
      rw [hk1]
      refine Or.inr ⟨idx ht (s.val + (m - 1)), ⟨m - 1, by omega, rfl⟩, ?_⟩
      rw [nxt_idx]; congr 1; omega

lemma halo_card_eq {S : Finset (Fin (6 * t))} (hS : S ≠ Finset.univ)
    {C : Finset (Fin (6 * t))} (hC : C ∈ pcs (nxt ht) S) :
    (halo (nxt ht) C).card = C.card + 1 := by
  obtain ⟨s, _, _, harc, hpos, hlt, _⟩ := comp_arc ht hS hC
  conv_lhs => rw [harc, halo_arc ht s hpos, card_arc ht s (by omega)]

lemma sum_halo_le {S : Finset (Fin (6 * t))} (hS : S ≠ Finset.univ) :
    ∑ C ∈ pcs (nxt ht) S, (C.card + 1) ≤ 6 * t := by
  have h1 : ∑ C ∈ pcs (nxt ht) S, (C.card + 1) =
      ∑ C ∈ pcs (nxt ht) S, (halo (nxt ht) C).card :=
    Finset.sum_congr rfl fun C hC => (halo_card_eq ht hS hC).symm
  rw [h1, ← Finset.card_biUnion (separate (nxt ht) S (ninj ht))]
  simpa using Finset.card_le_univ ((pcs (nxt ht) S).biUnion (halo (nxt ht)))

lemma mem_biUnion_halo_iff {S : Finset (Fin (6 * t))} (x : Fin (6 * t)) :
    x ∈ (pcs (nxt ht) S).biUnion (halo (nxt ht)) ↔ x ∈ S ∨ prv ht x ∈ S := by
  simp only [Finset.mem_biUnion, halo, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨C, hC, hx | ⟨y, hy, rfl⟩⟩
    · exact Or.inl (center (nxt ht) S hC hx).1
    · rw [prv_nxt]
      exact Or.inr (center (nxt ht) S hC hy).1
  · rintro (hx | hpx)
    · exact ⟨cc (nxt ht) S x, Finset.mem_image_of_mem _ hx, Or.inl (selfMem (nxt ht) S hx)⟩
    · exact ⟨cc (nxt ht) S (prv ht x), Finset.mem_image_of_mem _ hpx,
        Or.inr ⟨prv ht x, selfMem (nxt ht) S hpx, nxt_prv ht x⟩⟩

end Cycle

section Columns

def col2 (r : ℕ) : V2 :=
  if r % 3 = 0 then ![1, 0] else if r % 3 = 1 then ![0, 1] else ![1, 1]

def hPat (k : ℕ) : V4 :=
  fun b => if k % 2 = b.val / 2 ∧ (k / 2 % 3 = b.val % 2 ∨ k / 2 % 3 = 2) then 1 else 0

def hVec {t : ℕ} (i : Fin (6 * t)) : V4 :=
  fun b => if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2) then 1 else 0

def hSum {t : ℕ} (C : Finset (Fin (6 * t))) : V4 := ∑ i ∈ C, hVec i

def evenProj : V4 →ₗ[F2] V2 where
  toFun v b := v ⟨b.val, by omega⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def oddProj : V4 →ₗ[F2] V2 where
  toFun v b := v ⟨b.val + 2, by omega⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def incEven : V2 →ₗ[F2] V4 where
  toFun u b := if h : b.val < 2 then u ⟨b.val, h⟩ else 0
  map_add' u v := by ext b; dsimp; split_ifs <;> simp
  map_smul' c u := by ext b; dsimp; split_ifs <;> simp

def incOdd : V2 →ₗ[F2] V4 where
  toFun u b := if h : 2 ≤ b.val then u ⟨b.val - 2, by omega⟩ else 0
  map_add' u v := by ext b; dsimp; split_ifs <;> simp
  map_smul' c u := by ext b; dsimp; split_ifs <;> simp

lemma evenProj_incEven (u : V2) : evenProj (incEven u) = u := by
  ext b; fin_cases b <;> rfl

lemma oddProj_incEven (u : V2) : oddProj (incEven u) = 0 := by
  ext b; fin_cases b <;> rfl

lemma evenProj_incOdd (u : V2) : evenProj (incOdd u) = 0 := by
  ext b; fin_cases b <;> rfl

lemma oddProj_incOdd (u : V2) : oddProj (incOdd u) = u := by
  ext b; fin_cases b <;> rfl

lemma incEven_inj : Function.Injective incEven := fun u v h => by
  have := congrArg evenProj h
  simpa [evenProj_incEven] using this

lemma incOdd_inj : Function.Injective incOdd := fun u v h => by
  have := congrArg oddProj h
  simpa [oddProj_incOdd] using this

lemma v4_decomp (v : V4) : v = incEven (evenProj v) + incOdd (oddProj v) := by
  ext b; fin_cases b <;> simp [incEven, incOdd, evenProj, oddProj]

lemma v4_eq_zero_iff (v : V4) : v = 0 ↔ evenProj v = 0 ∧ oddProj v = 0 := by
  constructor
  · rintro rfl; simp
  · rintro ⟨he, ho⟩
    rw [v4_decomp v, he, ho]
    simp

lemma range_incEven_inf_incOdd :
    LinearMap.range incEven ⊓ LinearMap.range incOdd = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  obtain ⟨u, hu⟩ := hv.1
  obtain ⟨w, hw⟩ := hv.2
  have he : evenProj v = 0 := by rw [← hw, evenProj_incOdd]
  have ho : oddProj v = 0 := by rw [← hu, oddProj_incEven]
  exact (v4_eq_zero_iff v).mpr ⟨he, ho⟩

lemma range_incEven_sup_incOdd :
    LinearMap.range incEven ⊔ LinearMap.range incOdd = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro v
  rw [v4_decomp v]
  exact Submodule.add_mem_sup (LinearMap.mem_range_self incEven _) (LinearMap.mem_range_self incOdd _)

lemma zmod2_cases (c : F2) : c = 0 ∨ c = 1 := by
  rcases c with ⟨v, hv⟩
  interval_cases v
  · left; rfl
  · right; rfl

lemma zmod2_ne_zero_iff (c : F2) : c ≠ 0 ↔ c = 1 := by
  rcases zmod2_cases c with rfl | rfl <;> simp

lemma v2_add_self (u : V2) : u + u = 0 := by
  ext b; simp [CharTwo.add_self_eq_zero]

lemma v4_add_self (v : V4) : v + v = 0 := by
  ext b; simp [CharTwo.add_self_eq_zero]

lemma col2_mod3 (r : ℕ) : col2 (r % 3) = col2 r := by
  simp [col2]

lemma col2_ne_zero (r : ℕ) : col2 r ≠ 0 := by
  rw [← col2_mod3]
  have hlt : r % 3 < 3 := Nat.mod_lt _ (by decide)
  interval_cases (r % 3) <;> decide

lemma col2_consec_li (r : ℕ) : LinearIndependent F2 ![col2 r, col2 (r + 1)] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h0 : g 0 • col2 (r % 3) + g 1 • col2 ((r + 1) % 3) = 0 := by
    simpa [Fin.sum_univ_two, col2_mod3] using hg
  have hlt : r % 3 < 3 := Nat.mod_lt _ (by decide)
  have hr : (r + 1) % 3 = (r % 3 + 1) % 3 := by omega
  rw [hr] at h0
  rcases zmod2_cases (g 0) with h00 | h01 <;> rcases zmod2_cases (g 1) with h10 | h11
  · fin_cases i <;> assumption
  · rw [h00, h11, zero_smul, one_smul, zero_add] at h0
    exact (col2_ne_zero _ h0).elim
  · rw [h01, h10, one_smul, zero_smul, add_zero] at h0
    exact (col2_ne_zero _ h0).elim
  · rw [h01, h11, one_smul, one_smul] at h0
    exfalso
    interval_cases (r % 3) <;> revert h0 <;> decide

lemma span_col2_consec (r : ℕ) : Submodule.span F2 {col2 r, col2 (r + 1)} = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  have hset : ({col2 r, col2 (r + 1)} : Set V2) = Set.range ![col2 r, col2 (r + 1)] := by
    ext x; simp [Fin.exists_fin_two, or_comm]
  rw [hset, finrank_span_eq_card (col2_consec_li r)]
  simp [Module.finrank_fin_fun]

lemma col2_eq_iff (r₁ r₂ : ℕ) : col2 r₁ = col2 r₂ ↔ r₁ % 3 = r₂ % 3 := by
  rw [← col2_mod3 r₁, ← col2_mod3 r₂]
  have h1 : r₁ % 3 < 3 := Nat.mod_lt _ (by decide)
  have h2 : r₂ % 3 < 3 := Nat.mod_lt _ (by decide)
  interval_cases (r₁ % 3) <;> interval_cases (r₂ % 3) <;> decide

lemma exists_col2_eq (u : V2) (hu : u ≠ 0) : ∃ c : ℕ, c < 3 ∧ col2 c = u := by
  have h0 : u 0 = 0 ∨ u 0 = 1 := zmod2_cases (u 0)
  have h1 : u 1 = 0 ∨ u 1 = 1 := zmod2_cases (u 1)
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · exfalso; apply hu; ext b; fin_cases b <;> assumption
  · refine ⟨1, by decide, ?_⟩; ext b; fin_cases b <;> simp [col2, h0, h1]
  · refine ⟨0, by decide, ?_⟩; ext b; fin_cases b <;> simp [col2, h0, h1]
  · refine ⟨2, by decide, ?_⟩; ext b; fin_cases b <;> simp [col2, h0, h1]

lemma hPat_mod6 (k : ℕ) : hPat (k % 6) = hPat k := by
  ext b
  have h1 : k % 6 % 2 = k % 2 := by omega
  have h2 : k % 6 / 2 % 3 = k / 2 % 3 := by omega
  simp [hPat, h1, h2]

lemma hVec_idx {t : ℕ} (ht : 0 < t) (k : ℕ) : hVec (idx ht k) = hPat k := by
  ext b
  simp [hVec, hPat, idx_mod2 ht k, idx_div2_mod3 ht k]

lemma hVec_eq_incEven {t : ℕ} {i : Fin (6 * t)} (he : i.val % 2 = 0) :
    hVec i = incEven (col2 (i.val / 2)) := by
  ext b
  have hq : i.val / 2 % 3 < 3 := Nat.mod_lt _ (by decide)
  fin_cases b <;> simp only [hVec, incEven, col2, he] <;> interval_cases (i.val / 2 % 3) <;> decide

lemma hVec_eq_incOdd {t : ℕ} {i : Fin (6 * t)} (ho : i.val % 2 = 1) :
    hVec i = incOdd (col2 (i.val / 2)) := by
  ext b
  have hq : i.val / 2 % 3 < 3 := Nat.mod_lt _ (by decide)
  fin_cases b <;> simp only [hVec, incOdd, col2, ho] <;> interval_cases (i.val / 2 % 3) <;> decide

lemma hPat_eq_incEven {k : ℕ} (he : k % 2 = 0) :
    hPat k = incEven (col2 (k / 2)) := by
  ext b
  have hq : k / 2 % 3 < 3 := Nat.mod_lt _ (by decide)
  fin_cases b <;> simp only [hPat, incEven, col2, he] <;> interval_cases (k / 2 % 3) <;> decide

lemma hPat_eq_incOdd {k : ℕ} (ho : k % 2 = 1) :
    hPat k = incOdd (col2 (k / 2)) := by
  ext b
  have hq : k / 2 % 3 < 3 := Nat.mod_lt _ (by decide)
  fin_cases b <;> simp only [hPat, incOdd, col2, ho] <;> interval_cases (k / 2 % 3) <;> decide

lemma hVec_ne_zero {t : ℕ} (i : Fin (6 * t)) : hVec i ≠ 0 := by
  by_cases h : i.val % 2 = 0
  · rw [hVec_eq_incEven h]
    intro hz
    exact col2_ne_zero _ (by simpa [evenProj_incEven] using congrArg evenProj hz)
  · have ho : i.val % 2 = 1 := by omega
    rw [hVec_eq_incOdd ho]
    intro hz
    exact col2_ne_zero _ (by simpa [oddProj_incOdd] using congrArg oddProj hz)

def arcSum (s m : ℕ) : V4 := ∑ j ∈ Finset.range m, hPat (s + j)

lemma sum_hPat_six (s : ℕ) : ∑ j ∈ Finset.range 6, hPat (s + j) = 0 := by
  have hstep : ∀ j, hPat (s + j) = hPat (s % 6 + j) := fun j => by
    rw [← hPat_mod6 (s + j), ← hPat_mod6 (s % 6 + j)]
    congr 1; omega
  have heq : ∑ j ∈ Finset.range 6, hPat (s + j) = ∑ j ∈ Finset.range 6, hPat (s % 6 + j) :=
    Finset.sum_congr rfl fun j _ => hstep j
  rw [heq]
  have hs : s % 6 < 6 := Nat.mod_lt _ (by decide)
  interval_cases (s % 6) <;> decide

lemma arcSum_add_six (s m : ℕ) : arcSum s (m + 6) = arcSum s m := by
  unfold arcSum
  rw [Finset.sum_range_add, show ∑ x ∈ Finset.range 6, hPat (s + (m + x)) =
      ∑ x ∈ Finset.range 6, hPat ((s + m) + x) from
    Finset.sum_congr rfl fun x _ => by rw [add_assoc], sum_hPat_six, add_zero]

lemma arcSum_mod6 (s m : ℕ) : arcSum s m = arcSum (s % 6) (m % 6) := by
  have hm : ∀ q, arcSum s (m % 6 + 6 * q) = arcSum s (m % 6) := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [show m % 6 + 6 * (q + 1) = (m % 6 + 6 * q) + 6 by ring, arcSum_add_six, ih]
  have h1 : arcSum s m = arcSum s (m % 6) := by
    conv_lhs => rw [← Nat.mod_add_div m 6, add_comm]
    rw [add_comm]
    exact hm (m / 6)
  rw [h1]
  unfold arcSum
  apply Finset.sum_congr rfl
  intro j _
  rw [← hPat_mod6 (s + j), ← hPat_mod6 (s % 6 + j)]
  congr 1; omega

lemma hSum_arc {t : ℕ} (ht : 0 < t) (s : Fin (6 * t)) {m : ℕ} (hm : m ≤ 6 * t) :
    hSum (arc ht s m) = arcSum s.val m := by
  unfold hSum arc arcSum
  rw [Finset.sum_image]
  · exact Finset.sum_congr rfl fun k _ => hVec_idx ht (s.val + k)
  · intro j₁ hj₁ j₂ hj₂ heq
    exact idx_inj_range ht s hm (Finset.mem_range.mp hj₁) (Finset.mem_range.mp hj₂) heq

lemma arcSum_eq_zero_iff (s m : ℕ) : arcSum s m = 0 ↔ m % 6 = 0 := by
  rw [arcSum_mod6]
  have hs : s % 6 < 6 := Nat.mod_lt _ (by decide)
  have hm : m % 6 < 6 := Nat.mod_lt _ (by decide)
  interval_cases (s % 6) <;> interval_cases (m % 6) <;> decide

lemma arcSum_oddProj_zero_iff (s m : ℕ) :
    oddProj (arcSum s m) = 0 ↔ m % 6 = 0 ∨ (m % 6 = 1 ∧ s % 2 = 0) ∨ (m % 6 = 5 ∧ s % 2 = 1) := by
  rw [arcSum_mod6]
  have hs : s % 6 < 6 := Nat.mod_lt _ (by decide)
  have hm : m % 6 < 6 := Nat.mod_lt _ (by decide)
  have h2 : s % 2 = s % 6 % 2 := by omega
  rw [h2]
  interval_cases (s % 6) <;> interval_cases (m % 6) <;> decide

lemma arcSum_evenProj_zero_iff (s m : ℕ) :
    evenProj (arcSum s m) = 0 ↔ m % 6 = 0 ∨ (m % 6 = 1 ∧ s % 2 = 1) ∨ (m % 6 = 5 ∧ s % 2 = 0) := by
  rw [arcSum_mod6]
  have hs : s % 6 < 6 := Nat.mod_lt _ (by decide)
  have hm : m % 6 < 6 := Nat.mod_lt _ (by decide)
  have h2 : s % 2 = s % 6 % 2 := by omega
  rw [h2]
  interval_cases (s % 6) <;> interval_cases (m % 6) <;> decide

lemma arcSum_two (s : ℕ) :
    arcSum s 2 = hPat s + hPat (s + 1) := by
  simp [arcSum, Finset.sum_range_succ]

lemma arcSum_three (s : ℕ) :
    arcSum s 3 = hPat s + hPat (s + 1) + hPat (s + 2) := by
  simp [arcSum, Finset.sum_range_succ]

lemma card_lane_col_eq {t : ℕ} (ht : 0 < t) (p : ℕ) (hp : p < 2) (u : V2) (hu : u ≠ 0) :
    (Finset.univ.filter (fun i : Fin (6 * t) => i.val % 2 = p ∧ col2 (i.val / 2) = u)).card = t := by
  obtain ⟨c, hc, rfl⟩ := exists_col2_eq u hu
  let f : Fin t → Fin (6 * t) := fun q => ⟨6 * q.val + 2 * c + p, by have := q.isLt; omega⟩
  have hset : Finset.univ.filter (fun i : Fin (6 * t) => i.val % 2 = p ∧ col2 (i.val / 2) = col2 c) =
      Finset.univ.image f := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, col2_eq_iff]
    constructor
    · rintro ⟨hp', hc'⟩
      refine ⟨⟨i.val / 6, by have := i.isLt; omega⟩, ?_⟩
      apply Fin.ext
      dsimp [f]
      have : c % 3 = c := Nat.mod_eq_of_lt hc
      omega
    · rintro ⟨q, rfl⟩
      dsimp [f]
      have : c % 3 = c := Nat.mod_eq_of_lt hc
      omega
  rw [hset, Finset.card_image_of_injective]
  · simp
  · intro q₁ q₂ h
    have hv := congrArg Fin.val h
    dsimp [f] at hv
    exact Fin.ext (by omega)

lemma card_six_window_hits {t : ℕ} (ht : 0 < t) (s : Fin (6 * t))
    (we wo : V2) (hwe : we ≠ 0) (hwo : wo ≠ 0) :
    ((arc ht s 6).filter (fun i : Fin (6 * t) =>
      (i.val % 2 = 0 ∧ col2 (i.val / 2) = we) ∨ (i.val % 2 = 1 ∧ col2 (i.val / 2) = wo))).card = 2 := by
  obtain ⟨ce, hce, rfl⟩ := exists_col2_eq we hwe
  obtain ⟨co, hco, rfl⟩ := exists_col2_eq wo hwo
  let re := (2 * ce + 6 - s.val % 6) % 6
  let ro := (2 * co + 1 + 6 - s.val % 6) % 6
  have hre : re < 6 := Nat.mod_lt _ (by decide)
  have hro : ro < 6 := Nat.mod_lt _ (by decide)
  have hne : re ≠ ro := by omega
  let xe := idx ht (s.val + re)
  let xo := idx ht (s.val + ro)
  have hxne : xe ≠ xo := fun h => hne (idx_inj_range ht s (by omega) hre hro h)
  have hsub : (arc ht s 6).filter (fun i : Fin (6 * t) =>
      (i.val % 2 = 0 ∧ col2 (i.val / 2) = col2 ce) ∨
      (i.val % 2 = 1 ∧ col2 (i.val / 2) = col2 co)) = {xe, xo} := by
    ext x
    simp only [Finset.mem_filter, mem_arc_iff, Finset.mem_insert, Finset.mem_singleton, col2_eq_iff]
    constructor
    · rintro ⟨⟨k, hk, rfl⟩, hcond⟩
      simp only [idx_mod2, idx_div2_mod3] at hcond
      rcases hcond with ⟨hp, hc⟩ | ⟨hp, hc⟩
      · left; congr 1
        have : ce % 3 = ce := Nat.mod_eq_of_lt hce
        have : k = re := by dsimp [re]; omega
        rw [this]
      · right; congr 1
        have : co % 3 = co := Nat.mod_eq_of_lt hco
        have : k = ro := by dsimp [ro]; omega
        rw [this]
    · rintro (rfl | rfl)
      · refine ⟨⟨re, hre, rfl⟩, Or.inl ?_⟩
        rw [idx_mod2, idx_div2_mod3]
        have : ce % 3 = ce := Nat.mod_eq_of_lt hce
        dsimp [re]; omega
      · refine ⟨⟨ro, hro, rfl⟩, Or.inr ?_⟩
        rw [idx_mod2, idx_div2_mod3]
        have : co % 3 = co := Nat.mod_eq_of_lt hco
        dsimp [ro]; omega
  rw [hsub, Finset.card_pair hxne]

end Columns

section RunKernel

variable {t : ℕ} (ht : 0 < t)

abbrev W (t : ℕ) := Fin (6 * t) → F2

def goodU (U : Submodule F2 (W t)) : Prop :=
  (∀ x ∈ U, ∀ b : Fin 4, (∑ i, hVec i b * x i) = 0) ∧
  (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (nxt ht i) = x (nxt ht i) * y i)

noncomputable def suppU (U : Submodule F2 (W t)) : Finset (Fin (6 * t)) :=
  Finset.univ.filter (fun i => ∃ x ∈ U, x i ≠ 0)

def sitesOf (S : Finset (Fin (6 * t))) (p : ℕ) : ℕ :=
  (S.filter (fun i => i.val % 2 = p)).card

noncomputable def hSpace (S : Finset (Fin (6 * t))) : Submodule F2 V4 :=
  Submodule.span F2 (↑((pcs (nxt ht) S).image hSum) : Set V4)

noncomputable def rk (S : Finset (Fin (6 * t))) : ℕ :=
  Module.finrank F2 (hSpace ht S)

lemma mem_hSpace {S : Finset (Fin (6 * t))} {C : Finset (Fin (6 * t))}
    (hC : C ∈ pcs (nxt ht) S) : hSum C ∈ hSpace ht S :=
  Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem hSum hC))

lemma zero_of_not_mem_supp {U : Submodule F2 (W t)} {x : W t} (hx : x ∈ U)
    {i : Fin (6 * t)} (hi : i ∉ suppU U) : x i = 0 := by
  by_contra hne
  exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, hne⟩)

lemma const_on_adj {U : Submodule F2 (W t)} (hg : goodU ht U)
    {i : Fin (6 * t)} (hi : i ∈ suppU U) (hni : nxt ht i ∈ suppU U)
    {x : W t} (hx : x ∈ U) : x i = x (nxt ht i) := by
  obtain ⟨u, hu, hui⟩ := (Finset.mem_filter.mp hi).2
  obtain ⟨v, hv, hvni⟩ := (Finset.mem_filter.mp hni).2
  have hui1 : u i = 1 := (zmod2_ne_zero_iff _).mp hui
  have hvni1 : v (nxt ht i) = 1 := (zmod2_ne_zero_iff _).mp hvni
  have hw : ∃ w ∈ U, w i = 1 ∧ w (nxt ht i) = 1 := by
    rcases zmod2_cases (u (nxt ht i)) with hu0 | hu1
    · rcases zmod2_cases (v i) with hv0 | hv1
      · refine ⟨u + v, U.add_mem hu hv, ?_, ?_⟩
        · simp [hui1, hv0]
        · simp [hu0, hvni1]
      · exact ⟨v, hv, hv1, hvni1⟩
    · exact ⟨u, hu, hui1, hu1⟩
  obtain ⟨w, hwU, hwi, hwni⟩ := hw
  have hmul := hg.2 x hx w hwU i
  simpa [hwi, hwni] using hmul

lemma const_on_edge {U : Submodule F2 (W t)} (hg : goodU ht U)
    {i j : Fin (6 * t)} (he : edge (nxt ht) (suppU U) i j)
    {x : W t} (hx : x ∈ U) : x i = x j := by
  rcases he.2.2 with rfl | rfl
  · exact const_on_adj ht hg he.1 he.2.1 hx
  · exact (const_on_adj ht hg he.2.1 he.1 hx).symm

lemma const_on_comp {U : Submodule F2 (W t)} (hg : goodU ht U)
    {C : Finset (Fin (6 * t))} (hC : C ∈ pcs (nxt ht) (suppU U))
    {i j : Fin (6 * t)} (hi : i ∈ C) (hj : j ∈ C)
    {x : W t} (hx : x ∈ U) : x i = x j := by
  obtain ⟨_, hci⟩ := center (nxt ht) (suppU U) hC hi
  rw [← hci] at hj
  obtain ⟨hjS, hpath⟩ := Finset.mem_filter.mp hj
  clear hj hjS
  induction hpath with
  | refl => rfl
  | tail _ he ih => exact ih.trans (const_on_edge ht hg he hx)

lemma finrank_le_one_of_supp_univ {U : Submodule F2 (W t)} (hg : goodU ht U)
    (huniv : suppU U = Finset.univ) : Module.finrank F2 U ≤ 1 := by
  let ones : W t := fun _ => 1
  have hle : U ≤ Submodule.span F2 {ones} := by
    intro x hx
    have hconst : ∀ i : Fin (6 * t), x i = x ⟨0, by omega⟩ := by
      intro i
      have go (k : ℕ) : x (idx ht k) = x ⟨0, by omega⟩ := by
        induction k with
        | zero =>
          have : idx ht 0 = ⟨0, by omega⟩ := by apply Fin.ext; simp [idx]
          rw [this]
        | succ k ih =>
          have h1 : idx ht k ∈ suppU U := huniv.symm ▸ Finset.mem_univ _
          have h2 : nxt ht (idx ht k) ∈ suppU U := huniv.symm ▸ Finset.mem_univ _
          have hc := const_on_adj ht hg h1 h2 hx
          rw [nxt_idx] at hc
          exact hc.symm.trans ih
      simpa [idx_self] using go i.val
    rw [Submodule.mem_span_singleton]
    refine ⟨x ⟨0, by omega⟩, ?_⟩
    ext i
    simp [ones, hconst i]
  have hm := Submodule.finrank_mono hle
  have h1 : ones ≠ 0 := by
    intro h
    have := congrFun h ⟨0, by omega⟩
    simp [ones] at this
  rwa [finrank_span_singleton h1] at hm

lemma finrank_add_rk_le_runs {U : Submodule F2 (W t)} (hg : goodU ht U) :
    Module.finrank F2 U + rk ht (suppU U) ≤ (pcs (nxt ht) (suppU U)).card := by
  set S := suppU U
  set P := pcs (nxt ht) S
  let rep : ↥P → Fin (6 * t) := fun C => Classical.choose (populated (nxt ht) S C.2)
  have hrep : ∀ C : ↥P, rep C ∈ C.1 := fun C => Classical.choose_spec (populated (nxt ht) S C.2)
  let ρ : U →ₗ[F2] (↥P → F2) :=
    { toFun := fun x C => x.1 (rep C)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hρ_inj : Function.Injective ρ := by
    intro x y hxy
    apply Subtype.ext
    ext i
    by_cases hi : i ∈ S
    · let C : ↥P := ⟨cc (nxt ht) S i, Finset.mem_image_of_mem _ hi⟩
      have hiC : i ∈ C.1 := selfMem (nxt ht) S hi
      have h1 := const_on_comp ht hg C.2 hiC (hrep C) x.2
      have h2 := const_on_comp ht hg C.2 hiC (hrep C) y.2
      have h3 := congrFun hxy C
      exact h1.trans (h3.trans h2.symm)
    · rw [zero_of_not_mem_supp x.2 hi, zero_of_not_mem_supp y.2 hi]
  let Φ : (↥P → F2) →ₗ[F2] V4 :=
    { toFun := fun c => ∑ C : ↥P, c C • hSum C.1
      map_add' := fun c d => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun a c => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  have hker : LinearMap.range ρ ≤ LinearMap.ker Φ := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    ext b
    dsimp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, ρ, Pi.zero_apply]
    rw [Finset.sum_apply]
    have hsum1 : (∑ C : ↥P, (x.1 (rep C) • hSum C.1) b) =
        ∑ C ∈ P, ∑ i ∈ id C, hVec i b * x.1 i := by
      rw [← Finset.sum_coe_sort P (fun C => ∑ i ∈ id C, hVec i b * x.1 i)]
      apply Finset.sum_congr rfl
      intro C _
      simp only [id_eq, Pi.smul_apply, smul_eq_mul, hSum, Finset.sum_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [const_on_comp ht hg C.2 hi (hrep C) x.2, mul_comm]
    rw [hsum1, ← Finset.sum_biUnion (pcs_pairwiseDisjoint (nxt ht) S), pcs_biUnion_eq]
    have hsum2 : (∑ i ∈ S, hVec i b * x.1 i) = ∑ i : Fin (6 * t), hVec i b * x.1 i := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro i _ hi
      rw [zero_of_not_mem_supp x.2 hi, mul_zero]
    rw [hsum2]
    exact hg.1 x.1 x.2 b
  have hrange : LinearMap.range Φ = hSpace ht S := by
    apply le_antisymm
    · rintro _ ⟨c, rfl⟩
      dsimp only [Φ, LinearMap.coe_mk, AddHom.coe_mk]
      apply Submodule.sum_mem
      intro C _
      exact Submodule.smul_mem _ _ (mem_hSpace ht C.2)
    · apply Submodule.span_le.mpr
      intro v hv
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hv)
      refine ⟨Pi.single ⟨C, hC⟩ 1, ?_⟩
      dsimp only [Φ, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Finset.sum_eq_single (⟨C, hC⟩ : ↥P)]
      · simp
      · intro D _ hne
        simp [Pi.single_eq_of_ne hne]
      · intro h; exact (h (Finset.mem_univ _)).elim
  have h1 : Module.finrank F2 U = Module.finrank F2 (LinearMap.range ρ) :=
    (LinearMap.finrank_range_of_inj hρ_inj).symm
  have h2 : Module.finrank F2 (LinearMap.range ρ) ≤ Module.finrank F2 (LinearMap.ker Φ) :=
    Submodule.finrank_mono hker
  have h3 := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hrange, Module.finrank_pi, Fintype.card_coe] at h3
  change rk ht S + Module.finrank F2 (LinearMap.ker Φ) = P.card at h3
  omega

lemma active_run {U : Submodule F2 (W t)} (hg : goodU ht U)
    {C : Finset (Fin (6 * t))} (hC : C ∈ pcs (nxt ht) (suppU U)) :
    hSum C ∈ Submodule.span F2 (↑(((pcs (nxt ht) (suppU U)).erase C).image hSum) : Set V4) := by
  set S := suppU U
  set P := pcs (nxt ht) S
  obtain ⟨i0, hi0C⟩ := populated (nxt ht) S hC
  have hi0S : i0 ∈ S := (center (nxt ht) S hC hi0C).1
  obtain ⟨x, hxU, hxi0⟩ := (Finset.mem_filter.mp hi0S).2
  have hxi01 : x i0 = 1 := (zmod2_ne_zero_iff _).mp hxi0
  let rep : Finset (Fin (6 * t)) → Fin (6 * t) := fun D =>
    if hD : D ∈ P then Classical.choose (populated (nxt ht) S hD) else i0
  have hrep : ∀ D, ∀ hD : D ∈ P, rep D ∈ D := fun D hD => by
    simp only [rep, dif_pos hD]
    exact Classical.choose_spec (populated (nxt ht) S hD)
  have htot : ∑ D ∈ P, x (rep D) • hSum D = 0 := by
    ext b
    rw [Finset.sum_apply, Pi.zero_apply]
    have h1 : (∑ D ∈ P, (x (rep D) • hSum D) b) = ∑ D ∈ P, ∑ i ∈ id D, hVec i b * x i := by
      apply Finset.sum_congr rfl
      intro D hD
      simp only [id_eq, Pi.smul_apply, smul_eq_mul, hSum, Finset.sum_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [const_on_comp ht hg hD hi (hrep D hD) hxU, mul_comm]
    rw [h1, ← Finset.sum_biUnion (pcs_pairwiseDisjoint (nxt ht) S), pcs_biUnion_eq]
    have h2 : (∑ i ∈ S, hVec i b * x i) = ∑ i : Fin (6 * t), hVec i b * x i := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro i _ hi
      rw [zero_of_not_mem_supp hxU hi, mul_zero]
    rw [h2]
    exact hg.1 x hxU b
  have hsplit := Finset.add_sum_erase P (fun D => x (rep D) • hSum D) hC
  rw [htot] at hsplit
  have hxC : x (rep C) = 1 :=
    (const_on_comp ht hg hC (hrep C hC) hi0C hxU).trans hxi01
  rw [hxC, one_smul] at hsplit
  have heq : hSum C = ∑ D ∈ P.erase C, x (rep D) • hSum D := by
    have hadd := congrArg (fun v => v + hSum C) hsplit
    simp only [zero_add] at hadd
    rw [add_comm (hSum C), add_assoc, v4_add_self, add_zero] at hadd
    exact hadd.symm
  rw [heq]
  apply Submodule.sum_mem
  intro D hD
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem hSum hD)))

lemma active_proj {U : Submodule F2 (W t)} (hg : goodU ht U)
    (proj : V4 →ₗ[F2] V2) {C : Finset (Fin (6 * t))} (hC : C ∈ pcs (nxt ht) (suppU U))
    (hne : proj (hSum C) ≠ 0) :
    ∃ D ∈ pcs (nxt ht) (suppU U), D ≠ C ∧ proj (hSum D) ≠ 0 := by
  by_contra! hall
  have hle : Submodule.span F2 (↑(((pcs (nxt ht) (suppU U)).erase C).image hSum) : Set V4) ≤
      LinearMap.ker proj := by
    apply Submodule.span_le.mpr
    intro v hv
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hv)
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    exact hall D (Finset.mem_of_mem_erase hD) (Finset.ne_of_mem_erase hD)
  exact hne (hle (active_run ht hg hC))

end RunKernel

section UpperBounds

variable {t : ℕ} (ht : 0 < t)

lemma submodule_le_one_eq_zero_or_w {M : Type*} [AddCommGroup M] [Module F2 M]
    [FiniteDimensional F2 M] {V : Submodule F2 M} (hV : Module.finrank F2 V ≤ 1) :
    ∃ w : M, ∀ v ∈ V, v = 0 ∨ v = w := by
  by_cases h0 : Module.finrank F2 V = 0
  · refine ⟨0, fun v hv => Or.inl ?_⟩
    exact congrArg Subtype.val ((finrank_zero_iff_forall_zero.mp h0) ⟨v, hv⟩)
  · have h1 : Module.finrank F2 V = 1 := by omega
    have hne : V ≠ ⊥ := by
      intro eb
      rw [eb, finrank_bot] at h1
      omega
    obtain ⟨w, hwV, hw0⟩ : ∃ w ∈ V, w ≠ 0 := by
      by_contra! hall
      exact hne ((Submodule.eq_bot_iff V).mpr hall)
    have hle : Submodule.span F2 {w} ≤ V := (Submodule.span_singleton_le_iff_mem w V).mpr hwV
    have heq : Submodule.span F2 {w} = V :=
      Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_singleton hw0, h1])
    refine ⟨w, fun v hv => ?_⟩
    rw [← heq, Submodule.mem_span_singleton] at hv
    obtain ⟨c, rfl⟩ := hv
    rcases zmod2_cases c with rfl | rfl
    · left; simp
    · right; simp

lemma rk_zero_runs {S : Finset (Fin (6 * t))} (hS : S ≠ Finset.univ)
    (hrk : rk ht S = 0) : 7 * (pcs (nxt ht) S).card ≤ 6 * t := by
  have hseven : ∀ C ∈ pcs (nxt ht) S, 7 ≤ C.card + 1 := by
    intro C hC
    obtain ⟨s, _, _, harc, hpos, hlt, _⟩ := comp_arc ht hS hC
    have hz : hSum C = 0 := congrArg Subtype.val
      ((finrank_zero_iff_forall_zero.mp hrk) ⟨hSum C, mem_hSpace ht hC⟩)
    rw [harc, hSum_arc ht s (by omega), arcSum_eq_zero_iff] at hz
    omega
  have hsum := Finset.sum_le_sum hseven
  simp only [Finset.sum_const, smul_eq_mul] at hsum
  have hle := sum_halo_le ht hS
  omega

lemma rk_le_one_runs {S : Finset (Fin (6 * t))} (hS : S ≠ Finset.univ)
    (hrk : rk ht S ≤ 1) : (pcs (nxt ht) S).card < 2 * t := by
  obtain ⟨w, hw⟩ := submodule_le_one_eq_zero_or_w hrk
  set P := pcs (nxt ht) S
  by_cases hwe : evenProj w = 0
  · by_cases hwo : oddProj w = 0
    · have hw0 : w = 0 := (v4_eq_zero_iff w).mpr ⟨hwe, hwo⟩
      have hrk0 : rk ht S = 0 := by
        rw [rk, finrank_zero_iff_forall_zero]
        intro ⟨v, hv⟩
        apply Subtype.ext
        rcases hw v hv with h | h
        · exact h
        · exact h.trans hw0
      have h7 : 7 * P.card ≤ 6 * t := rk_zero_runs ht hS hrk0
      omega
    · let P1 := P.filter (fun C => C.card = 1)
      let P2 := P.filter (fun C => 2 ≤ C.card)
      have hdis : Disjoint P1 P2 := Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega
      have hun : P1 ∪ P2 = P := by
        ext C; simp only [P1, P2, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨hC, _⟩ | ⟨hC, _⟩); exact hC; exact hC
        · intro hC
          have hpos := Finset.card_pos.mpr (populated (nxt ht) S hC)
          by_cases hc1 : C.card = 1
          · exact Or.inl ⟨hC, hc1⟩
          · exact Or.inr ⟨hC, by omega⟩
      have hpart : P1.card + P2.card = P.card := by
        rw [← Finset.card_union_of_disjoint hdis, hun]
      have hP1 : P1.card ≤ t := by
        let T := Finset.univ.filter (fun i : Fin (6 * t) => i.val % 2 = 1 ∧ col2 (i.val / 2) = oddProj w)
        have hT : T.card = t := card_lane_col_eq ht 1 (by decide) (oddProj w) hwo
        have hsub : P1.biUnion id ⊆ T := by
          intro i hi
          obtain ⟨C, hC1, hiC⟩ := Finset.mem_biUnion.mp hi
          obtain ⟨hCP, hcard1⟩ := Finset.mem_filter.mp hC1
          have hCeq : C = {i} := Finset.eq_singleton_iff_unique_mem.mpr
            ⟨hiC, fun j hj => Finset.card_le_one_iff.mp hcard1.le hj hiC⟩
          have hsumW : hVec i = w := by
            have hm := mem_hSpace ht hCP
            rw [hCeq, hSum, Finset.sum_singleton] at hm
            rcases hw _ hm with h0 | h1
            · exact (hVec_ne_zero i h0).elim
            · exact h1
          have hpar : i.val % 2 = 1 := by
            by_contra hne
            have he : i.val % 2 = 0 := by omega
            have := congrArg oddProj hsumW
            rw [hVec_eq_incEven he, oddProj_incEven] at this
            exact hwo this.symm
          have hcol : col2 (i.val / 2) = oddProj w := by
            have := congrArg oddProj hsumW
            rwa [hVec_eq_incOdd hpar, oddProj_incOdd] at this
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpar, hcol⟩
        have hcard_bi : (P1.biUnion id).card = P1.card := by
          rw [Finset.card_biUnion]
          · have : ∑ C ∈ P1, C.card = ∑ _ ∈ P1, 1 :=
              Finset.sum_congr rfl fun C hC => (Finset.mem_filter.mp hC).2
            simpa using this
          · intro C hC D hD hne
            exact pcs_pairwiseDisjoint (nxt ht) S (Finset.mem_filter.mp hC).1
              (Finset.mem_filter.mp hD).1 hne
        calc P1.card = (P1.biUnion id).card := hcard_bi.symm
          _ ≤ T.card := Finset.card_le_card hsub
          _ = t := hT
      have hP2 : ∀ C ∈ P2, 6 ≤ C.card + 1 := by
        intro C hC2
        obtain ⟨hCP, hge2⟩ := Finset.mem_filter.mp hC2
        obtain ⟨s, _, _, harc, _, hlt, _⟩ := comp_arc ht hS hCP
        have hev : evenProj (hSum C) = 0 := by
          rcases hw _ (mem_hSpace ht hCP) with h0 | h1
          · rw [h0, map_zero]
          · rw [h1, hwe]
        rw [harc, hSum_arc ht s (by omega), arcSum_evenProj_zero_iff] at hev
        omega
      have hsum_le : 2 * P1.card + 6 * P2.card ≤ 6 * t := by
        have h1 : 2 * P1.card ≤ ∑ C ∈ P1, (C.card + 1) := by
          have : ∑ C ∈ P1, (C.card + 1) = ∑ _ ∈ P1, 2 :=
            Finset.sum_congr rfl fun C hC => by have := (Finset.mem_filter.mp hC).2; omega
          rw [this, Finset.sum_const, smul_eq_mul]; omega
        have h2 : 6 * P2.card ≤ ∑ C ∈ P2, (C.card + 1) := by
          have := Finset.sum_le_sum hP2
          simp only [Finset.sum_const, smul_eq_mul] at this; omega
        have htot : ∑ C ∈ P, (C.card + 1) ≤ 6 * t := sum_halo_le ht hS
        rw [← hun, Finset.sum_union hdis] at htot
        omega
      omega
  · by_cases hwo : oddProj w = 0
    · let P1 := P.filter (fun C => C.card = 1)
      let P2 := P.filter (fun C => 2 ≤ C.card)
      have hdis : Disjoint P1 P2 := Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega
      have hun : P1 ∪ P2 = P := by
        ext C; simp only [P1, P2, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨hC, _⟩ | ⟨hC, _⟩); exact hC; exact hC
        · intro hC
          have hpos := Finset.card_pos.mpr (populated (nxt ht) S hC)
          by_cases hc1 : C.card = 1
          · exact Or.inl ⟨hC, hc1⟩
          · exact Or.inr ⟨hC, by omega⟩
      have hpart : P1.card + P2.card = P.card := by
        rw [← Finset.card_union_of_disjoint hdis, hun]
      have hP1 : P1.card ≤ t := by
        let T := Finset.univ.filter (fun i : Fin (6 * t) => i.val % 2 = 0 ∧ col2 (i.val / 2) = evenProj w)
        have hT : T.card = t := card_lane_col_eq ht 0 (by decide) (evenProj w) hwe
        have hsub : P1.biUnion id ⊆ T := by
          intro i hi
          obtain ⟨C, hC1, hiC⟩ := Finset.mem_biUnion.mp hi
          obtain ⟨hCP, hcard1⟩ := Finset.mem_filter.mp hC1
          have hCeq : C = {i} := Finset.eq_singleton_iff_unique_mem.mpr
            ⟨hiC, fun j hj => Finset.card_le_one_iff.mp hcard1.le hj hiC⟩
          have hsumW : hVec i = w := by
            have hm := mem_hSpace ht hCP
            rw [hCeq, hSum, Finset.sum_singleton] at hm
            rcases hw _ hm with h0 | h1
            · exact (hVec_ne_zero i h0).elim
            · exact h1
          have hpar : i.val % 2 = 0 := by
            by_contra hne
            have ho : i.val % 2 = 1 := by omega
            have := congrArg evenProj hsumW
            rw [hVec_eq_incOdd ho, evenProj_incOdd] at this
            exact hwe this.symm
          have hcol : col2 (i.val / 2) = evenProj w := by
            have := congrArg evenProj hsumW
            rwa [hVec_eq_incEven hpar, evenProj_incEven] at this
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpar, hcol⟩
        have hcard_bi : (P1.biUnion id).card = P1.card := by
          rw [Finset.card_biUnion]
          · have : ∑ C ∈ P1, C.card = ∑ _ ∈ P1, 1 :=
              Finset.sum_congr rfl fun C hC => (Finset.mem_filter.mp hC).2
            simpa using this
          · intro C hC D hD hne
            exact pcs_pairwiseDisjoint (nxt ht) S (Finset.mem_filter.mp hC).1
              (Finset.mem_filter.mp hD).1 hne
        calc P1.card = (P1.biUnion id).card := hcard_bi.symm
          _ ≤ T.card := Finset.card_le_card hsub
          _ = t := hT
      have hP2 : ∀ C ∈ P2, 6 ≤ C.card + 1 := by
        intro C hC2
        obtain ⟨hCP, hge2⟩ := Finset.mem_filter.mp hC2
        obtain ⟨s, _, _, harc, _, hlt, _⟩ := comp_arc ht hS hCP
        have hod : oddProj (hSum C) = 0 := by
          rcases hw _ (mem_hSpace ht hCP) with h0 | h1
          · rw [h0, map_zero]
          · rw [h1, hwo]
        rw [harc, hSum_arc ht s (by omega), arcSum_oddProj_zero_iff] at hod
        omega
      have hsum_le : 2 * P1.card + 6 * P2.card ≤ 6 * t := by
        have h1 : 2 * P1.card ≤ ∑ C ∈ P1, (C.card + 1) := by
          have : ∑ C ∈ P1, (C.card + 1) = ∑ _ ∈ P1, 2 :=
            Finset.sum_congr rfl fun C hC => by have := (Finset.mem_filter.mp hC).2; omega
          rw [this, Finset.sum_const, smul_eq_mul]; omega
        have h2 : 6 * P2.card ≤ ∑ C ∈ P2, (C.card + 1) := by
          have := Finset.sum_le_sum hP2
          simp only [Finset.sum_const, smul_eq_mul] at this; omega
        have htot : ∑ C ∈ P, (C.card + 1) ≤ 6 * t := sum_halo_le ht hS
        rw [← hun, Finset.sum_union hdis] at htot
        omega
      omega
    · have hno1 : ∀ C ∈ P, 2 ≤ C.card := by
        intro C hC
        have hpos := Finset.card_pos.mpr (populated (nxt ht) S hC)
        by_contra hlt2
        have h1 : C.card = 1 := by omega
        obtain ⟨i, hiC⟩ := populated (nxt ht) S hC
        have hCeq : C = {i} := Finset.eq_singleton_iff_unique_mem.mpr
          ⟨hiC, fun j hj => Finset.card_le_one_iff.mp h1.le hj hiC⟩
        have hsumW : hVec i = w := by
          have hm := mem_hSpace ht hC
          rw [hCeq, hSum, Finset.sum_singleton] at hm
          rcases hw _ hm with h0 | h1'
          · exact (hVec_ne_zero i h0).elim
          · exact h1'
        by_cases hp : i.val % 2 = 0
        · have := congrArg oddProj hsumW
          rw [hVec_eq_incEven hp, oddProj_incEven] at this
          exact hwo this.symm
        · have ho : i.val % 2 = 1 := by omega
          have := congrArg evenProj hsumW
          rw [hVec_eq_incOdd ho, evenProj_incOdd] at this
          exact hwe this.symm
      let P2 := P.filter (fun C => C.card = 2)
      let P3 := P.filter (fun C => 3 ≤ C.card)
      have hdis : Disjoint P2 P3 := Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega
      have hun : P2 ∪ P3 = P := by
        ext C; simp only [P2, P3, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨hC, _⟩ | ⟨hC, _⟩); exact hC; exact hC
        · intro hC
          have hge2 := hno1 C hC
          by_cases hc2 : C.card = 2
          · exact Or.inl ⟨hC, hc2⟩
          · exact Or.inr ⟨hC, by omega⟩
      have hpart : P2.card + P3.card = P.card := by
        rw [← Finset.card_union_of_disjoint hdis, hun]
      have hP2 : P2.card ≤ t := by
        let T := Finset.univ.filter (fun i : Fin (6 * t) => i.val % 2 = 0 ∧ col2 (i.val / 2) = evenProj w)
        have hT : T.card = t := card_lane_col_eq ht 0 (by decide) (evenProj w) hwe
        have hhit : ∀ C : ↥P2, ∃ i ∈ C.1, i ∈ T := by
          intro C
          obtain ⟨hCP, hc2⟩ := Finset.mem_filter.mp C.2
          obtain ⟨s, _, _, harc, _, hlt, _⟩ := comp_arc ht hS hCP
          have hsumW : hSum C.1 = w := by
            rcases hw _ (mem_hSpace ht hCP) with h0 | h1
            · rw [harc, hc2, hSum_arc ht s (by omega), arcSum_eq_zero_iff] at h0; omega
            · exact h1
          have hs2 : hSum C.1 = hPat s.val + hPat (s.val + 1) := by
            rw [harc, hc2, hSum_arc ht s (by omega), arcSum_two]
          by_cases hsp : s.val % 2 = 0
          · have hsp1 : (s.val + 1) % 2 = 1 := by omega
            have hev : evenProj w = col2 (s.val / 2) := by
              rw [← hsumW, hs2, hPat_eq_incEven hsp, hPat_eq_incOdd hsp1, map_add,
                evenProj_incEven, evenProj_incOdd, add_zero]
            refine ⟨idx ht (s.val + 0), ?_, ?_⟩
            · rw [harc, hc2]; exact (mem_arc_iff ht s 2 _).mpr ⟨0, by decide, rfl⟩
            · rw [add_zero, idx_self]
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsp, hev.symm⟩
          · have hsp1 : s.val % 2 = 1 := by omega
            have hsp2 : (s.val + 1) % 2 = 0 := by omega
            have hev : evenProj w = col2 ((s.val + 1) / 2) := by
              rw [← hsumW, hs2, hPat_eq_incOdd hsp1, hPat_eq_incEven hsp2, map_add,
                evenProj_incOdd, evenProj_incEven, zero_add]
            refine ⟨idx ht (s.val + 1), ?_, ?_⟩
            · rw [harc, hc2]; exact (mem_arc_iff ht s 2 _).mpr ⟨1, by decide, rfl⟩
            · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
              · rw [idx_mod2]; exact hsp2
              · rw [← col2_mod3, idx_div2_mod3, col2_mod3]; exact hev.symm
        choose f hfC hfT using hhit
        have hinj : Function.Injective (fun C : ↥P2 => (⟨f C, hfT C⟩ : ↥T)) := by
          intro C D eq
          have hfeq : f C = f D := congrArg Subtype.val eq
          by_contra hne
          have hdis' := pcs_pairwiseDisjoint (nxt ht) S
            (Finset.mem_filter.mp C.2).1 (Finset.mem_filter.mp D.2).1 (fun e => hne (Subtype.ext e))
          exact Finset.disjoint_left.mp hdis' (hfC C) (hfeq ▸ hfC D)
        have hle := Fintype.card_le_of_injective _ hinj
        simpa [hT] using hle
      have hsum_le : 3 * P2.card + 4 * P3.card ≤ 6 * t := by
        have h2 : 3 * P2.card ≤ ∑ C ∈ P2, (C.card + 1) := by
          have : ∑ C ∈ P2, (C.card + 1) = ∑ _ ∈ P2, 3 :=
            Finset.sum_congr rfl fun C hC => by have := (Finset.mem_filter.mp hC).2; omega
          rw [this, Finset.sum_const, smul_eq_mul]; omega
        have h3 : 4 * P3.card ≤ ∑ C ∈ P3, (C.card + 1) := by
          have : ∑ _ ∈ P3, 4 ≤ ∑ C ∈ P3, (C.card + 1) :=
            Finset.sum_le_sum fun C hC => by have := (Finset.mem_filter.mp hC).2; omega
          simp only [Finset.sum_const, smul_eq_mul] at this; omega
        have htot : ∑ C ∈ P, (C.card + 1) ≤ 6 * t := sum_halo_le ht hS
        rw [← hun, Finset.sum_union hdis] at htot
        omega
      omega

lemma runs_lt_a {S : Finset (Fin (6 * t))} (hS : S ≠ Finset.univ)
    (h0 : 0 < sitesOf S 0) (h1 : 0 < sitesOf S 1) : (pcs (nxt ht) S).card < 3 * t := by
  set P := pcs (nxt ht) S
  have hle : 2 * P.card ≤ 6 * t := by
    have h2 : ∑ _ ∈ P, 2 ≤ ∑ C ∈ P, (C.card + 1) :=
      Finset.sum_le_sum fun C hC => by have := Finset.card_pos.mpr (populated (nxt ht) S hC); omega
    have htot : ∑ C ∈ P, (C.card + 1) ≤ 6 * t := sum_halo_le ht hS
    simp only [Finset.sum_const, smul_eq_mul] at h2
    omega
  by_contra hge
  have heq : P.card = 3 * t := by omega
  have hsum_eq : ∑ C ∈ P, (C.card + 1) = 6 * t := by
    have h2 : 2 * P.card ≤ ∑ C ∈ P, (C.card + 1) := by
      have := Finset.sum_le_sum fun C (hC : C ∈ P) =>
        show 2 ≤ C.card + 1 by have := Finset.card_pos.mpr (populated (nxt ht) S hC); omega
      simp only [Finset.sum_const, smul_eq_mul] at this; omega
    have htot : ∑ C ∈ P, (C.card + 1) ≤ 6 * t := sum_halo_le ht hS
    omega
  have hall1 : ∀ C ∈ P, C.card = 1 := by
    intro C hC
    by_contra hne
    have hpos := Finset.card_pos.mpr (populated (nxt ht) S hC)
    have hge3 : 3 ≤ C.card + 1 := by omega
    have hrest : 2 * (P.erase C).card ≤ ∑ D ∈ P.erase C, (D.card + 1) := by
      have := Finset.sum_le_sum fun D (hD : D ∈ P.erase C) =>
        show 2 ≤ D.card + 1 by
          have := Finset.card_pos.mpr (populated (nxt ht) S (Finset.mem_of_mem_erase hD)); omega
      simp only [Finset.sum_const, smul_eq_mul] at this; omega
    have hsplit := Finset.add_sum_erase P (fun D => D.card + 1) hC
    have her : (P.erase C).card = P.card - 1 := Finset.card_erase_of_mem hC
    omega
  have huniv : P.biUnion (halo (nxt ht)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_biUnion (separate (nxt ht) S (ninj ht))]
    have : ∑ C ∈ P, (halo (nxt ht) C).card = ∑ C ∈ P, (C.card + 1) :=
      Finset.sum_congr rfl fun C hC => halo_card_eq ht hS hC
    rw [this, hsum_eq, Fintype.card_fin]
  have halt : ∀ x : Fin (6 * t), x ∈ S ↔ nxt ht x ∉ S := by
    intro x
    constructor
    · intro hx hnx
      let C := cc (nxt ht) S x
      have hCP : C ∈ P := Finset.mem_image_of_mem _ hx
      have hxC : x ∈ C := selfMem (nxt ht) S hx
      have hnxC : nxt ht x ∈ C := Finset.mem_filter.mpr ⟨hnx, .single ⟨hx, hnx, Or.inl rfl⟩⟩
      have hne : x ≠ nxt ht x := by
        intro eq
        have hp := nxt_parity ht x
        rw [← eq] at hp; omega
      have h2 : 2 ≤ C.card := by
        calc 2 = ({x, nxt ht x} : Finset _).card := (Finset.card_pair hne).symm
          _ ≤ C.card := Finset.card_le_card (Finset.insert_subset hxC (Finset.singleton_subset_iff.mpr hnxC))
      have := hall1 C hCP
      omega
    · intro hnx
      have hmem : nxt ht x ∈ P.biUnion (halo (nxt ht)) := huniv.symm ▸ Finset.mem_univ _
      rw [mem_biUnion_halo_iff, prv_nxt] at hmem
      rcases hmem with h | h
      · exact (hnx h).elim
      · exact h
  obtain ⟨i0, hi0⟩ := Finset.card_pos.mp h0
  obtain ⟨hi0S, hi0p⟩ := Finset.mem_filter.mp hi0
  obtain ⟨i1, hi1⟩ := Finset.card_pos.mp h1
  obtain ⟨hi1S, hi1p⟩ := Finset.mem_filter.mp hi1
  have go (k : ℕ) : idx ht (i0.val + k) ∈ S ↔ k % 2 = 0 := by
    induction k with
    | zero =>
      rw [add_zero, idx_self]
      simp [hi0S]
    | succ k ih =>
      rw [← add_assoc, ← nxt_idx]
      have hstep := halt (idx ht (i0.val + k))
      constructor
      · intro h'; have hnot := hstep.not.mpr (not_not.mpr h'); have := ih.not.mp hnot; omega
      · intro h'; exact hstep.not.mp (ih.not.mpr (by omega)) |> of_not_not
  let k := 6 * t - i0.val + i1.val
  have heqi1 : idx ht (i0.val + k) = i1 := by
    apply Fin.ext
    change (i0.val + (6 * t - i0.val + i1.val)) % (6 * t) = i1.val
    have : i0.val + (6 * t - i0.val + i1.val) = i1.val + 6 * t := by have := i0.isLt; omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt i1.isLt]
  have hk := (go k).mp (heqi1.symm ▸ hi1S)
  dsimp only [k] at hk
  have := i0.isLt
  omega

lemma range_incEven_le_of_consec {V : Submodule F2 V4} {r : ℕ}
    (h1 : incEven (col2 r) ∈ V) (h2 : incEven (col2 (r + 1)) ∈ V) :
    LinearMap.range incEven ≤ V := by
  rintro _ ⟨u, rfl⟩
  have hu : u ∈ Submodule.span F2 {col2 r, col2 (r + 1)} := by
    rw [span_col2_consec]; trivial
  have hle : Submodule.span F2 {col2 r, col2 (r + 1)} ≤ V.comap incEven := by
    apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact h1
    · exact h2
  exact hle hu

lemma range_incOdd_le_of_consec {V : Submodule F2 V4} {r : ℕ}
    (h1 : incOdd (col2 r) ∈ V) (h2 : incOdd (col2 (r + 1)) ∈ V) :
    LinearMap.range incOdd ≤ V := by
  rintro _ ⟨u, rfl⟩
  have hu : u ∈ Submodule.span F2 {col2 r, col2 (r + 1)} := by
    rw [span_col2_consec]; trivial
  have hle : Submodule.span F2 {col2 r, col2 (r + 1)} ≤ V.comap incOdd := by
    apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact h1
    · exact h2
  exact hle hu

lemma range_incOdd_le_of_even_and_consec {V : Submodule F2 V4}
    (hev : LinearMap.range incEven ≤ V) {v₁ v₂ : V4} (hv1 : v₁ ∈ V) (hv2 : v₂ ∈ V) {r : ℕ}
    (ho1 : oddProj v₁ = col2 r) (ho2 : oddProj v₂ = col2 (r + 1)) :
    LinearMap.range incOdd ≤ V := by
  have hsub : ∀ v : V4, incOdd (oddProj v) = v + incEven (evenProj v) := fun v => by
    ext b; fin_cases b <;> simp [incEven, incOdd, evenProj, oddProj, CharTwo.add_self_eq_zero]
  have h1 : incOdd (col2 r) ∈ V := by
    rw [← ho1, hsub v₁]
    exact V.add_mem hv1 (hev (LinearMap.mem_range_self incEven _))
  have h2 : incOdd (col2 (r + 1)) ∈ V := by
    rw [← ho2, hsub v₂]
    exact V.add_mem hv2 (hev (LinearMap.mem_range_self incEven _))
  exact range_incOdd_le_of_consec h1 h2

lemma range_incEven_le_of_odd_and_consec {V : Submodule F2 V4}
    (hod : LinearMap.range incOdd ≤ V) {v₁ v₂ : V4} (hv1 : v₁ ∈ V) (hv2 : v₂ ∈ V) {r : ℕ}
    (he1 : evenProj v₁ = col2 r) (he2 : evenProj v₂ = col2 (r + 1)) :
    LinearMap.range incEven ≤ V := by
  have hsub : ∀ v : V4, incEven (evenProj v) = v + incOdd (oddProj v) := fun v => by
    ext b; fin_cases b <;> simp [incEven, incOdd, evenProj, oddProj, CharTwo.add_self_eq_zero]
  have h1 : incEven (col2 r) ∈ V := by
    rw [← he1, hsub v₁]
    exact V.add_mem hv1 (hod (LinearMap.mem_range_self incOdd _))
  have h2 : incEven (col2 (r + 1)) ∈ V := by
    rw [← he2, hsub v₂]
    exact V.add_mem hv2 (hod (LinearMap.mem_range_self incOdd _))
  exact range_incEven_le_of_consec h1 h2

lemma finrank_eq_four_of_both_lanes {V : Submodule F2 V4}
    (hev : LinearMap.range incEven ≤ V) (hod : LinearMap.range incOdd ≤ V) :
    Module.finrank F2 V = 4 := by
  have htop : V = ⊤ := by
    rw [eq_top_iff, ← range_incEven_sup_incOdd]
    exact sup_le hev hod
  rw [htop, finrank_top, Module.finrank_fin_fun]

lemma solo_mem_hSpace {S : Finset (Fin (6 * t))} {x : Fin (6 * t)}
    (hx : x ∈ S) (hp : prv ht x ∉ S) (hn : nxt ht x ∉ S) :
    ({x} : Finset (Fin (6 * t))) ∈ pcs (nxt ht) S ∧ hVec x ∈ hSpace ht S := by
  have hcc : cc (nxt ht) S x = {x} := by
    ext y
    simp only [cc, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hyS, hpath⟩
      clear hyS
      induction hpath with
      | refl => rfl
      | @tail a b _ he ih =>
        rw [ih] at he
        rcases he.2.2 with hf | hb
        · exact (hn (hf ▸ he.2.1)).elim
        · have hb' : b = prv ht x := by rw [← hb, prv_nxt]
          exact (hp (hb' ▸ he.2.1)).elim
    · rintro rfl
      exact ⟨hx, .refl⟩
  have hmem : ({x} : Finset (Fin (6 * t))) ∈ pcs (nxt ht) S := by
    rw [← hcc]
    exact Finset.mem_image_of_mem _ hx
  have hsp := mem_hSpace ht hmem
  rw [hSum, Finset.sum_singleton] at hsp
  exact ⟨hmem, hsp⟩

lemma span_of_consec_solos {S : Finset (Fin (6 * t))} (b k : ℕ) (hk : 2 ≤ k)
    (hmem : ∀ j < k, hVec (idx ht (b + 2 * j)) ∈ hSpace ht S) :
    (b % 2 = 0 → LinearMap.range incEven ≤ hSpace ht S) ∧
    (b % 2 = 1 → LinearMap.range incOdd ≤ hSpace ht S) := by
  have hm0 := hmem 0 (by omega)
  have hm1 := hmem 1 (by omega)
  constructor
  · intro he
    have hp0 : (idx ht (b + 2 * 0)).val % 2 = 0 := by rw [idx_mod2]; omega
    have hp1 : (idx ht (b + 2 * 1)).val % 2 = 0 := by rw [idx_mod2]; omega
    rw [hVec_eq_incEven hp0, ← col2_mod3, idx_div2_mod3, col2_mod3] at hm0
    rw [hVec_eq_incEven hp1, ← col2_mod3, idx_div2_mod3, col2_mod3] at hm1
    have eq1 : (b + 2 * 1) / 2 = (b + 2 * 0) / 2 + 1 := by omega
    rw [eq1] at hm1
    exact range_incEven_le_of_consec hm0 hm1
  · intro ho
    have hp0 : (idx ht (b + 2 * 0)).val % 2 = 1 := by rw [idx_mod2]; omega
    have hp1 : (idx ht (b + 2 * 1)).val % 2 = 1 := by rw [idx_mod2]; omega
    rw [hVec_eq_incOdd hp0, ← col2_mod3, idx_div2_mod3, col2_mod3] at hm0
    rw [hVec_eq_incOdd hp1, ← col2_mod3, idx_div2_mod3, col2_mod3] at hm1
    have eq1 : (b + 2 * 1) / 2 = (b + 2 * 0) / 2 + 1 := by omega
    rw [eq1] at hm1
    exact range_incOdd_le_of_consec hm0 hm1

lemma runs_sub1_two_gaps {U : Submodule F2 (W t)} (hg : goodU ht U)
    (h0 : 0 < sitesOf (suppU U) 0) (h1 : 0 < sitesOf (suppU U) 1)
    {a1 a2 : Fin (6 * t)} {k1 k2 : ℕ}
    (hpar : a2.val % 2 = (a1.val + 1) % 2)
    (hsolo1 : ∀ k < k1, ({idx ht (a1.val + 1 + 2 * k)} : Finset (Fin (6 * t))) ∈ pcs (nxt ht) (suppU U) ∧
      hVec (idx ht (a1.val + 1 + 2 * k)) ∈ hSpace ht (suppU U))
    (hsolo2 : ∀ k < k2, ({idx ht (a2.val + 1 + 2 * k)} : Finset (Fin (6 * t))) ∈ pcs (nxt ht) (suppU U) ∧
      hVec (idx ht (a2.val + 1 + 2 * k)) ∈ hSpace ht (suppU U))
    (hdecomp : ∀ C ∈ pcs (nxt ht) (suppU U),
      (∃ k < k1, C = {idx ht (a1.val + 1 + 2 * k)}) ∨
      (∃ k < k2, C = {idx ht (a2.val + 1 + 2 * k)})) :
    LinearMap.range incEven ≤ hSpace ht (suppU U) ∧ LinearMap.range incOdd ≤ hSpace ht (suppU U) := by
  have hge2 : ∀ (x y : Fin (6 * t)) (kx ky : ℕ),
      y.val % 2 = (x.val + 1) % 2 →
      (∀ k < kx, ({idx ht (x.val + 1 + 2 * k)} : Finset (Fin (6 * t))) ∈ pcs (nxt ht) (suppU U)) →
      (∀ C ∈ pcs (nxt ht) (suppU U),
        (∃ k < kx, C = {idx ht (x.val + 1 + 2 * k)}) ∨
        (∃ k < ky, C = {idx ht (y.val + 1 + 2 * k)})) →
      2 ≤ kx := by
    intro x y kx ky hxy hsx hdec
    by_contra hlt2
    have h01 : kx = 0 ∨ kx = 1 := by omega
    rcases h01 with rfl | rfl
    · by_cases hp : (x.val + 1) % 2 = 0
      · obtain ⟨i, hi⟩ := Finset.card_pos.mp h0
        obtain ⟨hiS, hip⟩ := Finset.mem_filter.mp hi
        rcases hdec _ (Finset.mem_image_of_mem _ hiS) with ⟨k, hk, _⟩ | ⟨k, _, hceq⟩
        · omega
        · have hiin : i ∈ ({idx ht (y.val + 1 + 2 * k)} : Finset _) :=
            hceq ▸ selfMem (nxt ht) (suppU U) hiS
          rw [Finset.mem_singleton] at hiin
          have := congrArg (fun z : Fin (6 * t) => z.val % 2) hiin
          rw [idx_mod2] at this; omega
      · obtain ⟨i, hi⟩ := Finset.card_pos.mp h1
        obtain ⟨hiS, hip⟩ := Finset.mem_filter.mp hi
        rcases hdec _ (Finset.mem_image_of_mem _ hiS) with ⟨k, hk, _⟩ | ⟨k, _, hceq⟩
        · omega
        · have hiin : i ∈ ({idx ht (y.val + 1 + 2 * k)} : Finset _) :=
            hceq ▸ selfMem (nxt ht) (suppU U) hiS
          rw [Finset.mem_singleton] at hiin
          have := congrArg (fun z : Fin (6 * t) => z.val % 2) hiin
          rw [idx_mod2] at this; omega
    · let x0 := idx ht (x.val + 1 + 2 * 0)
      have hx0P := hsx 0 (by omega)
      by_cases hp : (x.val + 1) % 2 = 0
      · have hp0 : x0.val % 2 = 0 := by dsimp [x0]; rw [idx_mod2]; omega
        have hne : evenProj (hSum {x0}) ≠ 0 := by
          rw [hSum, Finset.sum_singleton, hVec_eq_incEven hp0, evenProj_incEven]
          exact col2_ne_zero _
        obtain ⟨D, hDP, hDne, hDev⟩ := active_proj ht hg evenProj hx0P hne
        rcases hdec D hDP with ⟨k, hk, rfl⟩ | ⟨k, _, rfl⟩
        · have hk0 : k = 0 := by omega
          exact hDne (by subst hk0; rfl)
        · have hpD : (idx ht (y.val + 1 + 2 * k)).val % 2 = 1 := by rw [idx_mod2]; omega
          rw [hSum, Finset.sum_singleton, hVec_eq_incOdd hpD, evenProj_incOdd] at hDev
          exact hDev rfl
      · have hp0 : x0.val % 2 = 1 := by dsimp [x0]; rw [idx_mod2]; omega
        have hne : oddProj (hSum {x0}) ≠ 0 := by
          rw [hSum, Finset.sum_singleton, hVec_eq_incOdd hp0, oddProj_incOdd]
          exact col2_ne_zero _
        obtain ⟨D, hDP, hDne, hDod⟩ := active_proj ht hg oddProj hx0P hne
        rcases hdec D hDP with ⟨k, hk, rfl⟩ | ⟨k, _, rfl⟩
        · have hk0 : k = 0 := by omega
          exact hDne (by subst hk0; rfl)
        · have hpD : (idx ht (y.val + 1 + 2 * k)).val % 2 = 0 := by rw [idx_mod2]; omega
          rw [hSum, Finset.sum_singleton, hVec_eq_incEven hpD, oddProj_incEven] at hDod
          exact hDod rfl
  have hk1 : 2 ≤ k1 := hge2 a1 a2 k1 k2 hpar (fun k hk => (hsolo1 k hk).1) hdecomp
  have hk2 : 2 ≤ k2 := hge2 a2 a1 k2 k1 (by omega) (fun k hk => (hsolo2 k hk).1)
    (fun C hC => (hdecomp C hC).symm)
  have hs1 := span_of_consec_solos ht (a1.val + 1) k1 hk1 (fun j hj => (hsolo1 j hj).2)
  have hs2 := span_of_consec_solos ht (a2.val + 1) k2 hk2 (fun j hj => (hsolo2 j hj).2)
  by_cases hp : (a1.val + 1) % 2 = 0
  · exact ⟨hs1.1 hp, hs2.2 (by omega)⟩
  · exact ⟨hs2.1 (by omega), hs1.2 (by omega)⟩

lemma runs_sub1_run_gap {U : Submodule F2 (W t)} (ht2 : 2 ≤ t) (hg : goodU ht U)
    {a1 a2 : Fin (6 * t)} {k1 k2 : ℕ}
    (ha1S : a1 ∈ suppU U) (harc1 : cc (nxt ht) (suppU U) a1 = arc ht a1 2)
    (hpar : a2.val % 2 = (a1.val + 3) % 2)
    (hk12 : k1 + k2 = 3 * t - 2)
    (ha1_from_a2 : k2 = 1 → idx ht (a2.val + 3) = a1)
    (hsolo1 : ∀ k < k1, ({idx ht (a1.val + 3 + 2 * k)} : Finset (Fin (6 * t))) ∈ pcs (nxt ht) (suppU U) ∧
      hVec (idx ht (a1.val + 3 + 2 * k)) ∈ hSpace ht (suppU U))
    (hsolo2 : ∀ k < k2, ({idx ht (a2.val + 1 + 2 * k)} : Finset (Fin (6 * t))) ∈ pcs (nxt ht) (suppU U) ∧
      hVec (idx ht (a2.val + 1 + 2 * k)) ∈ hSpace ht (suppU U))
    (hdecomp : ∀ C ∈ pcs (nxt ht) (suppU U),
      C = cc (nxt ht) (suppU U) a1 ∨
      (∃ k < k1, C = {idx ht (a1.val + 3 + 2 * k)}) ∨
      (∃ k < k2, C = {idx ht (a2.val + 1 + 2 * k)})) :
    LinearMap.range incEven ≤ hSpace ht (suppU U) ∧ LinearMap.range incOdd ≤ hSpace ht (suppU U) := by
  have hC1P : cc (nxt ht) (suppU U) a1 ∈ pcs (nxt ht) (suppU U) := Finset.mem_image_of_mem _ ha1S
  have hC1sum : hSum (cc (nxt ht) (suppU U) a1) = hPat a1.val + hPat (a1.val + 1) := by
    rw [harc1, hSum_arc ht a1 (by omega), arcSum_two]
  have hk1_pos : 1 ≤ k1 := by
    by_contra hk0
    by_cases hp : a1.val % 2 = 0
    · have hod : oddProj (hSum (cc (nxt ht) (suppU U) a1)) ≠ 0 := by
        rw [hC1sum, hPat_eq_incEven hp, hPat_eq_incOdd (by omega), map_add,
          oddProj_incEven, oddProj_incOdd, zero_add]
        exact col2_ne_zero _
      obtain ⟨D, hDP, hDne, hDod⟩ := active_proj ht hg oddProj hC1P hod
      rcases hdecomp D hDP with rfl | ⟨k, hk, rfl⟩ | ⟨k, _, rfl⟩
      · exact hDne rfl
      · omega
      · have hpD : (idx ht (a2.val + 1 + 2 * k)).val % 2 = 0 := by rw [idx_mod2]; omega
        rw [hSum, Finset.sum_singleton, hVec_eq_incEven hpD, oddProj_incEven] at hDod
        exact hDod rfl
    · have hev : evenProj (hSum (cc (nxt ht) (suppU U) a1)) ≠ 0 := by
        rw [hC1sum, hPat_eq_incOdd (by omega), hPat_eq_incEven (by omega), map_add,
          evenProj_incOdd, evenProj_incEven, zero_add]
        exact col2_ne_zero _
      obtain ⟨D, hDP, hDne, hDev⟩ := active_proj ht hg evenProj hC1P hev
      rcases hdecomp D hDP with rfl | ⟨k, hk, rfl⟩ | ⟨k, _, rfl⟩
      · exact hDne rfl
      · omega
      · have hpD : (idx ht (a2.val + 1 + 2 * k)).val % 2 = 1 := by rw [idx_mod2]; omega
        rw [hSum, Finset.sum_singleton, hVec_eq_incOdd hpD, evenProj_incOdd] at hDev
        exact hDev rfl
  have hk2_pos : 1 ≤ k2 := by
    by_contra hk0
    by_cases hp : a1.val % 2 = 0
    · have hev : evenProj (hSum (cc (nxt ht) (suppU U) a1)) ≠ 0 := by
        rw [hC1sum, hPat_eq_incEven hp, hPat_eq_incOdd (by omega), map_add,
          evenProj_incEven, evenProj_incOdd, add_zero]
        exact col2_ne_zero _
      obtain ⟨D, hDP, hDne, hDev⟩ := active_proj ht hg evenProj hC1P hev
      rcases hdecomp D hDP with rfl | ⟨k, _, rfl⟩ | ⟨k, hk, rfl⟩
      · exact hDne rfl
      · have hpD : (idx ht (a1.val + 3 + 2 * k)).val % 2 = 1 := by rw [idx_mod2]; omega
        rw [hSum, Finset.sum_singleton, hVec_eq_incOdd hpD, evenProj_incOdd] at hDev
        exact hDev rfl
      · omega
    · have hod : oddProj (hSum (cc (nxt ht) (suppU U) a1)) ≠ 0 := by
        rw [hC1sum, hPat_eq_incOdd (by omega), hPat_eq_incEven (by omega), map_add,
          oddProj_incOdd, oddProj_incEven, add_zero]
        exact col2_ne_zero _
      obtain ⟨D, hDP, hDne, hDod⟩ := active_proj ht hg oddProj hC1P hod
      rcases hdecomp D hDP with rfl | ⟨k, _, rfl⟩ | ⟨k, hk, rfl⟩
      · exact hDne rfl
      · have hpD : (idx ht (a1.val + 3 + 2 * k)).val % 2 = 0 := by rw [idx_mod2]; omega
        rw [hSum, Finset.sum_singleton, hVec_eq_incEven hpD, oddProj_incEven] at hDod
        exact hDod rfl
      · omega
  by_cases hk2_2 : 2 ≤ k2
  · have hs2 := span_of_consec_solos ht (a2.val + 1) k2 hk2_2 (fun j hj => (hsolo2 j hj).2)
    by_cases hk1_2 : 2 ≤ k1
    · have hs1 := span_of_consec_solos ht (a1.val + 3) k1 hk1_2 (fun j hj => (hsolo1 j hj).2)
      by_cases hp : a1.val % 2 = 0
      · exact ⟨hs2.1 (by omega), hs1.2 (by omega)⟩
      · exact ⟨hs1.1 (by omega), hs2.2 (by omega)⟩
    · have hm_s := (hsolo1 0 (by omega)).2
      have hm_c := mem_hSpace ht hC1P
      by_cases hp : a1.val % 2 = 0
      · have hev : LinearMap.range incEven ≤ hSpace ht (suppU U) := hs2.1 (by omega)
        refine ⟨hev, range_incOdd_le_of_even_and_consec hev hm_c hm_s (r := (a1.val + 1) / 2) ?_ ?_⟩
        · rw [hC1sum, hPat_eq_incEven hp, hPat_eq_incOdd (by omega), map_add,
            oddProj_incEven, oddProj_incOdd, zero_add]
        · have hp' : (idx ht (a1.val + 3 + 2 * 0)).val % 2 = 1 := by rw [idx_mod2]; omega
          rw [hVec_eq_incOdd hp', oddProj_incOdd, ← col2_mod3, idx_div2_mod3, col2_mod3]
          congr 1; omega
      · have hod : LinearMap.range incOdd ≤ hSpace ht (suppU U) := hs2.2 (by omega)
        refine ⟨range_incEven_le_of_odd_and_consec hod hm_c hm_s (r := (a1.val + 1) / 2) ?_ ?_, hod⟩
        · rw [hC1sum, hPat_eq_incOdd (by omega), hPat_eq_incEven (by omega), map_add,
            evenProj_incOdd, evenProj_incEven, zero_add]
        · have hp' : (idx ht (a1.val + 3 + 2 * 0)).val % 2 = 0 := by rw [idx_mod2]; omega
          rw [hVec_eq_incEven hp', evenProj_incEven, ← col2_mod3, idx_div2_mod3, col2_mod3]
          congr 1; omega
  · have hk2_eq : k2 = 1 := by omega
    have hk1_2 : 2 ≤ k1 := by omega
    have hs1 := span_of_consec_solos ht (a1.val + 3) k1 hk1_2 (fun j hj => (hsolo1 j hj).2)
    have hm_s := (hsolo2 0 (by omega)).2
    have hm_c := mem_hSpace ht hC1P
    have ha1_rel : idx ht (a2.val + 3) = a1 := ha1_from_a2 hk2_eq
    by_cases hp : a1.val % 2 = 0
    · have hod : LinearMap.range incOdd ≤ hSpace ht (suppU U) := hs1.2 (by omega)
      refine ⟨range_incEven_le_of_odd_and_consec hod hm_s hm_c (r := (a2.val + 1) / 2) ?_ ?_, hod⟩
      · have hp' : (idx ht (a2.val + 1 + 2 * 0)).val % 2 = 0 := by rw [idx_mod2]; omega
        rw [hVec_eq_incEven hp', evenProj_incEven, ← col2_mod3, idx_div2_mod3, col2_mod3]
      · rw [hC1sum, hPat_eq_incEven hp, hPat_eq_incOdd (by omega), map_add,
          evenProj_incEven, evenProj_incOdd, add_zero, ← col2_mod3, ← ha1_rel, idx_div2_mod3, col2_mod3]
        congr 1; omega
    · have hev : LinearMap.range incEven ≤ hSpace ht (suppU U) := hs1.1 (by omega)
      refine ⟨hev, range_incOdd_le_of_even_and_consec hev hm_s hm_c (r := (a2.val + 1) / 2) ?_ ?_⟩
      · have hp' : (idx ht (a2.val + 1 + 2 * 0)).val % 2 = 1 := by rw [idx_mod2]; omega
        rw [hVec_eq_incOdd hp', oddProj_incOdd, ← col2_mod3, idx_div2_mod3, col2_mod3]
      · rw [hC1sum, hPat_eq_incOdd (by omega), hPat_eq_incEven (by omega), map_add,
          oddProj_incOdd, oddProj_incEven, add_zero, ← col2_mod3, ← ha1_rel, idx_div2_mod3, col2_mod3]
        congr 1; omega

lemma runs_sub1_two_runs_half {S : Finset (Fin (6 * t))}
    {a1 a2 : Fin (6 * t)} {k1 k2 : ℕ}
    (ha1S : a1 ∈ S) (ha2S : a2 ∈ S)
    (harc1 : cc (nxt ht) S a1 = arc ht a1 2) (harc2 : cc (nxt ht) S a2 = arc ht a2 2)
    (hpar : a2.val % 2 = (a1.val + 3) % 2)
    (hk2_2 : 2 ≤ k2)
    (ha2_of_0 : k1 = 0 → idx ht (a1.val + 3) = a2)
    (hsolo1 : ∀ k < k1, hVec (idx ht (a1.val + 3 + 2 * k)) ∈ hSpace ht S)
    (hsolo2 : ∀ k < k2, hVec (idx ht (a2.val + 3 + 2 * k)) ∈ hSpace ht S) :
    LinearMap.range incEven ≤ hSpace ht S ∧ LinearMap.range incOdd ≤ hSpace ht S := by
  have hm1 : hSum (cc (nxt ht) S a1) ∈ hSpace ht S := mem_hSpace ht (Finset.mem_image_of_mem _ ha1S)
  have hm2 : hSum (cc (nxt ht) S a2) ∈ hSpace ht S := mem_hSpace ht (Finset.mem_image_of_mem _ ha2S)
  have hC1sum : hSum (cc (nxt ht) S a1) = hPat a1.val + hPat (a1.val + 1) := by
    rw [harc1, hSum_arc ht a1 (by omega), arcSum_two]
  have hC2sum : hSum (cc (nxt ht) S a2) = hPat a2.val + hPat (a2.val + 1) := by
    rw [harc2, hSum_arc ht a2 (by omega), arcSum_two]
  have hs2 := span_of_consec_solos ht (a2.val + 3) k2 hk2_2 hsolo2
  by_cases hk1_2 : 2 ≤ k1
  · have hs1 := span_of_consec_solos ht (a1.val + 3) k1 hk1_2 hsolo1
    by_cases hp : a1.val % 2 = 0
    · exact ⟨hs2.1 (by omega), hs1.2 (by omega)⟩
    · exact ⟨hs1.1 (by omega), hs2.2 (by omega)⟩
  · by_cases hk1_1 : k1 = 1
    · have hm_s := hsolo1 0 (by omega)
      by_cases hp : a1.val % 2 = 0
      · have hev : LinearMap.range incEven ≤ hSpace ht S := hs2.1 (by omega)
        refine ⟨hev, range_incOdd_le_of_even_and_consec hev hm1 hm_s (r := (a1.val + 1) / 2) ?_ ?_⟩
        · rw [hC1sum, hPat_eq_incEven hp, hPat_eq_incOdd (by omega), map_add,
            oddProj_incEven, oddProj_incOdd, zero_add]
        · have hp' : (idx ht (a1.val + 3 + 2 * 0)).val % 2 = 1 := by rw [idx_mod2]; omega
          rw [hVec_eq_incOdd hp', oddProj_incOdd, ← col2_mod3, idx_div2_mod3, col2_mod3]
          congr 1; omega
      · have hod : LinearMap.range incOdd ≤ hSpace ht S := hs2.2 (by omega)
        refine ⟨range_incEven_le_of_odd_and_consec hod hm1 hm_s (r := (a1.val + 1) / 2) ?_ ?_, hod⟩
        · rw [hC1sum, hPat_eq_incOdd (by omega), hPat_eq_incEven (by omega), map_add,
            evenProj_incOdd, evenProj_incEven, zero_add]
        · have hp' : (idx ht (a1.val + 3 + 2 * 0)).val % 2 = 0 := by rw [idx_mod2]; omega
          rw [hVec_eq_incEven hp', evenProj_incEven, ← col2_mod3, idx_div2_mod3, col2_mod3]
          congr 1; omega
    · have hk1_0 : k1 = 0 := by omega
      have ha2_rel : idx ht (a1.val + 3) = a2 := ha2_of_0 hk1_0
      by_cases hp : a1.val % 2 = 0
      · have hev : LinearMap.range incEven ≤ hSpace ht S := hs2.1 (by omega)
        refine ⟨hev, range_incOdd_le_of_even_and_consec hev hm1 hm2 (r := (a1.val + 1) / 2) ?_ ?_⟩
        · rw [hC1sum, hPat_eq_incEven hp, hPat_eq_incOdd (by omega), map_add,
            oddProj_incEven, oddProj_incOdd, zero_add]
        · rw [hC2sum, hPat_eq_incOdd (by omega), hPat_eq_incEven (by omega), map_add,
            oddProj_incOdd, oddProj_incEven, add_zero, ← col2_mod3, ← ha2_rel, idx_div2_mod3, col2_mod3]
          congr 1; omega
      · have hod : LinearMap.range incOdd ≤ hSpace ht S := hs2.2 (by omega)
        refine ⟨range_incEven_le_of_odd_and_consec hod hm1 hm2 (r := (a1.val + 1) / 2) ?_ ?_, hod⟩
        · rw [hC1sum, hPat_eq_incOdd (by omega), hPat_eq_incEven (by omega), map_add,
            evenProj_incOdd, evenProj_incEven, zero_add]
        · rw [hC2sum, hPat_eq_incEven (by omega), hPat_eq_incOdd (by omega), map_add,
            evenProj_incEven, evenProj_incOdd, add_zero, ← col2_mod3, ← ha2_rel, idx_div2_mod3, col2_mod3]
          congr 1; omega

lemma runs_eq_a_sub_one {U : Submodule F2 (W t)} (ht2 : 2 ≤ t) (hg : goodU ht U)
    (hS : suppU U ≠ Finset.univ) (h0 : 0 < sitesOf (suppU U) 0) (h1 : 0 < sitesOf (suppU U) 1)
    (hr : (pcs (nxt ht) (suppU U)).card = 3 * t - 1) : rk ht (suppU U) = 4 := by
  set S := suppU U
  set P := pcs (nxt ht) S
  let RunStarts := Finset.univ.filter (fun x : Fin (6 * t) => x ∈ S ∧ prv ht x ∉ S)
  let Gaps := Finset.univ.filter (fun x : Fin (6 * t) => x ∉ S ∧ prv ht x ∉ S)
  let Starts := Finset.univ.filter (fun x : Fin (6 * t) => prv ht x ∉ S)
  have hdisRG : Disjoint RunStarts Gaps :=
    Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2.1 h1.1
  have hunRG : RunStarts ∪ Gaps = Starts := by
    ext x; simp only [RunStarts, Gaps, Starts, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hbijRS : Finset.image (cc (nxt ht) S) RunStarts = P := by
    ext C
    simp only [Finset.mem_image, RunStarts, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨s, ⟨hs, _⟩, rfl⟩
      exact Finset.mem_image_of_mem _ hs
    · intro hC
      obtain ⟨s, hsC, hps, _, _, _, _⟩ := comp_arc ht hS hC
      obtain ⟨hsS, hcs⟩ := center (nxt ht) S hC hsC
      exact ⟨s, ⟨hsS, hps⟩, hcs⟩
  have hinjRS : Set.InjOn (cc (nxt ht) S) (RunStarts : Set (Fin (6 * t))) := by
    intro s₁ hs₁ s₂ hs₂ heq
    obtain ⟨h1S, h1p⟩ := (Finset.mem_filter.mp hs₁).2
    obtain ⟨h2S, h2p⟩ := (Finset.mem_filter.mp hs₂).2
    obtain ⟨harc1, hlt1, _⟩ := comp_arc_of_start ht hS h1S h1p
    have h2in : s₂ ∈ cc (nxt ht) S s₁ := heq.symm ▸ selfMem (nxt ht) S h2S
    rw [harc1, mem_arc_iff] at h2in
    obtain ⟨k, hk, hkeq⟩ := h2in
    cases k with
    | zero => rw [add_zero, idx_self] at hkeq; exact hkeq
    | succ k =>
      exfalso; apply h2p
      have : prv ht s₂ = idx ht (s₁.val + k) := by
        rw [← hkeq, ← add_assoc, ← nxt_idx, prv_nxt]
      rw [this]
      have hmem : idx ht (s₁.val + k) ∈ cc (nxt ht) S s₁ := by
        rw [harc1, mem_arc_iff]; exact ⟨k, by omega, rfl⟩
      exact (Finset.mem_filter.mp hmem).1
  have hGaps_eq : Gaps = Finset.univ \ P.biUnion (halo (nxt ht)) := by
    ext x
    simp only [Gaps, P, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
      mem_biUnion_halo_iff, not_or]
  have hsum_halo : ∑ C ∈ P, (C.card + 1) + Gaps.card = 6 * t := by
    have h1' : ∑ C ∈ P, (C.card + 1) = (P.biUnion (halo (nxt ht))).card := by
      rw [Finset.card_biUnion (separate (nxt ht) S (ninj ht))]
      exact Finset.sum_congr rfl fun C hC => (halo_card_eq ht hS hC).symm
    rw [h1', hGaps_eq, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    have hle := Finset.card_le_univ (P.biUnion (halo (nxt ht)))
    simp only [Fintype.card_fin] at hle
    omega
  have hsum_def : ∑ C ∈ P, (C.card - 1) + Gaps.card = 2 := by
    have h1' : ∑ C ∈ P, (C.card + 1) = ∑ C ∈ P, (C.card - 1) + 2 * P.card := by
      have : ∑ C ∈ P, (C.card + 1) = ∑ C ∈ P, ((C.card - 1) + 2) :=
        Finset.sum_congr rfl fun C hC => by
          have := Finset.card_pos.mpr (populated (nxt ht) S hC); omega
      rw [this, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
      ring
    omega
  let dwt : Fin (6 * t) → ℕ := fun x => if x ∈ S then (cc (nxt ht) S x).card - 1 else 1
  let Defects := Starts.filter (fun x => 0 < dwt x)
  have hsum_dwt : ∑ x ∈ Defects, dwt x = 2 := by
    have h1' : ∑ x ∈ Defects, dwt x = ∑ x ∈ Starts, dwt x := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro x hx hnd
      simp only [Defects, Finset.mem_filter, not_and, not_lt, Nat.le_zero] at hnd
      exact hnd hx
    rw [h1', ← hunRG, Finset.sum_union hdisRG]
    have hG : ∑ x ∈ Gaps, dwt x = Gaps.card := by
      have : ∑ x ∈ Gaps, dwt x = ∑ _ ∈ Gaps, 1 :=
        Finset.sum_congr rfl fun x hx => by
          have hxS := (Finset.mem_filter.mp hx).2.1
          simp [dwt, hxS]
      simp [this]
    have hR : ∑ x ∈ RunStarts, dwt x = ∑ C ∈ P, (C.card - 1) := by
      rw [← hbijRS, Finset.sum_image hinjRS]
      apply Finset.sum_congr rfl
      intro x hx
      have hxS := (Finset.mem_filter.mp hx).2.1
      simp [dwt, hxS]
    rw [hG, hR, hsum_def]
  have hSolo : ∀ x ∈ Starts, x ∉ Defects → x ∈ S ∧ nxt ht x ∉ S ∧ (cc (nxt ht) S x).card = 1 := by
    intro x hx hnd
    have hpx : prv ht x ∉ S := (Finset.mem_filter.mp hx).2
    have hdw0 : dwt x = 0 := by
      by_contra hne
      exact hnd (Finset.mem_filter.mpr ⟨hx, by omega⟩)
    have hxS : x ∈ S := by
      by_contra hns
      simp [dwt, hns] at hdw0
    have hpos : 0 < (cc (nxt ht) S x).card :=
      Finset.card_pos.mpr ⟨x, selfMem (nxt ht) S hxS⟩
    have hc1 : (cc (nxt ht) S x).card = 1 := by simp [dwt, hxS] at hdw0; omega
    have hnx : nxt ht x ∉ S := by
      obtain ⟨_, _, hout⟩ := comp_arc_of_start ht hS hxS hpx
      rw [hc1] at hout
      simpa [← nxt_idx, idx_self] using hout
    exact ⟨hxS, hnx, hc1⟩
  have hDef_card_le : Defects.card ≤ 2 := by
    have hge : Defects.card ≤ ∑ x ∈ Defects, dwt x := by
      have : ∑ _ ∈ Defects, 1 ≤ ∑ x ∈ Defects, dwt x :=
        Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2
      simpa using this
    omega
  have hDef_card_pos : 0 < Defects.card := by
    by_contra h0'
    have he : Defects = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [he, Finset.sum_empty] at hsum_dwt
    omega
  have hwalk : ∀ (b : Fin (6 * t)) (len : ℕ), b ∈ Starts → len ≤ 6 * t →
      (∀ j < len, idx ht (b.val + j) ∉ Defects) →
      ∀ k, 2 * k < len →
        idx ht (b.val + 2 * k) ∈ S ∧
        prv ht (idx ht (b.val + 2 * k)) ∉ S ∧
        nxt ht (idx ht (b.val + 2 * k)) ∉ S := by
    intro b len hb hlen hnoDef
    have hgo : ∀ k, 2 * k ≤ len → idx ht (b.val + 2 * k) ∈ Starts := by
      intro k
      induction k with
      | zero => intro _; simpa [idx_self] using hb
      | succ k ih =>
        intro hk
        have hst : idx ht (b.val + 2 * k) ∈ Starts := ih (by omega)
        have hnd : idx ht (b.val + 2 * k) ∉ Defects := hnoDef (2 * k) (by omega)
        obtain ⟨_, hnx, _⟩ := hSolo _ hst hnd
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have e : prv ht (idx ht (b.val + 2 * (k + 1))) = nxt ht (idx ht (b.val + 2 * k)) := by
          rw [nxt_idx, show b.val + 2 * (k + 1) = (b.val + 2 * k + 1) + 1 by omega,
            ← nxt_idx, prv_nxt]
        rwa [e]
    intro k hk
    have hst := hgo k (by omega)
    have hnd := hnoDef (2 * k) hk
    obtain ⟨hs, hnx, _⟩ := hSolo _ hst hnd
    exact ⟨hs, (Finset.mem_filter.mp hst).2, hnx⟩
  by_cases hcard1 : Defects.card = 1
  · obtain ⟨a1, hDefEq⟩ := Finset.card_eq_one.mp hcard1
    have ha1Def : a1 ∈ Defects := hDefEq.symm ▸ Finset.mem_singleton_self a1
    have hdw2 : dwt a1 = 2 := by rw [hDefEq, Finset.sum_singleton] at hsum_dwt; exact hsum_dwt
    have ha1S : a1 ∈ S := by by_contra hns; simp [dwt, hns] at hdw2
    have ha1p : prv ht a1 ∉ S := (Finset.mem_filter.mp (Finset.mem_filter.mp ha1Def).1).2
    have ha1c : (cc (nxt ht) S a1).card = 3 := by
      have hpos := Finset.card_pos.mpr ⟨a1, selfMem (nxt ht) S ha1S⟩
      simp [dwt, ha1S] at hdw2; omega
    obtain ⟨harc1, _, hout1⟩ := comp_arc_of_start ht hS ha1S ha1p
    rw [ha1c] at harc1 hout1
    let b := idx ht (a1.val + 4)
    have hb2 : b.val % 2 = a1.val % 2 := by dsimp [b]; rw [idx_mod2]; omega
    have hbSt : b ∈ Starts := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have : prv ht b = idx ht (a1.val + 3) := by
        dsimp only [b]
        rw [show a1.val + 4 = (a1.val + 3) + 1 by omega, ← nxt_idx, prv_nxt]
      rwa [this]
    have hnoDef : ∀ j < 6 * t - 4, idx ht (b.val + j) ∉ Defects := by
      intro j hj hmem
      rw [hDefEq, Finset.mem_singleton] at hmem
      have heq : idx ht (a1.val + (4 + j)) = idx ht (a1.val + 0) := by
        have hb1 : idx ht (b.val + j) = idx ht (a1.val + (4 + j)) := by
          apply Fin.ext; dsimp only [b]
          change ((a1.val + 4) % (6 * t) + j) % (6 * t) = (a1.val + (4 + j)) % (6 * t)
          rw [Nat.mod_add_mod, add_assoc]
        rw [← hb1, hmem, add_zero, idx_self]
      have := idx_inj_range ht a1 (le_refl _) (by omega) (by omega) heq
      omega
    have hw := hwalk b (6 * t - 4) hbSt (by omega) hnoDef
    let Q := (Finset.range (3 * t - 2)).image (fun k => ({idx ht (b.val + 2 * k)} : Finset (Fin (6 * t))))
    have hC1P : cc (nxt ht) S a1 ∈ P := Finset.mem_image_of_mem _ ha1S
    have hQsub : Q ⊆ P.erase (cc (nxt ht) S a1) := by
      intro C hC
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hC
      have hklt : k < 3 * t - 2 := Finset.mem_range.mp hk
      obtain ⟨hs, hp, hn⟩ := hw k (by omega)
      have hmemP := (solo_mem_hSpace ht hs hp hn).1
      refine Finset.mem_erase.mpr ⟨?_, hmemP⟩
      intro heq
      have := congrArg Finset.card heq
      rw [Finset.card_singleton, ha1c] at this
      omega
    have hQcard : Q.card = 3 * t - 2 := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro k₁ hk₁ k₂ hk₂ heq
      have hfeq : idx ht (b.val + 2 * k₁) = idx ht (b.val + 2 * k₂) :=
        Finset.singleton_injective heq
      have := idx_inj_range ht b (le_refl _) (by have := Finset.mem_range.mp hk₁; omega)
        (by have := Finset.mem_range.mp hk₂; omega) hfeq
      omega
    have hQeq : P.erase (cc (nxt ht) S a1) = Q := by
      apply (Finset.eq_of_subset_of_card_le hQsub _).symm
      rw [hQcard, Finset.card_erase_of_mem hC1P]
      omega
    exfalso
    by_cases hap : a1.val % 2 = 0
    · have hod : oddProj (hSum (cc (nxt ht) S a1)) ≠ 0 := by
        rw [harc1, hSum_arc ht a1 (by omega)]
        intro hz; rw [arcSum_oddProj_zero_iff] at hz; omega
      obtain ⟨D, hDP, hDne, hDod⟩ := active_proj ht hg oddProj hC1P hod
      have hDQ : D ∈ Q := hQeq ▸ Finset.mem_erase.mpr ⟨hDne, hDP⟩
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hDQ
      have hpar : (idx ht (b.val + 2 * k)).val % 2 = 0 := by rw [idx_mod2]; omega
      rw [hSum, Finset.sum_singleton, hVec_eq_incEven hpar, oddProj_incEven] at hDod
      exact hDod rfl
    · have hev : evenProj (hSum (cc (nxt ht) S a1)) ≠ 0 := by
        rw [harc1, hSum_arc ht a1 (by omega)]
        intro hz; rw [arcSum_evenProj_zero_iff] at hz; omega
      obtain ⟨D, hDP, hDne, hDev⟩ := active_proj ht hg evenProj hC1P hev
      have hDQ : D ∈ Q := hQeq ▸ Finset.mem_erase.mpr ⟨hDne, hDP⟩
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hDQ
      have hpar : (idx ht (b.val + 2 * k)).val % 2 = 1 := by rw [idx_mod2]; omega
      rw [hSum, Finset.sum_singleton, hVec_eq_incOdd hpar, evenProj_incOdd] at hDev
      exact hDev rfl
  · have hcard2 : Defects.card = 2 := by omega
    obtain ⟨a1, a2, hne12, hDefEq⟩ := Finset.card_eq_two.mp hcard2
    have ha1Def : a1 ∈ Defects := by rw [hDefEq]; simp
    have ha2Def : a2 ∈ Defects := by rw [hDefEq]; simp
    have hdw12 : dwt a1 + dwt a2 = 2 := by
      rw [hDefEq, Finset.sum_pair hne12] at hsum_dwt; exact hsum_dwt
    have hdw1 : dwt a1 = 1 := by
      have p1 := (Finset.mem_filter.mp ha1Def).2
      have p2 := (Finset.mem_filter.mp ha2Def).2
      omega
    have hdw2 : dwt a2 = 1 := by omega
    let L : Fin (6 * t) → ℕ := fun a => if a ∈ S then 3 else 1
    have hL_spec : ∀ a ∈ Defects, dwt a = 1 →
        (L a = 1 ∧ a ∉ S ∧ prv ht a ∉ S ∧ idx ht (a.val + 1) ∈ Starts) ∨
        (L a = 3 ∧ a ∈ S ∧ prv ht a ∉ S ∧ cc (nxt ht) S a = arc ht a 2 ∧
          idx ht (a.val + 2) ∉ S ∧ idx ht (a.val + 3) ∈ Starts ∧
          idx ht (a.val + 1) ∈ S ∧ idx ht (a.val + 1) ∉ Starts ∧ idx ht (a.val + 2) ∉ Starts) := by
      intro a ha hdw
      have hap : prv ht a ∉ S := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
      by_cases haS : a ∈ S
      · right
        have hpos := Finset.card_pos.mpr ⟨a, selfMem (nxt ht) S haS⟩
        have hc2 : (cc (nxt ht) S a).card = 2 := by simp [dwt, haS] at hdw; omega
        obtain ⟨harc, _, hout⟩ := comp_arc_of_start ht hS haS hap
        rw [hc2] at harc hout
        have h1S : idx ht (a.val + 1) ∈ S := by
          have : idx ht (a.val + 1) ∈ cc (nxt ht) S a := by
            rw [harc, mem_arc_iff]; exact ⟨1, by decide, rfl⟩
          exact (Finset.mem_filter.mp this).1
        have h1nSt : idx ht (a.val + 1) ∉ Starts := by
          simp only [Starts, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
          have : prv ht (idx ht (a.val + 1)) = a := by rw [← nxt_idx, idx_self, prv_nxt]
          rwa [this]
        have h2nSt : idx ht (a.val + 2) ∉ Starts := by
          simp only [Starts, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
          have : prv ht (idx ht (a.val + 2)) = idx ht (a.val + 1) := by
            rw [show a.val + 2 = (a.val + 1) + 1 by omega, ← nxt_idx, prv_nxt]
          rwa [this]
        have h3St : idx ht (a.val + 3) ∈ Starts := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have : prv ht (idx ht (a.val + 3)) = idx ht (a.val + 2) := by
            rw [show a.val + 3 = (a.val + 2) + 1 by omega, ← nxt_idx, prv_nxt]
          rwa [this]
        exact ⟨by simp [L, haS], haS, hap, harc, hout, h3St, h1S, h1nSt, h2nSt⟩
      · left
        have h1St : idx ht (a.val + 1) ∈ Starts := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have : prv ht (idx ht (a.val + 1)) = a := by rw [← nxt_idx, idx_self, prv_nxt]
          rwa [this]
        exact ⟨by simp [L, haS], haS, hap, h1St⟩
    have hseg : ∀ (x y : Fin (6 * t)), x ∈ Defects → y ∈ Defects → x ≠ y → dwt x = 1 →
        Defects = {x, y} →
        let dist := (y.val + 6 * t - x.val) % (6 * t)
        L x ≤ dist ∧ (dist - L x) % 2 = 0 ∧
        (∀ k < (dist - L x) / 2,
          idx ht (x.val + L x + 2 * k) ∈ S ∧
          prv ht (idx ht (x.val + L x + 2 * k)) ∉ S ∧
          nxt ht (idx ht (x.val + L x + 2 * k)) ∉ S) := by
      intro x y hxD hyD hxy hdwx hDeq dist
      have hdist_pos : 0 < dist := by
        by_contra h0'
        have h0'' : dist = 0 := by omega
        apply hxy; apply Fin.ext
        dsimp only [dist] at h0''
        have hxlt := x.isLt; have hylt := y.isLt
        by_cases c : y.val + 6 * t - x.val < 6 * t
        · rw [Nat.mod_eq_of_lt c] at h0''; omega
        · rw [mod_eq_sub_of_lt2 (by omega) (by omega)] at h0''; omega
      have hdist_lt : dist < 6 * t := Nat.mod_lt _ (by omega)
      have hy_eq : idx ht (x.val + dist) = y := idx_add_dist ht x y
      have hLx_le : L x ≤ dist := by
        rcases hL_spec x hxD hdwx with ⟨hL1, _, _, _⟩ | ⟨hL3, _, _, _, _, _, _, h1n, h2n⟩
        · omega
        · rw [hL3]
          by_contra hlt3
          have hySt : y ∈ Starts := (Finset.mem_filter.mp hyD).1
          have hd12 : dist = 1 ∨ dist = 2 := by omega
          rcases hd12 with hd1 | hd2
          · rw [hd1] at hy_eq; exact h1n (hy_eq ▸ hySt)
          · rw [hd2] at hy_eq; exact h2n (hy_eq ▸ hySt)
      have hbSt : idx ht (x.val + L x) ∈ Starts := by
        rcases hL_spec x hxD hdwx with ⟨hL1, _, _, h1St⟩ | ⟨hL3, _, _, _, _, h3St, _, _, _⟩
        · rw [hL1]; exact h1St
        · rw [hL3]; exact h3St
      let b := idx ht (x.val + L x)
      have hnoD : ∀ j < dist - L x, idx ht (b.val + j) ∉ Defects := by
        intro j hj hmem
        rw [hDeq, Finset.mem_insert, Finset.mem_singleton] at hmem
        have hb1 : idx ht (b.val + j) = idx ht (x.val + (L x + j)) := by
          apply Fin.ext; dsimp only [b]
          change ((x.val + L x) % (6 * t) + j) % (6 * t) = (x.val + (L x + j)) % (6 * t)
          rw [Nat.mod_add_mod, add_assoc]
        rw [hb1] at hmem
        rcases hmem with h1' | h2'
        · have : idx ht (x.val + (L x + j)) = idx ht (x.val + 0) := by rw [h1', add_zero, idx_self]
          have := idx_inj_range ht x (le_refl _) (by omega) (by omega) this
          have : 0 < L x := by dsimp [L]; split_ifs <;> omega
          omega
        · rw [← hy_eq] at h2'
          have := idx_inj_range ht x (le_refl _) (by omega) hdist_lt h2'
          omega
      have hw := hwalk b (dist - L x) hbSt (by omega) hnoD
      have heven : (dist - L x) % 2 = 0 := by
        by_contra hodd
        let q := (dist - L x) / 2
        obtain ⟨hs, _, _⟩ := hw q (by omega)
        have hpy : prv ht y ∈ S := by
          have e : prv ht y = idx ht (b.val + 2 * q) := by
            rw [← hy_eq]
            have e1 : idx ht (b.val + 2 * q) = idx ht (x.val + (L x + 2 * q)) := by
              apply Fin.ext; dsimp only [b]
              change ((x.val + L x) % (6 * t) + 2 * q) % (6 * t) = (x.val + (L x + 2 * q)) % (6 * t)
              rw [Nat.mod_add_mod, add_assoc]
            rw [e1, show x.val + dist = (x.val + (L x + 2 * q)) + 1 by omega, ← nxt_idx, prv_nxt]
          rwa [e]
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp hyD).1).2 hpy
      refine ⟨hLx_le, heven, fun k hk => ?_⟩
      have hb1 : idx ht (b.val + 2 * k) = idx ht (x.val + L x + 2 * k) := by
        apply Fin.ext; dsimp only [b]
        change ((x.val + L x) % (6 * t) + 2 * k) % (6 * t) = (x.val + L x + 2 * k) % (6 * t)
        rw [Nat.mod_add_mod]
      simpa [hb1] using hw k (by omega)
    have hseg1 := hseg a1 a2 ha1Def ha2Def hne12 hdw1 hDefEq
    have hseg2 := hseg a2 a1 ha2Def ha1Def hne12.symm hdw2 (by rw [hDefEq, Finset.pair_comm])
    let d1 := (a2.val + 6 * t - a1.val) % (6 * t)
    let d2 := (a1.val + 6 * t - a2.val) % (6 * t)
    have hd12_sum : d1 + d2 = 6 * t := by
      dsimp only [d1, d2]
      have h1lt := a1.isLt; have h2lt := a2.isLt
      by_cases c : a1.val < a2.val
      · rw [mod_eq_sub_of_lt2 (by omega) (by omega), Nat.mod_eq_of_lt (by omega)]; omega
      · have hgt : a2.val < a1.val := by
          have : a1.val ≠ a2.val := fun e => hne12 (Fin.ext e)
          omega
        rw [Nat.mod_eq_of_lt (by omega), mod_eq_sub_of_lt2 (by omega) (by omega)]; omega
    let k1 := (d1 - L a1) / 2
    let k2 := (d2 - L a2) / 2
    have hL1_le : L a1 ≤ d1 := hseg1.1
    have hL2_le : L a2 ≤ d2 := hseg2.1
    have h2k1 : 2 * k1 = d1 - L a1 := by have := hseg1.2.1; omega
    have h2k2 : 2 * k2 = d2 - L a2 := by have := hseg2.2.1; omega
    have hsolo1 : ∀ k < k1, ({idx ht (a1.val + L a1 + 2 * k)} : Finset (Fin (6 * t))) ∈ P ∧
        hVec (idx ht (a1.val + L a1 + 2 * k)) ∈ hSpace ht S := fun k hk => by
      obtain ⟨hs, hp, hn⟩ := hseg1.2.2 k hk
      exact solo_mem_hSpace ht hs hp hn
    have hsolo2 : ∀ k < k2, ({idx ht (a2.val + L a2 + 2 * k)} : Finset (Fin (6 * t))) ∈ P ∧
        hVec (idx ht (a2.val + L a2 + 2 * k)) ∈ hSpace ht S := fun k hk => by
      obtain ⟨hs, hp, hn⟩ := hseg2.2.2 k hk
      exact solo_mem_hSpace ht hs hp hn
    have hpar_rel : a2.val % 2 = (a1.val + L a1) % 2 := by
      have hy : idx ht (a1.val + d1) = a2 := idx_add_dist ht a1 a2
      have := congrArg (fun z : Fin (6 * t) => z.val % 2) hy
      rw [idx_mod2] at this; omega
    have hP_decomp : ∀ C ∈ P,
        (a1 ∈ S ∧ C = cc (nxt ht) S a1) ∨
        (a2 ∈ S ∧ C = cc (nxt ht) S a2) ∨
        (∃ k < k1, C = {idx ht (a1.val + L a1 + 2 * k)}) ∨
        (∃ k < k2, C = {idx ht (a2.val + L a2 + 2 * k)}) := by
      intro C hC
      obtain ⟨s, hsC, hps, _, _, _, _⟩ := comp_arc ht hS hC
      obtain ⟨hsS, hcs⟩ := center (nxt ht) S hC hsC
      by_cases hs1 : s = a1
      · left; exact ⟨hs1 ▸ hsS, (hs1 ▸ hcs).symm⟩
      by_cases hs2 : s = a2
      · right; left; exact ⟨hs2 ▸ hsS, (hs2 ▸ hcs).symm⟩
      have hsSt : s ∈ Starts := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hps⟩
      have hsNotDef : s ∉ Defects := by rw [hDefEq]; simp [hs1, hs2]
      obtain ⟨_, hns, _⟩ := hSolo s hsSt hsNotDef
      have hCeq : C = {s} := by
        rw [← hcs]
        have := (solo_mem_hSpace ht hsS hps hns).1
        exact joined (nxt ht) S (Finset.mem_image_of_mem _ hsS) this (selfMem (nxt ht) S hsS)
          (Finset.mem_singleton_self s) (Or.inl rfl)
      let ds := (s.val + 6 * t - a1.val) % (6 * t)
      have hds_lt : ds < 6 * t := Nat.mod_lt _ (by omega)
      have hs_eq : idx ht (a1.val + ds) = s := idx_add_dist ht a1 s
      have hds_ge : L a1 ≤ ds := by
        rcases hL_spec a1 ha1Def hdw1 with ⟨hL1, _, _, _⟩ | ⟨hL3, _, _, _, _, _, _, h1n, h2n⟩
        · rw [hL1]; by_contra h0'; have hd0 : ds = 0 := by omega
          rw [hd0, add_zero, idx_self] at hs_eq; exact hs1 hs_eq.symm
        · rw [hL3]; by_contra hlt3
          have hcases : ds = 0 ∨ ds = 1 ∨ ds = 2 := by omega
          rcases hcases with hd0 | hd1 | hd2
          · rw [hd0, add_zero, idx_self] at hs_eq; exact hs1 hs_eq.symm
          · rw [hd1] at hs_eq; exact h1n (hs_eq ▸ hsSt)
          · rw [hd2] at hs_eq; exact h2n (hs_eq ▸ hsSt)
      by_cases hlt_d1 : ds < d1
      · right; right; left
        have hev_ds : (ds - L a1) % 2 = 0 := by
          by_contra hodd
          let q := (ds - L a1) / 2
          obtain ⟨hs', _, _⟩ := hseg1.2.2 q (by omega)
          have hps' : prv ht s ∈ S := by
            have : prv ht s = idx ht (a1.val + L a1 + 2 * q) := by
              rw [← hs_eq, show a1.val + ds = (a1.val + L a1 + 2 * q) + 1 by omega, ← nxt_idx, prv_nxt]
            rwa [this]
          exact hps hps'
        refine ⟨(ds - L a1) / 2, by omega, ?_⟩
        rw [hCeq, ← hs_eq]; congr 2; omega
      · right; right; right
        let ds2 := (s.val + 6 * t - a2.val) % (6 * t)
        have hs2_eq : idx ht (a2.val + ds2) = s := idx_add_dist ht a2 s
        have hds2_eq : ds2 = ds - d1 := by
          have ha2_eq : idx ht (a1.val + d1) = a2 := idx_add_dist ht a1 a2
          have hidx2 : idx ht (a2.val + (ds - d1)) = s := by
            rw [← hs_eq]
            apply Fin.ext; rw [← ha2_eq]
            change ((a1.val + d1) % (6 * t) + (ds - d1)) % (6 * t) = (a1.val + ds) % (6 * t)
            rw [Nat.mod_add_mod]; congr 1; omega
          exact idx_inj_range ht a2 (le_refl _) (Nat.mod_lt _ (by omega)) (by omega) (hs2_eq.trans hidx2.symm)
        have hds2_ge : L a2 ≤ ds2 := by
          rcases hL_spec a2 ha2Def hdw2 with ⟨hL1, _, _, _⟩ | ⟨hL3, _, _, _, _, _, _, h1n, h2n⟩
          · rw [hL1]; by_contra h0'; have hd0 : ds2 = 0 := by omega
            rw [hd0, add_zero, idx_self] at hs2_eq; exact hs2 hs2_eq.symm
          · rw [hL3]; by_contra hlt3
            have hcases : ds2 = 0 ∨ ds2 = 1 ∨ ds2 = 2 := by omega
            rcases hcases with hd0 | hd1 | hd2
            · rw [hd0, add_zero, idx_self] at hs2_eq; exact hs2 hs2_eq.symm
            · rw [hd1] at hs2_eq; exact h1n (hs2_eq ▸ hsSt)
            · rw [hd2] at hs2_eq; exact h2n (hs2_eq ▸ hsSt)
        have hev_ds2 : (ds2 - L a2) % 2 = 0 := by
          by_contra hodd
          let q := (ds2 - L a2) / 2
          obtain ⟨hs', _, _⟩ := hseg2.2.2 q (by omega)
          have hps' : prv ht s ∈ S := by
            have : prv ht s = idx ht (a2.val + L a2 + 2 * q) := by
              rw [← hs2_eq, show a2.val + ds2 = (a2.val + L a2 + 2 * q) + 1 by omega, ← nxt_idx, prv_nxt]
            rwa [this]
          exact hps hps'
        refine ⟨(ds2 - L a2) / 2, by omega, ?_⟩
        rw [hCeq, ← hs2_eq]; congr 2; omega
    have hboth : LinearMap.range incEven ≤ hSpace ht S ∧ LinearMap.range incOdd ≤ hSpace ht S := by
      rcases hL_spec a1 ha1Def hdw1 with ⟨hL1, ha1nS, _, _⟩ | ⟨hL1, ha1S, _, harc1, _, _, _, _, _⟩ <;>
      rcases hL_spec a2 ha2Def hdw2 with ⟨hL2, ha2nS, _, _⟩ | ⟨hL2, ha2S, _, harc2, _, _, _, _, _⟩
      · refine runs_sub1_two_gaps ht hg h0 h1 (a1 := a1) (a2 := a2) (k1 := k1) (k2 := k2)
          (by rw [hL1] at hpar_rel; omega)
          (by simpa [hL1] using hsolo1) (by simpa [hL2] using hsolo2) ?_
        intro C hC
        rcases hP_decomp C hC with ⟨h, _⟩ | ⟨h, _⟩ | h | h
        · exact (ha1nS h).elim
        · exact (ha2nS h).elim
        · left; simpa [hL1] using h
        · right; simpa [hL2] using h
      · refine runs_sub1_run_gap ht ht2 hg (a1 := a2) (a2 := a1) (k1 := k2) (k2 := k1) ha2S harc2
          (by rw [hL1] at hpar_rel; omega)
          (by rw [hL1] at h2k1 hL1_le; rw [hL2] at h2k2 hL2_le; omega)
          (fun hk1 => by
            have hd1_eq : d1 = 3 := by rw [hL1] at h2k1 hL1_le; omega
            have hy : idx ht (a1.val + d1) = a2 := idx_add_dist ht a1 a2
            rwa [hd1_eq] at hy)
          (by simpa [hL2] using hsolo2) (by simpa [hL1] using hsolo1) ?_
        intro C hC
        rcases hP_decomp C hC with ⟨h, _⟩ | ⟨_, h⟩ | h | h
        · exact (ha1nS h).elim
        · exact Or.inl h
        · right; right; simpa [hL1] using h
        · right; left; simpa [hL2] using h
      · refine runs_sub1_run_gap ht ht2 hg (a1 := a1) (a2 := a2) (k1 := k1) (k2 := k2) ha1S harc1
          (by rw [hL1] at hpar_rel; omega)
          (by rw [hL1] at h2k1 hL1_le; rw [hL2] at h2k2 hL2_le; omega)
          (fun hk2 => by
            have hd2_eq : d2 = 3 := by rw [hL2] at h2k2 hL2_le; omega
            have hy : idx ht (a2.val + d2) = a1 := idx_add_dist ht a2 a1
            rwa [hd2_eq] at hy)
          (by simpa [hL1] using hsolo1) (by simpa [hL2] using hsolo2) ?_
        intro C hC
        rcases hP_decomp C hC with ⟨_, h⟩ | ⟨h, _⟩ | h | h
        · exact Or.inl h
        · exact (ha2nS h).elim
        · right; left; simpa [hL1] using h
        · right; right; simpa [hL2] using h
      · have hk12 : k1 + k2 = 3 * t - 3 := by
          rw [hL1] at h2k1 hL1_le; rw [hL2] at h2k2 hL2_le; omega
        by_cases hk2_2 : 2 ≤ k2
        · exact runs_sub1_two_runs_half ht (a1 := a1) (a2 := a2) (k1 := k1) (k2 := k2) ha1S ha2S harc1 harc2
            (by rw [hL1] at hpar_rel; omega) hk2_2
            (fun hk0 => by
              have hd1_eq : d1 = 3 := by rw [hL1] at h2k1 hL1_le; omega
              have hy : idx ht (a1.val + d1) = a2 := idx_add_dist ht a1 a2
              rwa [hd1_eq] at hy)
            (fun k hk => by simpa [hL1] using (hsolo1 k hk).2)
            (fun k hk => by simpa [hL2] using (hsolo2 k hk).2)
        · have hk1_2 : 2 ≤ k1 := by omega
          exact runs_sub1_two_runs_half ht (a1 := a2) (a2 := a1) (k1 := k2) (k2 := k1) ha2S ha1S harc2 harc1
            (by rw [hL1] at hpar_rel; omega) hk1_2
            (fun hk0 => by
              have hd2_eq : d2 = 3 := by rw [hL2] at h2k2 hL2_le; omega
              have hy : idx ht (a2.val + d2) = a1 := idx_add_dist ht a2 a1
              rwa [hd2_eq] at hy)
            (fun k hk => by simpa [hL2] using (hsolo2 k hk).2)
            (fun k hk => by simpa [hL1] using (hsolo1 k hk).2)
    exact finrank_eq_four_of_both_lanes hboth.1 hboth.2

lemma runs_a2_case_pure_even {S : Finset (Fin (6 * t))} (ht3 : 3 ≤ t) (hS : S ≠ Finset.univ)
    (h1 : 0 < sitesOf S 1) (hr : (pcs (nxt ht) S).card = 3 * t - 2)
    (hVeq : hSpace ht S = LinearMap.range incEven)
    (hdef : ∑ C ∈ pcs (nxt ht) S, (C.card - 1) ≤ 4) : False := by
  set P := pcs (nxt ht) S
  obtain ⟨i1, hi1⟩ := Finset.card_pos.mp h1
  obtain ⟨hi1S, hi1p⟩ := Finset.mem_filter.mp hi1
  let Cstar := cc (nxt ht) S i1
  have hCstarP : Cstar ∈ P := Finset.mem_image_of_mem _ hi1S
  obtain ⟨s, _, _, harc, _, hlt, hout⟩ := comp_arc ht hS hCstarP
  have hod0 : oddProj (hSum Cstar) = 0 := by
    have hmem : hSum Cstar ∈ LinearMap.range incEven := hVeq ▸ mem_hSpace ht hCstarP
    obtain ⟨u, hu⟩ := hmem
    rw [← hu, oddProj_incEven]
  have hge5 : 5 ≤ Cstar.card := by
    have hne1 : Cstar.card ≠ 1 := by
      intro hc1
      have hCeq : Cstar = {i1} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨selfMem (nxt ht) S hi1S, fun j hj => Finset.card_le_one_iff.mp hc1.le hj (selfMem (nxt ht) S hi1S)⟩
      rw [hCeq, hSum, Finset.sum_singleton, hVec_eq_incOdd hi1p, oddProj_incOdd] at hod0
      exact col2_ne_zero _ hod0
    rw [harc, hSum_arc ht s (by omega), arcSum_oddProj_zero_iff] at hod0
    omega
  have hcard5 : Cstar.card = 5 := by
    have h1' := Finset.single_le_sum (fun C _ => Nat.zero_le (C.card - 1)) hCstarP
    omega
  have hsp : s.val % 2 = 1 := by
    rw [harc, hcard5, hSum_arc ht s (by omega), arcSum_oddProj_zero_iff] at hod0
    omega
  have hsum_eq : ∑ C ∈ P, (C.card + 1) = 6 * t := by
    have h1' : ∑ C ∈ P, (C.card + 1) = ∑ C ∈ P, (C.card - 1) + 2 * P.card := by
      have : ∑ C ∈ P, (C.card + 1) = ∑ C ∈ P, ((C.card - 1) + 2) :=
        Finset.sum_congr rfl fun C hC => by
          have := Finset.card_pos.mpr (populated (nxt ht) S hC); omega
      rw [this, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]; ring
    have h2' := Finset.single_le_sum (fun C _ => Nat.zero_le (C.card - 1)) hCstarP
    have htot : ∑ C ∈ P, (C.card + 1) ≤ 6 * t := sum_halo_le ht hS
    omega
  have hall1 : ∀ C ∈ P, C ≠ Cstar → C.card = 1 := by
    intro C hCP hne
    have hsplit := Finset.add_sum_erase P (fun D => D.card - 1) hCstarP
    have hle' := Finset.single_le_sum (fun D _ => Nat.zero_le (D.card - 1))
      (Finset.mem_erase.mpr ⟨hne, hCP⟩)
    have hpos' := Finset.card_pos.mpr (populated (nxt ht) S hCP)
    omega
  have huniv : P.biUnion (halo (nxt ht)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_biUnion (separate (nxt ht) S (ninj ht))]
    have : ∑ C ∈ P, (halo (nxt ht) C).card = ∑ C ∈ P, (C.card + 1) :=
      Finset.sum_congr rfl fun C hC => halo_card_eq ht hS hC
    rw [this, hsum_eq, Fintype.card_fin]
  let y := idx ht (s.val + 6)
  have hpy : prv ht y ∉ S := by
    have e : prv ht y = idx ht (s.val + 5) := by
      dsimp only [y]
      rw [show s.val + 6 = (s.val + 5) + 1 by omega, ← nxt_idx, prv_nxt]
    rw [e, ← hcard5]; exact hout
  have hyS : y ∈ S := by
    have hm : y ∈ P.biUnion (halo (nxt ht)) := huniv.symm ▸ Finset.mem_univ _
    rw [mem_biUnion_halo_iff] at hm
    rcases hm with h | h
    · exact h
    · exact (hpy h).elim
  let D := cc (nxt ht) S y
  have hDP : D ∈ P := Finset.mem_image_of_mem _ hyS
  have hDne : D ≠ Cstar := by
    intro heq
    have hyC : y ∈ Cstar := heq ▸ selfMem (nxt ht) S hyS
    rw [harc, hcard5, mem_arc_iff] at hyC
    obtain ⟨k, hk, hkeq⟩ := hyC
    have := idx_inj_range ht s (le_refl _) (by omega) (by omega) hkeq
    omega
  have hD1 : D.card = 1 := hall1 D hDP hDne
  have hDeq : D = {y} := Finset.eq_singleton_iff_unique_mem.mpr
    ⟨selfMem (nxt ht) S hyS, fun j hj => Finset.card_le_one_iff.mp hD1.le hj (selfMem (nxt ht) S hyS)⟩
  have hyp : y.val % 2 = 1 := by dsimp only [y]; rw [idx_mod2]; omega
  have hmem : hSum D ∈ LinearMap.range incEven := hVeq ▸ mem_hSpace ht hDP
  obtain ⟨u, hu⟩ := hmem
  have := congrArg oddProj hu
  rw [oddProj_incEven, hDeq, hSum, Finset.sum_singleton, hVec_eq_incOdd hyp, oddProj_incOdd] at this
  exact col2_ne_zero _ this.symm

lemma runs_a2_case_pure_odd {S : Finset (Fin (6 * t))} (ht3 : 3 ≤ t) (hS : S ≠ Finset.univ)
    (h0 : 0 < sitesOf S 0) (hr : (pcs (nxt ht) S).card = 3 * t - 2)
    (hVeq : hSpace ht S = LinearMap.range incOdd)
    (hdef : ∑ C ∈ pcs (nxt ht) S, (C.card - 1) ≤ 4) : False := by
  set P := pcs (nxt ht) S
  obtain ⟨i0, hi0⟩ := Finset.card_pos.mp h0
  obtain ⟨hi0S, hi0p⟩ := Finset.mem_filter.mp hi0
  let Cstar := cc (nxt ht) S i0
  have hCstarP : Cstar ∈ P := Finset.mem_image_of_mem _ hi0S
  obtain ⟨s, _, _, harc, _, hlt, hout⟩ := comp_arc ht hS hCstarP
  have hev0 : evenProj (hSum Cstar) = 0 := by
    have hmem : hSum Cstar ∈ LinearMap.range incOdd := hVeq ▸ mem_hSpace ht hCstarP
    obtain ⟨u, hu⟩ := hmem
    rw [← hu, evenProj_incOdd]
  have hge5 : 5 ≤ Cstar.card := by
    have hne1 : Cstar.card ≠ 1 := by
      intro hc1
      have hCeq : Cstar = {i0} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨selfMem (nxt ht) S hi0S, fun j hj => Finset.card_le_one_iff.mp hc1.le hj (selfMem (nxt ht) S hi0S)⟩
      rw [hCeq, hSum, Finset.sum_singleton, hVec_eq_incEven hi0p, evenProj_incEven] at hev0
      exact col2_ne_zero _ hev0
    rw [harc, hSum_arc ht s (by omega), arcSum_evenProj_zero_iff] at hev0
    omega
  have hcard5 : Cstar.card = 5 := by
    have h1' := Finset.single_le_sum (fun C _ => Nat.zero_le (C.card - 1)) hCstarP
    omega
  have hsp : s.val % 2 = 0 := by
    rw [harc, hcard5, hSum_arc ht s (by omega), arcSum_evenProj_zero_iff] at hev0
    omega
  have hsum_eq : ∑ C ∈ P, (C.card + 1) = 6 * t := by
    have h1' : ∑ C ∈ P, (C.card + 1) = ∑ C ∈ P, (C.card - 1) + 2 * P.card := by
      have : ∑ C ∈ P, (C.card + 1) = ∑ C ∈ P, ((C.card - 1) + 2) :=
        Finset.sum_congr rfl fun C hC => by
          have := Finset.card_pos.mpr (populated (nxt ht) S hC); omega
      rw [this, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]; ring
    have h2' := Finset.single_le_sum (fun C _ => Nat.zero_le (C.card - 1)) hCstarP
    have htot : ∑ C ∈ P, (C.card + 1) ≤ 6 * t := sum_halo_le ht hS
    omega
  have hall1 : ∀ C ∈ P, C ≠ Cstar → C.card = 1 := by
    intro C hCP hne
    have hsplit := Finset.add_sum_erase P (fun D => D.card - 1) hCstarP
    have hle' := Finset.single_le_sum (fun D _ => Nat.zero_le (D.card - 1))
      (Finset.mem_erase.mpr ⟨hne, hCP⟩)
    have hpos' := Finset.card_pos.mpr (populated (nxt ht) S hCP)
    omega
  have huniv : P.biUnion (halo (nxt ht)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_biUnion (separate (nxt ht) S (ninj ht))]
    have : ∑ C ∈ P, (halo (nxt ht) C).card = ∑ C ∈ P, (C.card + 1) :=
      Finset.sum_congr rfl fun C hC => halo_card_eq ht hS hC
    rw [this, hsum_eq, Fintype.card_fin]
  let y := idx ht (s.val + 6)
  have hpy : prv ht y ∉ S := by
    have e : prv ht y = idx ht (s.val + 5) := by
      dsimp only [y]
      rw [show s.val + 6 = (s.val + 5) + 1 by omega, ← nxt_idx, prv_nxt]
    rw [e, ← hcard5]; exact hout
  have hyS : y ∈ S := by
    have hm : y ∈ P.biUnion (halo (nxt ht)) := huniv.symm ▸ Finset.mem_univ _
    rw [mem_biUnion_halo_iff] at hm
    rcases hm with h | h
    · exact h
    · exact (hpy h).elim
  let D := cc (nxt ht) S y
  have hDP : D ∈ P := Finset.mem_image_of_mem _ hyS
  have hDne : D ≠ Cstar := by
    intro heq
    have hyC : y ∈ Cstar := heq ▸ selfMem (nxt ht) S hyS
    rw [harc, hcard5, mem_arc_iff] at hyC
    obtain ⟨k, hk, hkeq⟩ := hyC
    have := idx_inj_range ht s (le_refl _) (by omega) (by omega) hkeq
    omega
  have hD1 : D.card = 1 := hall1 D hDP hDne
  have hDeq : D = {y} := Finset.eq_singleton_iff_unique_mem.mpr
    ⟨selfMem (nxt ht) S hyS, fun j hj => Finset.card_le_one_iff.mp hD1.le hj (selfMem (nxt ht) S hyS)⟩
  have hyp : y.val % 2 = 0 := by dsimp only [y]; rw [idx_mod2]; omega
  have hmem : hSum D ∈ LinearMap.range incOdd := hVeq ▸ mem_hSpace ht hDP
  obtain ⟨u, hu⟩ := hmem
  have := congrArg evenProj hu
  rw [evenProj_incOdd, hDeq, hSum, Finset.sum_singleton, hVec_eq_incEven hyp, evenProj_incEven] at this
  exact col2_ne_zero _ this.symm

lemma runs_a2_case_11 {S : Finset (Fin (6 * t))} (ht3 : 3 ≤ t) (hS : S ≠ Finset.univ)
    {we wo : V2} (hwe0 : we ≠ 0) (hwo0 : wo ≠ 0)
    (hV_proj : ∀ v ∈ hSpace ht S, (evenProj v = 0 ∨ evenProj v = we) ∧ (oddProj v = 0 ∨ oddProj v = wo))
    (hP_part : (pcs (nxt ht) S |>.filter (·.card = 1)).card +
      (pcs (nxt ht) S |>.filter (·.card = 2)).card +
      (pcs (nxt ht) S |>.filter (·.card = 3)).card +
      (pcs (nxt ht) S |>.filter (4 ≤ ·.card)).card = 3 * t - 2)
    (hP_def : (pcs (nxt ht) S |>.filter (·.card = 2)).card +
      2 * (pcs (nxt ht) S |>.filter (·.card = 3)).card +
      3 * (pcs (nxt ht) S |>.filter (4 ≤ ·.card)).card ≤ 4) : False := by
  set P := pcs (nxt ht) S
  set P1 := P.filter (fun C => C.card = 1)
  set P2 := P.filter (fun C => C.card = 2)
  set P3 := P.filter (fun C => C.card = 3)
  set P4 := P.filter (fun C => 4 ≤ C.card)
  let G := Finset.univ.filter (fun i : Fin (6 * t) =>
    (i.val % 2 = 0 ∧ col2 (i.val / 2) = we) ∨ (i.val % 2 = 1 ∧ col2 (i.val / 2) = wo))
  have hG_card : G.card = 2 * t := by
    let Ge := Finset.univ.filter (fun i : Fin (6 * t) => i.val % 2 = 0 ∧ col2 (i.val / 2) = we)
    let Go := Finset.univ.filter (fun i : Fin (6 * t) => i.val % 2 = 1 ∧ col2 (i.val / 2) = wo)
    have hdis : Disjoint Ge Go := Finset.disjoint_filter.mpr fun _ _ a b => by omega
    have hun : Ge ∪ Go = G := by ext i; simp [Ge, Go, G]
    rw [← hun, Finset.card_union_of_disjoint hdis,
      card_lane_col_eq ht 0 (by decide) we hwe0,
      card_lane_col_eq ht 1 (by decide) wo hwo0]
    omega
  have hch1 : ∀ C ∈ P1, 1 ≤ (C ∩ G).card := by
    intro C hC1
    obtain ⟨hCP, hc1⟩ := Finset.mem_filter.mp hC1
    obtain ⟨i, hiC⟩ := populated (nxt ht) S hCP
    have hCeq : C = {i} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hiC, fun j hj => Finset.card_le_one_iff.mp hc1.le hj hiC⟩
    have hpv := hV_proj (hSum C) (mem_hSpace ht hCP)
    rw [hCeq, hSum, Finset.sum_singleton] at hpv
    have hiG : i ∈ G := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      by_cases hp : i.val % 2 = 0
      · left; refine ⟨hp, ?_⟩
        rw [hVec_eq_incEven hp, evenProj_incEven] at hpv
        rcases hpv.1 with hz | heq; exact (col2_ne_zero _ hz).elim; exact heq
      · right; have ho : i.val % 2 = 1 := by omega
        refine ⟨ho, ?_⟩
        rw [hVec_eq_incOdd ho, oddProj_incOdd] at hpv
        rcases hpv.2 with hz | heq; exact (col2_ne_zero _ hz).elim; exact heq
    exact Finset.card_pos.mpr ⟨i, Finset.mem_inter.mpr ⟨hiC, hiG⟩⟩
  have hch2 : ∀ C ∈ P2, 2 ≤ (C ∩ G).card := by
    intro C hC2
    obtain ⟨hCP, hc2⟩ := Finset.mem_filter.mp hC2
    obtain ⟨s, _, _, harc, _, hlt, _⟩ := comp_arc ht hS hCP
    have hpv := hV_proj (hSum C) (mem_hSpace ht hCP)
    have hs2 : hSum C = hPat s.val + hPat (s.val + 1) := by
      rw [harc, hc2, hSum_arc ht s (by omega), arcSum_two]
    have h0in : idx ht (s.val + 0) ∈ C := by
      rw [harc, hc2]; exact (mem_arc_iff ht s 2 _).mpr ⟨0, by decide, rfl⟩
    have h1in : idx ht (s.val + 1) ∈ C := by
      rw [harc, hc2]; exact (mem_arc_iff ht s 2 _).mpr ⟨1, by decide, rfl⟩
    have hne01 : idx ht (s.val + 0) ≠ idx ht (s.val + 1) := fun h => by
      have := idx_inj_range ht s (by omega) (by decide : 0 < 2) (by decide : 1 < 2) h; omega
    have hbothG : idx ht (s.val + 0) ∈ G ∧ idx ht (s.val + 1) ∈ G := by
      rw [hs2] at hpv
      by_cases hsp : s.val % 2 = 0
      · rw [hPat_eq_incEven hsp, hPat_eq_incOdd (by omega)] at hpv
        simp only [map_add, evenProj_incEven, evenProj_incOdd, oddProj_incEven, oddProj_incOdd, add_zero, zero_add] at hpv
        have h0G : idx ht (s.val + 0) ∈ G := by
          rw [add_zero, idx_self]
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨hsp, ?_⟩⟩
          rcases hpv.1 with hz | heq; exact (col2_ne_zero _ hz).elim; exact heq
        have h1G : idx ht (s.val + 1) ∈ G := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨by rw [idx_mod2]; omega, ?_⟩⟩
          rw [← col2_mod3, idx_div2_mod3, col2_mod3]
          rcases hpv.2 with hz | heq; exact (col2_ne_zero _ hz).elim; exact heq
        exact ⟨h0G, h1G⟩
      · rw [hPat_eq_incOdd (by omega), hPat_eq_incEven (by omega)] at hpv
        simp only [map_add, evenProj_incEven, evenProj_incOdd, oddProj_incEven, oddProj_incOdd, add_zero, zero_add] at hpv
        have h0G : idx ht (s.val + 0) ∈ G := by
          rw [add_zero, idx_self]
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨by omega, ?_⟩⟩
          rcases hpv.2 with hz | heq; exact (col2_ne_zero _ hz).elim; exact heq
        have h1G : idx ht (s.val + 1) ∈ G := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨by rw [idx_mod2]; omega, ?_⟩⟩
          rw [← col2_mod3, idx_div2_mod3, col2_mod3]
          rcases hpv.1 with hz | heq; exact (col2_ne_zero _ hz).elim; exact heq
        exact ⟨h0G, h1G⟩
    calc 2 = ({idx ht (s.val + 0), idx ht (s.val + 1)} : Finset _).card := (Finset.card_pair hne01).symm
      _ ≤ (C ∩ G).card := Finset.card_le_card (Finset.insert_subset (Finset.mem_inter.mpr ⟨h0in, hbothG.1⟩)
          (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨h1in, hbothG.2⟩)))
  have hch3 : ∀ C ∈ P3, 1 ≤ (C ∩ G).card := by
    intro C hC3
    obtain ⟨hCP, hc3⟩ := Finset.mem_filter.mp hC3
    obtain ⟨s, _, _, harc, _, hlt, _⟩ := comp_arc ht hS hCP
    have hpv := hV_proj (hSum C) (mem_hSpace ht hCP)
    have hs3 : hSum C = hPat s.val + hPat (s.val + 1) + hPat (s.val + 2) := by
      rw [harc, hc3, hSum_arc ht s (by omega), arcSum_three]
    have h1in : idx ht (s.val + 1) ∈ C := by
      rw [harc, hc3]; exact (mem_arc_iff ht s 3 _).mpr ⟨1, by decide, rfl⟩
    have h1G : idx ht (s.val + 1) ∈ G := by
      rw [hs3] at hpv
      by_cases hsp : s.val % 2 = 0
      · rw [hPat_eq_incEven hsp, hPat_eq_incOdd (by omega), hPat_eq_incEven (by omega)] at hpv
        simp only [map_add, oddProj_incEven, oddProj_incOdd, zero_add, add_zero] at hpv
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨by rw [idx_mod2]; omega, ?_⟩⟩
        rw [← col2_mod3, idx_div2_mod3, col2_mod3]
        rcases hpv.2 with hz | heq; exact (col2_ne_zero _ hz).elim; exact heq
      · rw [hPat_eq_incOdd (by omega), hPat_eq_incEven (by omega), hPat_eq_incOdd (by omega)] at hpv
        simp only [map_add, evenProj_incOdd, evenProj_incEven, zero_add, add_zero] at hpv
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨by rw [idx_mod2]; omega, ?_⟩⟩
        rw [← col2_mod3, idx_div2_mod3, col2_mod3]
        rcases hpv.1 with hz | heq; exact (col2_ne_zero _ hz).elim; exact heq
    exact Finset.card_pos.mpr ⟨idx ht (s.val + 1), Finset.mem_inter.mpr ⟨h1in, h1G⟩⟩
  let P123 := P1 ∪ P2 ∪ P3
  have hd12 : Disjoint P1 P2 := Finset.disjoint_filter.mpr fun _ _ a b => by omega
  have hd123 : Disjoint (P1 ∪ P2) P3 :=
    Finset.disjoint_left.mpr fun C h12 h3 => by
      simp only [P1, P2, P3, Finset.mem_union, Finset.mem_filter] at h12 h3; omega
  have hP123_dis : (↑P123 : Set (Finset (Fin (6 * t)))).PairwiseDisjoint (fun C => C ∩ G) := by
    intro C hC D hD hne
    have hCP : C ∈ P := by
      simp only [P123, P1, P2, P3, Finset.mem_coe, Finset.mem_union, Finset.mem_filter] at hC
      rcases hC with (⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩ <;> exact h
    have hDP : D ∈ P := by
      simp only [P123, P1, P2, P3, Finset.mem_coe, Finset.mem_union, Finset.mem_filter] at hD
      rcases hD with (⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩ <;> exact h
    exact Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left
      (pcs_pairwiseDisjoint (nxt ht) S hCP hDP hne)
  have hsum123 : P1.card + 2 * P2.card + P3.card ≤ (P123.biUnion (fun C => C ∩ G)).card := by
    rw [Finset.card_biUnion hP123_dis]
    dsimp only [P123]
    rw [Finset.sum_union hd123, Finset.sum_union hd12]
    have s1 : P1.card ≤ ∑ C ∈ P1, (C ∩ G).card := by
      have := Finset.sum_le_sum hch1; simpa using this
    have s2 : 2 * P2.card ≤ ∑ C ∈ P2, (C ∩ G).card := by
      have := Finset.sum_le_sum hch2; simp only [Finset.sum_const, smul_eq_mul] at this; omega
    have s3 : P3.card ≤ ∑ C ∈ P3, (C ∩ G).card := by
      have := Finset.sum_le_sum hch3; simpa using this
    omega
  have hbi_sub : P123.biUnion (fun C => C ∩ G) ⊆ G := by
    intro x hx
    obtain ⟨_, _, hx'⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_inter.mp hx').2
  by_cases hP4_0 : P4.card = 0
  · have hleG := Finset.card_le_card hbi_sub
    omega
  · have hP4_1 : P4.card = 1 := by omega
    obtain ⟨Cstar, hCstar4⟩ := Finset.card_pos.mp (by omega : 0 < P4.card)
    obtain ⟨hCstarP, hge4⟩ := Finset.mem_filter.mp hCstar4
    obtain ⟨s, _, hps, harc, _, hlt, hout⟩ := comp_arc ht hS hCstarP
    let B := arc ht (prv ht s) 6
    have hBG_card : (B ∩ G).card = 2 := by
      have heq : B ∩ G = B.filter (fun i : Fin (6 * t) =>
          (i.val % 2 = 0 ∧ col2 (i.val / 2) = we) ∨ (i.val % 2 = 1 ∧ col2 (i.val / 2) = wo)) := by
        ext i; simp [G]
      rw [heq]
      exact card_six_window_hits ht (prv ht s) we wo hwe0 hwo0
    have hB_dis : Disjoint (P123.biUnion (fun C => C ∩ G)) (B ∩ G) := by
      apply Finset.disjoint_left.mpr
      intro x hx1 hx2
      obtain ⟨C, hC123, hxCG⟩ := Finset.mem_biUnion.mp hx1
      have hxC : x ∈ C := (Finset.mem_inter.mp hxCG).1
      have hxB : x ∈ B := (Finset.mem_inter.mp hx2).1
      have hCP : C ∈ P := by
        simp only [P123, P1, P2, P3, Finset.mem_union, Finset.mem_filter] at hC123
        rcases hC123 with (⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩ <;> exact h
      have hCne : C ≠ Cstar := by
        intro eq
        rw [eq] at hC123
        simp only [P123, P1, P2, P3, Finset.mem_union, Finset.mem_filter] at hC123
        omega
      have hxS : x ∈ S := (center (nxt ht) S hCP hxC).1
      have hxnCs : x ∉ Cstar := Finset.disjoint_left.mp
        (pcs_pairwiseDisjoint (nxt ht) S hCP hCstarP hCne) hxC
      obtain ⟨k, hk, hkx⟩ := (mem_arc_iff ht (prv ht s) 6 x).mp hxB
      have hshift : ∀ j, idx ht ((prv ht s).val + (j + 1)) = idx ht (s.val + j) := fun j => by
        apply Fin.ext
        change ((prv ht s).val + (j + 1)) % (6 * t) = (s.val + j) % (6 * t)
        rw [prv_val]
        have hs := s.isLt
        split_ifs with h0
        · rw [h0, zero_add]
          have e : 6 * t - 1 + (j + 1) = j + 6 * t := by omega
          rw [e, Nat.add_mod_right]
        · congr 1; omega
      cases k with
      | zero =>
        rw [add_zero, idx_self] at hkx
        exact hps (hkx ▸ hxS)
      | succ k =>
        rw [hshift k] at hkx
        by_cases hk4 : k < Cstar.card
        · apply hxnCs
          rw [harc, mem_arc_iff]
          exact ⟨k, hk4, hkx⟩
        · have hk4eq : k = 4 := by omega
          have hcs4 : Cstar.card = 4 := by omega
          rw [hk4eq, ← hcs4] at hkx
          exact hout (hkx ▸ hxS)
    have hun_sub : P123.biUnion (fun C => C ∩ G) ∪ (B ∩ G) ⊆ G :=
      Finset.union_subset hbi_sub Finset.inter_subset_right
    have hleG := Finset.card_le_card hun_sub
    rw [Finset.card_union_of_disjoint hB_dis, hBG_card] at hleG
    omega

lemma runs_eq_a_sub_two {S : Finset (Fin (6 * t))} (ht3 : 3 ≤ t) (hS : S ≠ Finset.univ)
    (h0 : 0 < sitesOf S 0) (h1 : 0 < sitesOf S 1)
    (hr : (pcs (nxt ht) S).card = 3 * t - 2) : 3 ≤ rk ht S := by
  by_contra hlt3
  have hrk2 : rk ht S ≤ 2 := by omega
  set V := hSpace ht S
  set P := pcs (nxt ht) S
  let Ve : Submodule F2 V2 := V.comap incEven
  let Vo : Submodule F2 V2 := V.comap incOdd
  have hVe_map : Ve.map incEven = V ⊓ LinearMap.range incEven := by
    ext v; simp [Ve, Submodule.mem_map, LinearMap.mem_range]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨hu, u, rfl⟩
    · rintro ⟨hv, u, rfl⟩; exact ⟨u, hv, rfl⟩
  have hVo_map : Vo.map incOdd = V ⊓ LinearMap.range incOdd := by
    ext v; simp [Vo, Submodule.mem_map, LinearMap.mem_range]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨hu, u, rfl⟩
    · rintro ⟨hv, u, rfl⟩; exact ⟨u, hv, rfl⟩
  have hVe_rk : Module.finrank F2 Ve = Module.finrank F2 (Ve.map incEven) := by
    have hrng : LinearMap.range (incEven.comp Ve.subtype) = Ve.map incEven := by
      ext v; simp [LinearMap.mem_range, Submodule.mem_map]
    rw [← hrng]
    exact (LinearMap.finrank_range_of_inj (fun x y h => Subtype.ext (incEven_inj h))).symm
  have hVo_rk : Module.finrank F2 Vo = Module.finrank F2 (Vo.map incOdd) := by
    have hrng : LinearMap.range (incOdd.comp Vo.subtype) = Vo.map incOdd := by
      ext v; simp [LinearMap.mem_range, Submodule.mem_map]
    rw [← hrng]
    exact (LinearMap.finrank_range_of_inj (fun x y h => Subtype.ext (incOdd_inj h))).symm
  have hinf : Ve.map incEven ⊓ Vo.map incOdd = ⊥ := by
    rw [hVe_map, hVo_map, Submodule.eq_bot_iff]
    intro v hv
    have : v ∈ LinearMap.range incEven ⊓ LinearMap.range incOdd := ⟨hv.1.2, hv.2.2⟩
    rwa [range_incEven_inf_incOdd] at this
  have hsup_le : Ve.map incEven ⊔ Vo.map incOdd ≤ V := by
    rw [hVe_map, hVo_map]
    exact sup_le inf_le_left inf_le_left
  have hde_do : Module.finrank F2 Ve + Module.finrank F2 Vo ≤ 2 := by
    have h1' := Submodule.finrank_sup_add_finrank_inf_eq (Ve.map incEven) (Vo.map incOdd)
    rw [hinf, finrank_bot, add_zero, ← hVe_rk, ← hVo_rk] at h1'
    have h2' : Module.finrank F2 ↥(Ve.map incEven ⊔ Vo.map incOdd) ≤ Module.finrank F2 V :=
      Submodule.finrank_mono hsup_le
    change Module.finrank F2 V ≤ 2 at hrk2
    omega
  set P1 := P.filter (fun C => C.card = 1)
  set P2 := P.filter (fun C => C.card = 2)
  set P3 := P.filter (fun C => C.card = 3)
  set P4 := P.filter (fun C => 4 ≤ C.card)
  have hdef_budget : ∑ C ∈ P, (C.card - 1) ≤ 4 := by
    have h1' : ∑ C ∈ P, (C.card + 1) = ∑ C ∈ P, (C.card - 1) + 2 * P.card := by
      have : ∑ C ∈ P, (C.card + 1) = ∑ C ∈ P, ((C.card - 1) + 2) :=
        Finset.sum_congr rfl fun C hC => by
          have := Finset.card_pos.mpr (populated (nxt ht) S hC); omega
      rw [this, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]; ring
    have htot : ∑ C ∈ P, (C.card + 1) ≤ 6 * t := sum_halo_le ht hS
    omega
  have hd12 : Disjoint P1 P2 := Finset.disjoint_filter.mpr fun _ _ a b => by omega
  have hd123 : Disjoint (P1 ∪ P2) P3 :=
    Finset.disjoint_left.mpr fun C h12 h3 => by
      simp only [P1, P2, P3, Finset.mem_union, Finset.mem_filter] at h12 h3; omega
  have hd1234 : Disjoint (P1 ∪ P2 ∪ P3) P4 :=
    Finset.disjoint_left.mpr fun C h123 h4 => by
      simp only [P1, P2, P3, P4, Finset.mem_union, Finset.mem_filter] at h123 h4; omega
  have hunP : P1 ∪ P2 ∪ P3 ∪ P4 = P := by
    ext C; simp only [P1, P2, P3, P4, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
    · intro hC
      have hpos := Finset.card_pos.mpr (populated (nxt ht) S hC)
      by_cases c1 : C.card = 1
      · exact Or.inl (Or.inl (Or.inl ⟨hC, c1⟩))
      by_cases c2 : C.card = 2
      · exact Or.inl (Or.inl (Or.inr ⟨hC, c2⟩))
      by_cases c3 : C.card = 3
      · exact Or.inl (Or.inr ⟨hC, c3⟩)
      exact Or.inr ⟨hC, by omega⟩
  have hP_part : P1.card + P2.card + P3.card + P4.card = 3 * t - 2 := by
    rw [← hr, ← hunP, Finset.card_union_of_disjoint hd1234, Finset.card_union_of_disjoint hd123,
      Finset.card_union_of_disjoint hd12]
  have hP_def : P2.card + 2 * P3.card + 3 * P4.card ≤ 4 := by
    have hsum := hdef_budget
    rw [← hunP, Finset.sum_union hd1234, Finset.sum_union hd123, Finset.sum_union hd12] at hsum
    have s2 : ∑ C ∈ P2, (C.card - 1) = P2.card := by
      have : ∑ C ∈ P2, (C.card - 1) = ∑ _ ∈ P2, 1 :=
        Finset.sum_congr rfl fun C hC => by have := (Finset.mem_filter.mp hC).2; omega
      simp [this]
    have s3 : ∑ C ∈ P3, (C.card - 1) = 2 * P3.card := by
      have : ∑ C ∈ P3, (C.card - 1) = ∑ _ ∈ P3, 2 :=
        Finset.sum_congr rfl fun C hC => by have := (Finset.mem_filter.mp hC).2; omega
      simp [this, mul_comm]
    have s4 : 3 * P4.card ≤ ∑ C ∈ P4, (C.card - 1) := by
      have : ∑ _ ∈ P4, 3 ≤ ∑ C ∈ P4, (C.card - 1) :=
        Finset.sum_le_sum fun C hC => by have := (Finset.mem_filter.mp hC).2; omega
      simp only [Finset.sum_const, smul_eq_mul] at this; omega
    omega
  have hno_even1 : Module.finrank F2 Ve = 0 → ∀ C ∈ P1, ∀ i ∈ C, i.val % 2 ≠ 0 := by
    intro h0e C hC1 i hiC hp0
    obtain ⟨hCP, hc1⟩ := Finset.mem_filter.mp hC1
    have hCeq : C = {i} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hiC, fun j hj => Finset.card_le_one_iff.mp hc1.le hj hiC⟩
    have hmem : col2 (i.val / 2) ∈ Ve := by
      show incEven (col2 (i.val / 2)) ∈ V
      rw [← hVec_eq_incEven hp0]
      simpa [hCeq, hSum] using mem_hSpace ht hCP
    exact col2_ne_zero _ (congrArg Subtype.val ((finrank_zero_iff_forall_zero.mp h0e) ⟨_, hmem⟩))
  have hno_odd1 : Module.finrank F2 Vo = 0 → ∀ C ∈ P1, ∀ i ∈ C, i.val % 2 ≠ 1 := by
    intro h0o C hC1 i hiC hp1
    obtain ⟨hCP, hc1⟩ := Finset.mem_filter.mp hC1
    have hCeq : C = {i} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hiC, fun j hj => Finset.card_le_one_iff.mp hc1.le hj hiC⟩
    have hmem : col2 (i.val / 2) ∈ Vo := by
      show incOdd (col2 (i.val / 2)) ∈ V
      rw [← hVec_eq_incOdd hp1]
      simpa [hCeq, hSum] using mem_hSpace ht hCP
    exact col2_ne_zero _ (congrArg Subtype.val ((finrank_zero_iff_forall_zero.mp h0o) ⟨_, hmem⟩))
  have hde_cases : Module.finrank F2 Ve = 0 ∨ Module.finrank F2 Ve = 1 ∨ Module.finrank F2 Ve = 2 := by omega
  have hdo_cases : Module.finrank F2 Vo = 0 ∨ Module.finrank F2 Vo = 1 ∨ Module.finrank F2 Vo = 2 := by omega
  rcases hde_cases with hde_eq | hde_eq | hde_eq <;> rcases hdo_cases with hdo_eq | hdo_eq | hdo_eq
  · have hP10 : P1 = ∅ := by
      ext C; simp only [Finset.notMem_empty, iff_false]
      intro hC1
      obtain ⟨i, hiC⟩ := populated (nxt ht) S (Finset.mem_filter.mp hC1).1
      by_cases hp : i.val % 2 = 0
      · exact hno_even1 hde_eq C hC1 i hiC hp
      · exact hno_odd1 hdo_eq C hC1 i hiC (by omega)
    rw [hP10, Finset.card_empty] at hP_part
    omega
  · have hP1_le : P1.card ≤ t := by
      obtain ⟨wo, hwo⟩ := submodule_le_one_eq_zero_or_w (show Module.finrank F2 Vo ≤ 1 by omega)
      have hwo0 : wo ≠ 0 := by
        intro hz
        have hbot : Vo = ⊥ := (Submodule.eq_bot_iff Vo).mpr fun u hu => by
          rcases hwo u hu with h | h; exact h; exact h.trans hz
        rw [hbot, finrank_bot] at hdo_eq; omega
      let T := Finset.univ.filter (fun i : Fin (6 * t) => i.val % 2 = 1 ∧ col2 (i.val / 2) = wo)
      have hT : T.card = t := card_lane_col_eq ht 1 (by decide) wo hwo0
      have hsub : P1.biUnion id ⊆ T := by
        intro i hi
        obtain ⟨C, hC1, hiC⟩ := Finset.mem_biUnion.mp hi
        obtain ⟨hCP, hc1⟩ := Finset.mem_filter.mp hC1
        have hp1 : i.val % 2 = 1 := by have := hno_even1 hde_eq C hC1 i hiC; omega
        have hCeq : C = {i} := Finset.eq_singleton_iff_unique_mem.mpr
          ⟨hiC, fun j hj => Finset.card_le_one_iff.mp hc1.le hj hiC⟩
        have hmem : col2 (i.val / 2) ∈ Vo := by
          show incOdd (col2 (i.val / 2)) ∈ V
          rw [← hVec_eq_incOdd hp1]
          simpa [hCeq, hSum] using mem_hSpace ht hCP
        rcases hwo _ hmem with hz | heq
        · exact (col2_ne_zero _ hz).elim
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp1, heq⟩
      have hcard_bi : (P1.biUnion id).card = P1.card := by
        rw [Finset.card_biUnion]
        · have : ∑ C ∈ P1, C.card = ∑ _ ∈ P1, 1 :=
            Finset.sum_congr rfl fun C hC => (Finset.mem_filter.mp hC).2
          simpa using this
        · intro C hC D hD hne
          exact pcs_pairwiseDisjoint (nxt ht) S (Finset.mem_filter.mp hC).1
            (Finset.mem_filter.mp hD).1 hne
      calc P1.card = (P1.biUnion id).card := hcard_bi.symm
        _ ≤ T.card := Finset.card_le_card hsub
        _ = t := hT
    have hP2_le : P2.card ≤ t := by
      let evV : V →ₗ[F2] V2 := evenProj.comp V.subtype
      have hker_ev : LinearMap.ker evV = (Vo.map incOdd).comap V.subtype := by
        ext ⟨v, hv⟩
        simp only [LinearMap.mem_ker, evV, LinearMap.comp_apply, Submodule.coe_subtype,
          Submodule.mem_comap, hVo_map, Submodule.mem_inf, LinearMap.mem_range]
        constructor
        · intro he0
          refine ⟨hv, oddProj v, ?_⟩
          have hd := v4_decomp v
          rw [he0, map_zero, zero_add] at hd
          exact hd.symm
        · rintro ⟨_, u, hu⟩
          rw [← hu, evenProj_incOdd]
      have hker_rk : Module.finrank F2 (LinearMap.ker evV) = 1 := by
        have hsub : Vo.map incOdd ≤ LinearMap.range V.subtype := by
          rw [Submodule.range_subtype, hVo_map]; exact inf_le_left
        have hrng : ((Vo.map incOdd).comap V.subtype).map V.subtype = Vo.map incOdd :=
          Submodule.map_comap_eq_of_le hsub
        rw [hker_ev]
        have := Submodule.finrank_map_subtype_eq V ((Vo.map incOdd).comap V.subtype)
        rw [hrng] at this
        have : Module.finrank F2 (Vo.map incOdd) = 1 := hVo_rk.symm.trans hdo_eq
        omega
      have hrng_rk : Module.finrank F2 (LinearMap.range evV) ≤ 1 := by
        have h3 := LinearMap.finrank_range_add_finrank_ker evV
        rw [hker_rk] at h3
        change Module.finrank F2 (LinearMap.range evV) + 1 = rk ht S at h3
        omega
      obtain ⟨we, hwe⟩ := submodule_le_one_eq_zero_or_w hrng_rk
      by_cases hwe0 : we = 0
      · have hP20 : P2 = ∅ := by
          ext C; simp only [Finset.notMem_empty, iff_false]
          intro hC2
          obtain ⟨hCP, hc2⟩ := Finset.mem_filter.mp hC2
          obtain ⟨s, _, _, harc, _, hlt, _⟩ := comp_arc ht hS hCP
          have hmem : evenProj (hSum C) ∈ LinearMap.range evV := ⟨⟨hSum C, mem_hSpace ht hCP⟩, rfl⟩
          have he0 : evenProj (hSum C) = 0 := by
            rcases hwe _ hmem with h | h; exact h; exact h.trans hwe0
          rw [harc, hc2, hSum_arc ht s (by omega), arcSum_evenProj_zero_iff] at he0; omega
        rw [hP20, Finset.card_empty]; omega
      · let T := Finset.univ.filter (fun i : Fin (6 * t) => i.val % 2 = 0 ∧ col2 (i.val / 2) = we)
        have hT : T.card = t := card_lane_col_eq ht 0 (by decide) we hwe0
        have hhit : ∀ C : ↥P2, ∃ i ∈ C.1, i ∈ T := by
          intro C
          obtain ⟨hCP, hc2⟩ := Finset.mem_filter.mp C.2
          obtain ⟨s, _, _, harc, _, hlt, _⟩ := comp_arc ht hS hCP
          have hmem : evenProj (hSum C.1) ∈ LinearMap.range evV := ⟨⟨hSum C.1, mem_hSpace ht hCP⟩, rfl⟩
          have heqW : evenProj (hSum C.1) = we := by
            rcases hwe _ hmem with h0' | h1'
            · rw [harc, hc2, hSum_arc ht s (by omega), arcSum_evenProj_zero_iff] at h0'; omega
            · exact h1'
          have hs2 : hSum C.1 = hPat s.val + hPat (s.val + 1) := by
            rw [harc, hc2, hSum_arc ht s (by omega), arcSum_two]
          by_cases hsp : s.val % 2 = 0
          · have hev : we = col2 (s.val / 2) := by
              rw [← heqW, hs2, hPat_eq_incEven hsp, hPat_eq_incOdd (by omega), map_add,
                evenProj_incEven, evenProj_incOdd, add_zero]
            refine ⟨idx ht (s.val + 0), ?_, ?_⟩
            · rw [harc, hc2]; exact (mem_arc_iff ht s 2 _).mpr ⟨0, by decide, rfl⟩
            · rw [add_zero, idx_self]
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsp, hev.symm⟩
          · have hev : we = col2 ((s.val + 1) / 2) := by
              rw [← heqW, hs2, hPat_eq_incOdd (by omega), hPat_eq_incEven (by omega), map_add,
                evenProj_incOdd, evenProj_incEven, zero_add]
            refine ⟨idx ht (s.val + 1), ?_, ?_⟩
            · rw [harc, hc2]; exact (mem_arc_iff ht s 2 _).mpr ⟨1, by decide, rfl⟩
            · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
              · rw [idx_mod2]; omega
              · rw [← col2_mod3, idx_div2_mod3, col2_mod3]; exact hev.symm
        choose f hfC hfT using hhit
        have hinj : Function.Injective (fun C : ↥P2 => (⟨f C, hfT C⟩ : ↥T)) := by
          intro C D eq
          have hfeq : f C = f D := congrArg Subtype.val eq
          by_contra hne
          have hdis' := pcs_pairwiseDisjoint (nxt ht) S
            (Finset.mem_filter.mp C.2).1 (Finset.mem_filter.mp D.2).1 (fun e => hne (Subtype.ext e))
          exact Finset.disjoint_left.mp hdis' (hfC C) (hfeq ▸ hfC D)
        have hle := Fintype.card_le_of_injective _ hinj
        simpa [hT] using hle
    omega
  · have hVeq : V = LinearMap.range incOdd := by
      have hle : Vo.map incOdd ≤ V := by rw [hVo_map]; exact inf_le_left
      have hVo2 : Module.finrank F2 (Vo.map incOdd) = 2 := hVo_rk.symm.trans hdo_eq
      have hrkV : Module.finrank F2 V = 2 := by
        have := Submodule.finrank_mono hle
        change Module.finrank F2 V ≤ 2 at hrk2
        omega
      have heq1 : Vo.map incOdd = V := Submodule.eq_of_le_of_finrank_eq hle (by omega)
      have hVoTop : Vo = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hdo_eq, Module.finrank_fin_fun])
      rw [← heq1, hVoTop, Submodule.map_top]
    exact runs_a2_case_pure_odd ht ht3 hS h0 hr hVeq hdef_budget
  · have hP1_le : P1.card ≤ t := by
      obtain ⟨we, hwe⟩ := submodule_le_one_eq_zero_or_w (show Module.finrank F2 Ve ≤ 1 by omega)
      have hwe0 : we ≠ 0 := by
        intro hz
        have hbot : Ve = ⊥ := (Submodule.eq_bot_iff Ve).mpr fun u hu => by
          rcases hwe u hu with h | h; exact h; exact h.trans hz
        rw [hbot, finrank_bot] at hde_eq; omega
      let T := Finset.univ.filter (fun i : Fin (6 * t) => i.val % 2 = 0 ∧ col2 (i.val / 2) = we)
      have hT : T.card = t := card_lane_col_eq ht 0 (by decide) we hwe0
      have hsub : P1.biUnion id ⊆ T := by
        intro i hi
        obtain ⟨C, hC1, hiC⟩ := Finset.mem_biUnion.mp hi
        obtain ⟨hCP, hc1⟩ := Finset.mem_filter.mp hC1
        have hp0 : i.val % 2 = 0 := by have := hno_odd1 hdo_eq C hC1 i hiC; omega
        have hCeq : C = {i} := Finset.eq_singleton_iff_unique_mem.mpr
          ⟨hiC, fun j hj => Finset.card_le_one_iff.mp hc1.le hj hiC⟩
        have hmem : col2 (i.val / 2) ∈ Ve := by
          show incEven (col2 (i.val / 2)) ∈ V
          rw [← hVec_eq_incEven hp0]
          simpa [hCeq, hSum] using mem_hSpace ht hCP
        rcases hwe _ hmem with hz | heq
        · exact (col2_ne_zero _ hz).elim
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp0, heq⟩
      have hcard_bi : (P1.biUnion id).card = P1.card := by
        rw [Finset.card_biUnion]
        · have : ∑ C ∈ P1, C.card = ∑ _ ∈ P1, 1 :=
            Finset.sum_congr rfl fun C hC => (Finset.mem_filter.mp hC).2
          simpa using this
        · intro C hC D hD hne
          exact pcs_pairwiseDisjoint (nxt ht) S (Finset.mem_filter.mp hC).1
            (Finset.mem_filter.mp hD).1 hne
      calc P1.card = (P1.biUnion id).card := hcard_bi.symm
        _ ≤ T.card := Finset.card_le_card hsub
        _ = t := hT
    have hP2_le : P2.card ≤ t := by
      let odV : V →ₗ[F2] V2 := oddProj.comp V.subtype
      have hker_od : LinearMap.ker odV = (Ve.map incEven).comap V.subtype := by
        ext ⟨v, hv⟩
        simp only [LinearMap.mem_ker, odV, LinearMap.comp_apply, Submodule.coe_subtype,
          Submodule.mem_comap, hVe_map, Submodule.mem_inf, LinearMap.mem_range]
        constructor
        · intro ho0
          refine ⟨hv, evenProj v, ?_⟩
          have hd := v4_decomp v
          rw [ho0, map_zero, add_zero] at hd
          exact hd.symm
        · rintro ⟨_, u, hu⟩
          rw [← hu, oddProj_incEven]
      have hker_rk : Module.finrank F2 (LinearMap.ker odV) = 1 := by
        have hsub : Ve.map incEven ≤ LinearMap.range V.subtype := by
          rw [Submodule.range_subtype, hVe_map]; exact inf_le_left
        have hrng : ((Ve.map incEven).comap V.subtype).map V.subtype = Ve.map incEven :=
          Submodule.map_comap_eq_of_le hsub
        rw [hker_od]
        have := Submodule.finrank_map_subtype_eq V ((Ve.map incEven).comap V.subtype)
        rw [hrng] at this
        have : Module.finrank F2 (Ve.map incEven) = 1 := hVe_rk.symm.trans hde_eq
        omega
      have hrng_rk : Module.finrank F2 (LinearMap.range odV) ≤ 1 := by
        have h3 := LinearMap.finrank_range_add_finrank_ker odV
        rw [hker_rk] at h3
        change Module.finrank F2 (LinearMap.range odV) + 1 = rk ht S at h3
        omega
      obtain ⟨wo, hwo⟩ := submodule_le_one_eq_zero_or_w hrng_rk
      by_cases hwo0 : wo = 0
      · have hP20 : P2 = ∅ := by
          ext C; simp only [Finset.notMem_empty, iff_false]
          intro hC2
          obtain ⟨hCP, hc2⟩ := Finset.mem_filter.mp hC2
          obtain ⟨s, _, _, harc, _, hlt, _⟩ := comp_arc ht hS hCP
          have hmem : oddProj (hSum C) ∈ LinearMap.range odV := ⟨⟨hSum C, mem_hSpace ht hCP⟩, rfl⟩
          have ho0 : oddProj (hSum C) = 0 := by
            rcases hwo _ hmem with h | h; exact h; exact h.trans hwo0
          rw [harc, hc2, hSum_arc ht s (by omega), arcSum_oddProj_zero_iff] at ho0; omega
        rw [hP20, Finset.card_empty]; omega
      · let T := Finset.univ.filter (fun i : Fin (6 * t) => i.val % 2 = 1 ∧ col2 (i.val / 2) = wo)
        have hT : T.card = t := card_lane_col_eq ht 1 (by decide) wo hwo0
        have hhit : ∀ C : ↥P2, ∃ i ∈ C.1, i ∈ T := by
          intro C
          obtain ⟨hCP, hc2⟩ := Finset.mem_filter.mp C.2
          obtain ⟨s, _, _, harc, _, hlt, _⟩ := comp_arc ht hS hCP
          have hmem : oddProj (hSum C.1) ∈ LinearMap.range odV := ⟨⟨hSum C.1, mem_hSpace ht hCP⟩, rfl⟩
          have heqW : oddProj (hSum C.1) = wo := by
            rcases hwo _ hmem with h0' | h1'
            · rw [harc, hc2, hSum_arc ht s (by omega), arcSum_oddProj_zero_iff] at h0'; omega
            · exact h1'
          have hs2 : hSum C.1 = hPat s.val + hPat (s.val + 1) := by
            rw [harc, hc2, hSum_arc ht s (by omega), arcSum_two]
          by_cases hsp : s.val % 2 = 1
          · have hod : wo = col2 (s.val / 2) := by
              rw [← heqW, hs2, hPat_eq_incOdd hsp, hPat_eq_incEven (by omega), map_add,
                oddProj_incOdd, oddProj_incEven, add_zero]
            refine ⟨idx ht (s.val + 0), ?_, ?_⟩
            · rw [harc, hc2]; exact (mem_arc_iff ht s 2 _).mpr ⟨0, by decide, rfl⟩
            · rw [add_zero, idx_self]
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsp, hod.symm⟩
          · have hod : wo = col2 ((s.val + 1) / 2) := by
              rw [← heqW, hs2, hPat_eq_incEven (by omega), hPat_eq_incOdd (by omega), map_add,
                oddProj_incEven, oddProj_incOdd, zero_add]
            refine ⟨idx ht (s.val + 1), ?_, ?_⟩
            · rw [harc, hc2]; exact (mem_arc_iff ht s 2 _).mpr ⟨1, by decide, rfl⟩
            · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
              · rw [idx_mod2]; omega
              · rw [← col2_mod3, idx_div2_mod3, col2_mod3]; exact hod.symm
        choose f hfC hfT using hhit
        have hinj : Function.Injective (fun C : ↥P2 => (⟨f C, hfT C⟩ : ↥T)) := by
          intro C D eq
          have hfeq : f C = f D := congrArg Subtype.val eq
          by_contra hne
          have hdis' := pcs_pairwiseDisjoint (nxt ht) S
            (Finset.mem_filter.mp C.2).1 (Finset.mem_filter.mp D.2).1 (fun e => hne (Subtype.ext e))
          exact Finset.disjoint_left.mp hdis' (hfC C) (hfeq ▸ hfC D)
        have hle := Fintype.card_le_of_injective _ hinj
        simpa [hT] using hle
    omega
  · have hVeq : Ve.map incEven ⊔ Vo.map incOdd = V := by
      have h1' := Submodule.finrank_sup_add_finrank_inf_eq (Ve.map incEven) (Vo.map incOdd)
      have hVe1 : Module.finrank F2 (Ve.map incEven) = 1 := hVe_rk.symm.trans hde_eq
      have hVo1 : Module.finrank F2 (Vo.map incOdd) = 1 := hVo_rk.symm.trans hdo_eq
      rw [hinf, finrank_bot, add_zero, hVe1, hVo1] at h1'
      have h2' := Submodule.finrank_mono hsup_le
      change Module.finrank F2 V ≤ 2 at hrk2
      exact Submodule.eq_of_le_of_finrank_eq hsup_le (by omega)
    obtain ⟨we, hwe⟩ := submodule_le_one_eq_zero_or_w (show Module.finrank F2 Ve ≤ 1 by omega)
    obtain ⟨wo, hwo⟩ := submodule_le_one_eq_zero_or_w (show Module.finrank F2 Vo ≤ 1 by omega)
    have hwe0 : we ≠ 0 := by
      intro hz
      have hbot : Ve = ⊥ := (Submodule.eq_bot_iff Ve).mpr fun u hu => by
        rcases hwe u hu with h | h; exact h; exact h.trans hz
      rw [hbot, finrank_bot] at hde_eq; omega
    have hwo0 : wo ≠ 0 := by
      intro hz
      have hbot : Vo = ⊥ := (Submodule.eq_bot_iff Vo).mpr fun u hu => by
        rcases hwo u hu with h | h; exact h; exact h.trans hz
      rw [hbot, finrank_bot] at hdo_eq; omega
    have hV_proj : ∀ v ∈ V, (evenProj v = 0 ∨ evenProj v = we) ∧ (oddProj v = 0 ∨ oddProj v = wo) := by
      intro v hv
      rw [← hVeq, Submodule.mem_sup] at hv
      obtain ⟨_, ⟨ue, hue, rfl⟩, _, ⟨uo, huo, rfl⟩, rfl⟩ := hv
      rw [map_add, evenProj_incEven, evenProj_incOdd, add_zero,
        map_add, oddProj_incEven, oddProj_incOdd, zero_add]
      exact ⟨hwe ue hue, hwo uo huo⟩
    exact runs_a2_case_11 ht ht3 hS hwe0 hwo0 hV_proj hP_part hP_def
  · omega
  · have hVeq : V = LinearMap.range incEven := by
      have hle : Ve.map incEven ≤ V := by rw [hVe_map]; exact inf_le_left
      have hVe2 : Module.finrank F2 (Ve.map incEven) = 2 := hVe_rk.symm.trans hde_eq
      have hrkV : Module.finrank F2 V = 2 := by
        have := Submodule.finrank_mono hle
        change Module.finrank F2 V ≤ 2 at hrk2
        omega
      have heq1 : Ve.map incEven = V := Submodule.eq_of_le_of_finrank_eq hle (by omega)
      have hVeTop : Ve = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hde_eq, Module.finrank_fin_fun])
      rw [← heq1, hVeTop, Submodule.map_top]
    exact runs_a2_case_pure_even ht ht3 hS h1 hr hVeq hdef_budget
  · omega
  · omega

def thresh (t : ℕ) : ℕ := if t = 1 then 1 else if t = 2 then 2 else 3 * t - 5

lemma mixed_finrank_le {U : Submodule F2 (W t)} (hg : goodU ht U)
    (h0 : 0 < sitesOf (suppU U) 0) (h1 : 0 < sitesOf (suppU U) 1) :
    Module.finrank F2 U ≤ thresh t := by
  by_cases hS : suppU U = Finset.univ
  · have hle := finrank_le_one_of_supp_univ ht hg hS
    unfold thresh; split_ifs <;> omega
  · have hbound := finrank_add_rk_le_runs ht hg
    have hlt := runs_lt_a ht hS h0 h1
    set r := (pcs (nxt ht) (suppU U)).card
    set k := rk ht (suppU U)
    unfold thresh
    split_ifs with ht1 ht2
    · subst ht1
      by_cases hr2 : r = 2
      · have hk0 : k ≠ 0 := fun hk => by have := rk_zero_runs ht hS hk; omega
        omega
      · omega
    · subst ht2
      by_cases hr5 : r = 5
      · have hk4 := runs_eq_a_sub_one ht (by decide) hg hS h0 h1 hr5; omega
      by_cases hr4 : r = 4
      · have hk2 : ¬ k ≤ 1 := fun hk => by have := rk_le_one_runs ht hS hk; omega
        omega
      by_cases hr3 : r = 3
      · have hk0 : k ≠ 0 := fun hk => by have := rk_zero_runs ht hS hk; omega
        omega
      omega
    · have ht3 : 3 ≤ t := by omega
      by_cases hr1 : r = 3 * t - 1
      · have hk4 := runs_eq_a_sub_one ht (by omega) hg hS h0 h1 hr1; omega
      by_cases hr2 : r = 3 * t - 2
      · have hk3 := runs_eq_a_sub_two ht ht3 hS h0 h1 hr2; omega
      by_cases hr3 : r = 3 * t - 3
      · have hk2 : ¬ k ≤ 1 := fun hk => by have := rk_le_one_runs ht hS hk; omega
        omega
      by_cases hr4 : r = 3 * t - 4
      · have hk0 : k ≠ 0 := fun hk => by have := rk_zero_runs ht hS hk; omega
        omega
      omega

end UpperBounds

section Witnesses

variable {t : ℕ} (ht : 0 < t)

lemma witness_exists :
    ∃ U : Submodule F2 (W t), goodU ht U ∧
      0 < sitesOf (suppU U) 0 ∧ 0 < sitesOf (suppU U) 1 ∧
      Module.finrank F2 U = thresh t := by
  unfold thresh
  split_ifs with ht1 ht2
  · subst ht1
    let ones : W 1 := fun _ => 1
    refine ⟨Submodule.span F2 {ones}, ?_, ?_, ?_, ?_⟩
    · constructor
      · intro x hx b
        rw [Submodule.mem_span_singleton] at hx
        obtain ⟨c, rfl⟩ := hx
        have hsum : (∑ i : Fin (6 * 1), hVec i b) = 0 := by
          fin_cases b <;> decide
        calc (∑ i : Fin (6 * 1), hVec i b * (c • ones) i)
            = (∑ i : Fin (6 * 1), hVec i b) * c := by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun i _ => by simp [ones]
          _ = 0 := by rw [hsum, zero_mul]
      · intro x hx y hy i
        rw [Submodule.mem_span_singleton] at hx hy
        obtain ⟨cx, rfl⟩ := hx
        obtain ⟨cy, rfl⟩ := hy
        simp [ones]
    · refine Finset.card_pos.mpr ⟨⟨0, by decide⟩, Finset.mem_filter.mpr ⟨?_, by decide⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ones, Submodule.subset_span (Set.mem_singleton _),
        by simp [ones]⟩
    · refine Finset.card_pos.mpr ⟨⟨1, by decide⟩, Finset.mem_filter.mpr ⟨?_, by decide⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ones, Submodule.subset_span (Set.mem_singleton _),
        by simp [ones]⟩
    · exact finrank_span_singleton (fun h => by have := congrFun h ⟨0, by decide⟩; simp [ones] at this)
  · subst ht2
    let u0 : W 2 := fun i => if i.val = 0 ∨ i.val = 6 then 1 else 0
    let u1 : W 2 := fun i => if i.val = 3 ∨ i.val = 9 then 1 else 0
    let U : Submodule F2 (W 2) := Submodule.span F2 {u0, u1}
    have hu0U : u0 ∈ U := Submodule.subset_span (by simp)
    have hu1U : u1 ∈ U := Submodule.subset_span (by simp)
    have hmemU : ∀ x ∈ U, ∃ c0 c1 : F2, x = c0 • u0 + c1 • u1 := by
      intro x hx
      obtain ⟨c0, c1, hc⟩ := Submodule.mem_span_pair.mp hx
      exact ⟨c0, c1, hc.symm⟩
    refine ⟨U, ?_, ?_, ?_, ?_⟩
    · constructor
      · intro x hx b
        obtain ⟨c0, c1, rfl⟩ := hmemU x hx
        have h0b : (∑ i : Fin (6 * 2), hVec i b * u0 i) = 0 := by
          dsimp only [u0]; fin_cases b <;> decide
        have h1b : (∑ i : Fin (6 * 2), hVec i b * u1 i) = 0 := by
          dsimp only [u1]; fin_cases b <;> decide
        calc (∑ i : Fin (6 * 2), hVec i b * (c0 • u0 + c1 • u1) i)
            = c0 * (∑ i : Fin (6 * 2), hVec i b * u0 i) +
              c1 * (∑ i : Fin (6 * 2), hVec i b * u1 i) := by
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro i _
              simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              ring
          _ = 0 := by rw [h0b, h1b, mul_zero, mul_zero, add_zero]
      · intro x hx y hy i
        obtain ⟨cx0, cx1, rfl⟩ := hmemU x hx
        obtain ⟨cy0, cy1, rfl⟩ := hmemU y hy
        have hdisj : ∀ j : Fin (6 * 2),
            (j.val = 0 ∨ j.val = 6 ∨ j.val = 3 ∨ j.val = 9) →
            ¬ ((nxt ht j).val = 0 ∨ (nxt ht j).val = 6 ∨ (nxt ht j).val = 3 ∨ (nxt ht j).val = 9) := by
          intro j hj hnj
          have hjlt := j.isLt
          have hnv := nxt_val ht j
          split_ifs at hnv <;> omega
        have hzero : ∀ (a b : F2) (j : Fin (6 * 2)),
            ¬ (j.val = 0 ∨ j.val = 6 ∨ j.val = 3 ∨ j.val = 9) → (a • u0 + b • u1) j = 0 := by
          intro a b j hnj
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, u0, u1]
          split_ifs <;> first | omega | simp
        by_cases hi : i.val = 0 ∨ i.val = 6 ∨ i.val = 3 ∨ i.val = 9
        · have hni := hdisj i hi
          rw [hzero cy0 cy1 _ hni, hzero cx0 cx1 _ hni, mul_zero, zero_mul]
        · rw [hzero cx0 cx1 _ hi, hzero cy0 cy1 _ hi, zero_mul, mul_zero]
    · refine Finset.card_pos.mpr ⟨⟨0, by decide⟩, Finset.mem_filter.mpr ⟨?_, by decide⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u0, hu0U, by simp [u0]⟩
    · refine Finset.card_pos.mpr ⟨⟨3, by decide⟩, Finset.mem_filter.mpr ⟨?_, by decide⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u1, hu1U, by simp [u1]⟩
    · have hli : LinearIndependent F2 ![u0, u1] := by
        rw [Fintype.linearIndependent_iff]
        intro g hg i
        have h0 := congrFun hg ⟨0, by decide⟩
        have h3 := congrFun hg ⟨3, by decide⟩
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, u0, u1] at h0 h3
        norm_num at h0 h3
        fin_cases i <;> assumption
      have hset : ({u0, u1} : Set (W 2)) = Set.range ![u0, u1] := by
        ext x; simp [Fin.exists_fin_two, or_comm]
      have hUeq : U = Submodule.span F2 (Set.range ![u0, u1]) := congrArg (Submodule.span F2) hset
      rw [hUeq, finrank_span_eq_card hli]
      simp
  · have ht3 : 3 ≤ t := by omega
    let E' : Finset (Fin (6 * t)) :=
      Finset.univ.filter (fun i => i.val % 2 = 0 ∧ i.val ≠ 2 ∧ i.val ≠ 4 ∧ i.val ≠ 8 ∧ i.val ≠ 10)
    have hE'_card : E'.card = 3 * t - 4 := by
      let Ev : Finset (Fin (6 * t)) := Finset.univ.filter (fun i => i.val % 2 = 0)
      have hEv_card : Ev.card = 3 * t := by
        let f : Fin (3 * t) → Fin (6 * t) := fun q => ⟨2 * q.val, by have := q.isLt; omega⟩
        have heq : Ev = Finset.univ.image f := by
          ext i
          simp only [Ev, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
          constructor
          · intro hp; refine ⟨⟨i.val / 2, by have := i.isLt; omega⟩, Fin.ext (by dsimp [f]; omega)⟩
          · rintro ⟨q, rfl⟩; dsimp [f]; omega
        rw [heq, Finset.card_image_of_injective]
        · simp
        · intro q₁ q₂ h; exact Fin.ext (by have := congrArg Fin.val h; dsimp [f] at this; omega)
      let B4 : Finset (Fin (6 * t)) :=
        {⟨2, by omega⟩, ⟨4, by omega⟩, ⟨8, by omega⟩, ⟨10, by omega⟩}
      have hB4_sub : B4 ⊆ Ev := by
        intro i hi
        simp only [B4, Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl | rfl | rfl <;> exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩
      have hB4_card : B4.card = 4 := by
        dsimp only [B4]
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_singleton] <;>
        simp [Fin.ext_iff]
      have hE'_eq : E' = Ev \ B4 := by
        ext i
        simp only [E', Ev, B4, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, not_or]
      rw [hE'_eq, Finset.card_sdiff, Finset.inter_eq_left.mpr hB4_sub, hEv_card, hB4_card]
    let extE : (↥E' → F2) →ₗ[F2] W t :=
      { toFun := fun f i => if hi : i ∈ E' then f ⟨i, hi⟩ else 0
        map_add' := fun f g => by ext i; dsimp; split_ifs <;> simp
        map_smul' := fun c f => by ext i; dsimp; split_ifs <;> simp }
    have hextE_inj : Function.Injective extE := by
      intro f g hfg
      ext ⟨i, hi⟩
      have := congrFun hfg i
      simpa [extE, hi] using this
    let chkE : (↥E' → F2) →ₗ[F2] V2 :=
      { toFun := fun f b => ∑ x : ↥E', evenProj (hVec x.1) b * f x
        map_add' := fun f g => by
          ext b; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
        map_smul' := fun c f => by
          ext b; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro x _; ring }
    have hchkE_surj : LinearMap.range chkE = ⊤ := by
      rw [Submodule.eq_top_iff']
      intro v
      have hp0 : (⟨12, by omega⟩ : Fin (6 * t)) ∈ E' := by simp [E']
      have hp1 : (⟨14, by omega⟩ : Fin (6 * t)) ∈ E' := by simp [E']
      let x0 : ↥E' := ⟨⟨12, by omega⟩, hp0⟩
      let x1 : ↥E' := ⟨⟨14, by omega⟩, hp1⟩
      refine ⟨v 0 • Pi.single x0 1 + v 1 • Pi.single x1 1, ?_⟩
      have he0 : evenProj (hVec x0.1) = ![1, 0] := by
        have hp : x0.1.val % 2 = 0 := by simp [x0]
        rw [hVec_eq_incEven hp, evenProj_incEven]
        change col2 (12 / 2) = ![1, 0]
        decide
      have he1 : evenProj (hVec x1.1) = ![0, 1] := by
        have hp : x1.1.val % 2 = 0 := by simp [x1]
        rw [hVec_eq_incEven hp, evenProj_incEven]
        change col2 (14 / 2) = ![0, 1]
        decide
      have hsingle : ∀ (x : ↥E'), chkE (Pi.single x 1) = evenProj (hVec x.1) := by
        intro x; ext b
        dsimp only [chkE, LinearMap.coe_mk, AddHom.coe_mk]
        rw [Finset.sum_eq_single x]
        · simp
        · intro y _ hne; simp [Pi.single_eq_of_ne hne]
        · intro h; exact (h (Finset.mem_univ _)).elim
      rw [map_add, map_smul, map_smul, hsingle x0, hsingle x1, he0, he1]
      ext b; fin_cases b <;> simp
    have hker_rk : Module.finrank F2 (LinearMap.ker chkE) = 3 * t - 6 := by
      have h3 := LinearMap.finrank_range_add_finrank_ker chkE
      rw [hchkE_surj, finrank_top, Module.finrank_fin_fun, Module.finrank_pi, Fintype.card_coe,
        hE'_card] at h3
      omega
    let VE' : Submodule F2 (W t) := (LinearMap.ker chkE).map extE
    have hVE'_rk : Module.finrank F2 VE' = 3 * t - 6 := by
      have hrng : LinearMap.range (extE.comp (LinearMap.ker chkE).subtype) = VE' := by
        ext x; simp [VE', LinearMap.mem_range, Submodule.mem_map]
      rw [← hrng, LinearMap.finrank_range_of_inj (fun x y h => Subtype.ext (hextE_inj h)), hker_rk]
    let uOdd : W t := fun i => if i.val = 3 ∨ i.val = 9 then 1 else 0
    have huOdd_ne : uOdd ≠ 0 := fun h => by
      have := congrFun h ⟨3, by omega⟩; simp [uOdd] at this
    let U : Submodule F2 (W t) := VE' ⊔ Submodule.span F2 {uOdd}
    have hinf : VE' ⊓ Submodule.span F2 {uOdd} = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨hx1, hx2⟩ := hx
      obtain ⟨f, _, rfl⟩ := hx1
      rw [SetLike.mem_coe, Submodule.mem_span_singleton] at hx2
      obtain ⟨c, hc⟩ := hx2
      have h3nE : (⟨3, by omega⟩ : Fin (6 * t)) ∉ E' := by simp [E']
      have h3val := congrFun hc ⟨3, by omega⟩
      simp only [extE, LinearMap.coe_mk, AddHom.coe_mk, dif_neg h3nE, Pi.smul_apply,
        smul_eq_mul, uOdd, true_or, ↓reduceIte, mul_one] at h3val
      rw [← hc, h3val, zero_smul]
    have hUrk : Module.finrank F2 U = 3 * t - 5 := by
      have h1' := Submodule.finrank_sup_add_finrank_inf_eq VE' (Submodule.span F2 {uOdd})
      rw [hinf, finrank_bot, add_zero, hVE'_rk, finrank_span_singleton huOdd_ne] at h1'
      dsimp only [U]
      omega
    have hsupp_VE' : ∀ x ∈ VE', ∀ i : Fin (6 * t), i ∉ E' → x i = 0 := by
      rintro _ ⟨f, _, rfl⟩ i hi
      simp [extE, hi]
    have hsupp_U : ∀ x ∈ U, ∀ i : Fin (6 * t), i ∉ E' → i.val ≠ 3 → i.val ≠ 9 → x i = 0 := by
      intro x hx i hi h3 h9
      rw [Submodule.mem_sup] at hx
      obtain ⟨xe, hxe, xo, hxo, rfl⟩ := hx
      rw [Submodule.mem_span_singleton] at hxo
      obtain ⟨c, rfl⟩ := hxo
      simp only [Pi.add_apply, hsupp_VE' xe hxe i hi, zero_add, Pi.smul_apply, smul_eq_mul,
        uOdd, h3, h9, or_self, ↓reduceIte, mul_zero]
    have hgood : goodU ht U := by
      constructor
      · intro x hx b
        rw [Submodule.mem_sup] at hx
        obtain ⟨xe, hxe, xo, hxo, rfl⟩ := hx
        have hxe0 : (∑ i : Fin (6 * t), hVec i b * xe i) = 0 := by
          obtain ⟨f, hf, rfl⟩ := hxe
          have hf0 : chkE f = 0 := hf
          have hsub : (∑ i : Fin (6 * t), hVec i b * extE f i) = ∑ i ∈ E', hVec i b * extE f i := by
            symm
            apply Finset.sum_subset (Finset.subset_univ E')
            intro i _ hi
            simp [extE, hi]
          rw [hsub]
          by_cases hb : b.val < 2
          · have hfb := congrFun hf0 ⟨b.val, hb⟩
            dsimp only [chkE, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hfb
            rw [← hfb, ← Finset.sum_coe_sort E' (fun i => hVec i b * extE f i)]
            apply Finset.sum_congr rfl
            intro y _
            simp only [extE, LinearMap.coe_mk, AddHom.coe_mk, dif_pos y.2, evenProj]
          · apply Finset.sum_eq_zero
            intro i hi
            have hp0 : i.val % 2 = 0 := (Finset.mem_filter.mp hi).2.1
            have hb0 : hVec i b = 0 := by
              rw [hVec_eq_incEven hp0]
              dsimp only [incEven, LinearMap.coe_mk, AddHom.coe_mk]
              rw [dif_neg hb]
            rw [hb0, zero_mul]
        have hxo0 : (∑ i : Fin (6 * t), hVec i b * xo i) = 0 := by
          rw [Submodule.mem_span_singleton] at hxo
          obtain ⟨c, rfl⟩ := hxo
          have hsum_odd : (∑ i : Fin (6 * t), hVec i b * uOdd i) = 0 := by
            let p3 : Fin (6 * t) := ⟨3, by omega⟩
            let p9 : Fin (6 * t) := ⟨9, by omega⟩
            have hne : p3 ≠ p9 := by simp [p3, p9, Fin.ext_iff]
            have hsub : (∑ i : Fin (6 * t), hVec i b * uOdd i) =
                ∑ i ∈ ({p3, p9} : Finset (Fin (6 * t))), hVec i b * uOdd i := by
              symm
              apply Finset.sum_subset (Finset.subset_univ _)
              intro i _ hi
              simp only [Finset.mem_insert, Finset.mem_singleton, p3, p9, Fin.ext_iff, not_or] at hi
              simp [uOdd, hi.1, hi.2]
            rw [hsub, Finset.sum_pair hne]
            have hu3 : uOdd p3 = 1 := by simp [uOdd, p3]
            have hu9 : uOdd p9 = 1 := by simp [uOdd, p9]
            rw [hu3, hu9, mul_one, mul_one]
            have heq : hVec p3 b = hVec p9 b := by
              have e3 : p3 = idx ht 3 := Fin.ext (by simp [p3, idx, Nat.mod_eq_of_lt (by omega : 3 < 6 * t)])
              have e9 : p9 = idx ht 9 := Fin.ext (by simp [p9, idx, Nat.mod_eq_of_lt (by omega : 9 < 6 * t)])
              rw [e3, e9, hVec_idx, hVec_idx, ← hPat_mod6 3, ← hPat_mod6 9]
            rw [heq, CharTwo.add_self_eq_zero]
          calc (∑ i : Fin (6 * t), hVec i b * (c • uOdd) i)
              = c * (∑ i : Fin (6 * t), hVec i b * uOdd i) := by
                rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; simp; ring
            _ = 0 := by rw [hsum_odd, mul_zero]
        calc (∑ i : Fin (6 * t), hVec i b * (xe + xo) i)
            = (∑ i : Fin (6 * t), hVec i b * xe i) + (∑ i : Fin (6 * t), hVec i b * xo i) := by
              rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; simp [mul_add]
          _ = 0 := by rw [hxe0, hxo0, add_zero]
      · intro x hx y hy i
        have hilt := i.isLt
        by_cases hi : i ∈ E' ∨ i.val = 3 ∨ i.val = 9
        · have hni : nxt ht i ∉ E' ∧ (nxt ht i).val ≠ 3 ∧ (nxt ht i).val ≠ 9 := by
            rcases hi with hiE | hi3 | hi9
            · obtain ⟨hp0, h2, h4, h8, h10⟩ := (Finset.mem_filter.mp hiE).2
              refine ⟨?_, ?_, ?_⟩
              · intro hmem
                have hp1 := (Finset.mem_filter.mp hmem).2.1
                have := nxt_parity ht i
                omega
              · rw [nxt_val]; split_ifs <;> omega
              · rw [nxt_val]; split_ifs <;> omega
            · refine ⟨?_, ?_, ?_⟩
              · intro hmem
                have h4 := (Finset.mem_filter.mp hmem).2.2.2.1
                rw [nxt_val] at h4; split_ifs at h4 <;> omega
              · rw [nxt_val]; split_ifs <;> omega
              · rw [nxt_val]; split_ifs <;> omega
            · refine ⟨?_, ?_, ?_⟩
              · intro hmem
                have h10 := (Finset.mem_filter.mp hmem).2.2.2.2.2
                rw [nxt_val] at h10; split_ifs at h10 <;> omega
              · rw [nxt_val]; split_ifs <;> omega
              · rw [nxt_val]; split_ifs <;> omega
          rw [hsupp_U y hy _ hni.1 hni.2.1 hni.2.2, hsupp_U x hx _ hni.1 hni.2.1 hni.2.2,
            mul_zero, zero_mul]
        · push_neg at hi
          rw [hsupp_U x hx _ hi.1 hi.2.1 hi.2.2, hsupp_U y hy _ hi.1 hi.2.1 hi.2.2,
            zero_mul, mul_zero]
    have hodd_pos : 0 < sitesOf (suppU U) 1 := by
      refine Finset.card_pos.mpr ⟨⟨3, by omega⟩, Finset.mem_filter.mpr ⟨?_, by simp⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, uOdd,
        Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _)), by simp [uOdd]⟩
    have heven_pos : 0 < sitesOf (suppU U) 0 := by
      have hne_bot : VE' ≠ ⊥ := by
        intro hb
        rw [hb, finrank_bot] at hVE'_rk
        omega
      obtain ⟨x, hxVE, hx0⟩ : ∃ x ∈ VE', x ≠ 0 := by
        by_contra! hall
        exact hne_bot ((Submodule.eq_bot_iff VE').mpr hall)
      obtain ⟨i, hxi⟩ : ∃ i : Fin (6 * t), x i ≠ 0 := by
        by_contra! hall; exact hx0 (funext hall)
      have hiE : i ∈ E' := by
        by_contra hnE
        exact hxi (hsupp_VE' x hxVE i hnE)
      have hp0 : i.val % 2 = 0 := (Finset.mem_filter.mp hiE).2.1
      refine Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨?_, hp0⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, Submodule.mem_sup_left hxVE, hxi⟩
    exact ⟨U, hgood, heven_pos, hodd_pos, hUrk⟩

end Witnesses

section PureCount

def embLane {t : ℕ} (p : ℕ) (hp : p < 2) : (Fin (3 * t) → F2) →ₗ[F2] W t where
  toFun y i := if i.val % 2 = p then y ⟨i.val / 2, by have := i.isLt; omega⟩ else 0
  map_add' y z := by ext i; dsimp; split_ifs <;> simp
  map_smul' c y := by ext i; dsimp; split_ifs <;> simp

lemma embLane_inj {t : ℕ} (p : ℕ) (hp : p < 2) : Function.Injective (embLane (t := t) p hp) := by
  intro y z h
  ext q
  have h1 := congrFun h ⟨2 * q.val + p, by have := q.isLt; omega⟩
  have hpar : (2 * q.val + p) % 2 = p := by omega
  have hdiv : (2 * q.val + p) / 2 = q.val := by omega
  simpa [embLane, hpar, hdiv] using h1

lemma mem_range_embLane_iff {t : ℕ} (p : ℕ) (hp : p < 2) (x : W t) :
    x ∈ LinearMap.range (embLane (t := t) p hp) ↔ ∀ i : Fin (6 * t), i.val % 2 ≠ p → x i = 0 := by
  constructor
  · rintro ⟨y, rfl⟩ i hne
    simp [embLane, hne]
  · intro hx
    refine ⟨fun q => x ⟨2 * q.val + p, by have := q.isLt; omega⟩, ?_⟩
    ext i
    dsimp only [embLane, LinearMap.coe_mk, AddHom.coe_mk]
    split_ifs with hpar
    · congr 1; apply Fin.ext; dsimp only; omega
    · exact (hx i hpar).symm

def HLane {t : ℕ} : (Fin (3 * t) → F2) →ₗ[F2] V2 where
  toFun y b := ∑ q : Fin (3 * t), col2 q.val b * y q
  map_add' y z := by ext b; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    ext b; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro q _; ring

lemma HLane_surj {t : ℕ} (ht : 0 < t) : LinearMap.range (HLane (t := t)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro v
  let q0 : Fin (3 * t) := ⟨0, by omega⟩
  let q1 : Fin (3 * t) := ⟨1, by omega⟩
  refine ⟨v 0 • Pi.single q0 1 + v 1 • Pi.single q1 1, ?_⟩
  have hsingle : ∀ (q : Fin (3 * t)), HLane (Pi.single q 1) = col2 q.val := by
    intro q; ext b
    dsimp only [HLane, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single q]
    · simp
    · intro r _ hne; simp [Pi.single_eq_of_ne hne]
    · intro h; exact (h (Finset.mem_univ _)).elim
  rw [map_add, map_smul, map_smul, hsingle q0, hsingle q1]
  have hc0 : col2 q0.val = ![1, 0] := by change col2 0 = ![1, 0]; decide
  have hc1 : col2 q1.val = ![0, 1] := by change col2 1 = ![0, 1]; decide
  rw [hc0, hc1]
  ext b; fin_cases b <;> simp

lemma finrank_ker_HLane {t : ℕ} (ht : 0 < t) :
    Module.finrank F2 (LinearMap.ker (HLane (t := t))) = 3 * t - 2 := by
  have h3 := LinearMap.finrank_range_add_finrank_ker (HLane (t := t))
  rw [HLane_surj ht, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h3
  omega

lemma hVec_sum_embLane {t : ℕ} (p : ℕ) (hp : p < 2) (y : Fin (3 * t) → F2) :
    (∀ b : Fin 4, (∑ i : Fin (6 * t), hVec i b * embLane (t := t) p hp y i) = 0) ↔
      y ∈ LinearMap.ker (HLane (t := t)) := by
  let f : Fin (3 * t) → Fin (6 * t) := fun q => ⟨2 * q.val + p, by have := q.isLt; omega⟩
  have hfinj : Function.Injective f := fun q₁ q₂ h => Fin.ext (by have := congrArg Fin.val h; dsimp [f] at this; omega)
  have hsum_eq : ∀ b : Fin 4,
      (∑ i : Fin (6 * t), hVec i b * embLane (t := t) p hp y i) =
      ∑ q : Fin (3 * t), hVec (f q) b * y q := by
    intro b
    have hsub : (∑ i : Fin (6 * t), hVec i b * embLane (t := t) p hp y i) =
        ∑ i ∈ Finset.univ.image f, hVec i b * embLane (t := t) p hp y i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have hne : i.val % 2 ≠ p := by
        intro heq
        apply hi
        refine Finset.mem_image.mpr ⟨⟨i.val / 2, by have := i.isLt; omega⟩, Finset.mem_univ _, ?_⟩
        apply Fin.ext; dsimp [f]; omega
      simp [embLane, hne]
    rw [hsub, Finset.sum_image (fun q₁ _ q₂ _ h => hfinj h)]
    apply Finset.sum_congr rfl
    intro q _
    have hpar : (f q).val % 2 = p := by dsimp [f]; omega
    have hdiv : (f q).val / 2 = q.val := by dsimp [f]; omega
    simp [embLane, hpar, hdiv]
  rw [LinearMap.mem_ker]
  constructor
  · intro hb
    ext c
    dsimp only [HLane, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
    have h0 := hb ⟨2 * p + c.val, by omega⟩
    rw [hsum_eq] at h0
    rw [← h0]
    apply Finset.sum_congr rfl
    intro q _
    congr 1
    have hp01 : p = 0 ∨ p = 1 := by omega
    rcases hp01 with rfl | rfl
    · have hpq : (f q).val % 2 = 0 := by dsimp [f]; omega
      have hdv : (f q).val / 2 = q.val := by dsimp [f]; omega
      rw [hVec_eq_incEven hpq, hdv]
      fin_cases c <;> simp [incEven]
    · have hpq : (f q).val % 2 = 1 := by dsimp [f]; omega
      have hdv : (f q).val / 2 = q.val := by dsimp [f]; omega
      rw [hVec_eq_incOdd hpq, hdv]
      fin_cases c <;> simp [incOdd]
  · intro hker b
    rw [hsum_eq]
    have hp01 : p = 0 ∨ p = 1 := by omega
    rcases hp01 with rfl | rfl
    · by_cases hb : b.val < 2
      · have hc := congrFun hker ⟨b.val, hb⟩
        dsimp only [HLane, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hc
        rw [← hc]
        apply Finset.sum_congr rfl
        intro q _
        congr 1
        have hpq : (f q).val % 2 = 0 := by dsimp [f]; omega
        have hdv : (f q).val / 2 = q.val := by dsimp [f]; omega
        rw [hVec_eq_incEven hpq, hdv]
        dsimp only [incEven, LinearMap.coe_mk, AddHom.coe_mk]
        rw [dif_pos hb]
      · apply Finset.sum_eq_zero
        intro q _
        have hpq : (f q).val % 2 = 0 := by dsimp [f]; omega
        rw [hVec_eq_incEven hpq]
        dsimp only [incEven, LinearMap.coe_mk, AddHom.coe_mk]
        rw [dif_neg hb, zero_mul]
    · by_cases hb : 2 ≤ b.val
      · have hc := congrFun hker ⟨b.val - 2, by omega⟩
        dsimp only [HLane, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hc
        rw [← hc]
        apply Finset.sum_congr rfl
        intro q _
        congr 1
        have hpq : (f q).val % 2 = 1 := by dsimp [f]; omega
        have hdv : (f q).val / 2 = q.val := by dsimp [f]; omega
        rw [hVec_eq_incOdd hpq, hdv]
        dsimp only [incOdd, LinearMap.coe_mk, AddHom.coe_mk]
        rw [dif_pos hb]
      · apply Finset.sum_eq_zero
        intro q _
        have hpq : (f q).val % 2 = 1 := by dsimp [f]; omega
        rw [hVec_eq_incOdd hpq]
        dsimp only [incOdd, LinearMap.coe_mk, AddHom.coe_mk]
        rw [dif_neg hb, zero_mul]

lemma adj_of_le_range_embLane {t : ℕ} (ht : 0 < t) (p : ℕ) (hp : p < 2) {U : Submodule F2 (W t)}
    (hle : U ≤ LinearMap.range (embLane (t := t) p hp)) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (nxt ht i) = x (nxt ht i) * y i := by
  intro x hx y hy i
  by_cases hi : i.val % 2 = p
  · have hni : (nxt ht i).val % 2 ≠ p := by rw [nxt_parity]; omega
    have hy0 := (mem_range_embLane_iff p hp y).mp (hle hy) (nxt ht i) hni
    have hx0 := (mem_range_embLane_iff p hp x).mp (hle hx) (nxt ht i) hni
    rw [hy0, hx0, mul_zero, zero_mul]
  · have hx0 := (mem_range_embLane_iff p hp x).mp (hle hx) i hi
    have hy0 := (mem_range_embLane_iff p hp y).mp (hle hy) i hi
    rw [hx0, hy0, zero_mul, mul_zero]

lemma card_lane_eq {t : ℕ} (ht : 0 < t) (p : ℕ) (hp : p < 2) (d : ℕ) :
    letI : Fintype (Submodule F2 (W t)) := Fintype.ofFinite _
    ((Finset.univ : Finset (Submodule F2 (W t))).filter
      (fun U : Submodule F2 (W t) => goodU ht U ∧ Module.finrank F2 U = d ∧
        U ≤ LinearMap.range (embLane (t := t) p hp))).card =
    Nat.card {V : Submodule F2 (Fin (3 * t - 2) → F2) // Module.finrank F2 V = d} := by
  letI : Fintype (Submodule F2 (W t)) := Fintype.ofFinite _
  let S := (Finset.univ : Finset (Submodule F2 (W t))).filter
    (fun U : Submodule F2 (W t) => goodU ht U ∧ Module.finrank F2 U = d ∧
      U ≤ LinearMap.range (embLane (t := t) p hp))
  have hcard1 : S.card = Nat.card {U : Submodule F2 (W t) //
      goodU ht U ∧ Module.finrank F2 U = d ∧ U ≤ LinearMap.range (embLane (t := t) p hp)} := by
    rw [← Fintype.card_eq_nat_card, ← Fintype.card_coe]
    apply Fintype.card_congr
    exact
      { toFun := fun ⟨U, hU⟩ => ⟨U, (Finset.mem_filter.mp hU).2⟩
        invFun := fun ⟨U, hU⟩ => ⟨U, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU⟩⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun ⟨_, _⟩ => rfl }
  rw [hcard1]
  have he_rk : Module.finrank F2 (LinearMap.ker (HLane (t := t))) =
      Module.finrank F2 (Fin (3 * t - 2) → F2) := by
    rw [finrank_ker_HLane ht, Module.finrank_fin_fun]
  let eK : LinearMap.ker (HLane (t := t)) ≃ₗ[F2] (Fin (3 * t - 2) → F2) :=
    LinearEquiv.ofFinrankEq _ _ he_rk
  let φ : (Fin (3 * t - 2) → F2) →ₗ[F2] W t :=
    (embLane (t := t) p hp).comp ((LinearMap.ker (HLane (t := t))).subtype.comp eK.symm.toLinearMap)
  have hφ_inj : Function.Injective φ :=
    (embLane_inj p hp).comp (Subtype.val_injective.comp eK.symm.injective)
  have hφ_map_rk : ∀ V : Submodule F2 (Fin (3 * t - 2) → F2),
      Module.finrank F2 (V.map φ) = Module.finrank F2 V := by
    intro V
    have hrng : LinearMap.range (φ.comp V.subtype) = V.map φ := by
      ext x; simp [LinearMap.mem_range, Submodule.mem_map]
    rw [← hrng, LinearMap.finrank_range_of_inj (fun x y h => Subtype.ext (hφ_inj h))]
  have hφ_range : ∀ U : Submodule F2 (W t),
      (goodU ht U ∧ U ≤ LinearMap.range (embLane (t := t) p hp)) ↔ U ≤ LinearMap.range φ := by
    intro U
    constructor
    · rintro ⟨hg, hle⟩ x hx
      obtain ⟨y, rfl⟩ := hle hx
      have hyK : y ∈ LinearMap.ker (HLane (t := t)) :=
        (hVec_sum_embLane p hp y).mp (hg.1 _ hx)
      refine ⟨eK ⟨y, hyK⟩, ?_⟩
      simp [φ]
    · intro hle
      have hleE : U ≤ LinearMap.range (embLane (t := t) p hp) := by
        intro x hx
        obtain ⟨v, rfl⟩ := hle hx
        exact ⟨_, rfl⟩
      refine ⟨⟨?_, adj_of_le_range_embLane ht p hp hleE⟩, hleE⟩
      intro x hx b
      obtain ⟨v, rfl⟩ := hle hx
      exact ((hVec_sum_embLane p hp _).mpr (eK.symm v).2) b
  symm
  apply Nat.card_congr
  exact
    { toFun := fun ⟨V, hV⟩ =>
        ⟨V.map φ, by
          have hsub : V.map φ ≤ LinearMap.range φ := by
            rintro _ ⟨v, _, rfl⟩; exact ⟨v, rfl⟩
          have hgr := (hφ_range (V.map φ)).mpr hsub
          exact ⟨hgr.1, (hφ_map_rk V).trans hV, hgr.2⟩⟩
      invFun := fun ⟨U, hU⟩ =>
        ⟨U.comap φ, by
          have hsub : U ≤ LinearMap.range φ := (hφ_range U).mp ⟨hU.1, hU.2.2⟩
          have hmc : (U.comap φ).map φ = U := Submodule.map_comap_eq_of_le hsub
          have := hφ_map_rk (U.comap φ)
          rw [hmc, hU.2.1] at this
          exact this.symm⟩
      left_inv := fun ⟨V, _⟩ => Subtype.ext (Submodule.comap_map_eq_of_injective hφ_inj V)
      right_inv := fun ⟨U, hU⟩ => Subtype.ext (Submodule.map_comap_eq_of_le
        ((hφ_range U).mp ⟨hU.1, hU.2.2⟩)) }

lemma pure_lane_count {t : ℕ} (ht : 0 < t) {d : ℕ} (hd : thresh t < d) :
    letI : Fintype (Submodule F2 (W t)) := Fintype.ofFinite _
    (((Finset.univ : Finset (Submodule F2 (W t))).filter (goodU ht)).filter
      (fun U : Submodule F2 (W t) => Module.finrank F2 U = d)).card =
    2 * Nat.card {V : Submodule F2 (Fin (3 * t - 2) → F2) // Module.finrank F2 V = d} := by
  letI : Fintype (Submodule F2 (W t)) := Fintype.ofFinite _
  have hd_pos : 0 < d := by
    have : 1 ≤ thresh t := by unfold thresh; split_ifs <;> omega
    omega
  let A := ((Finset.univ : Finset (Submodule F2 (W t))).filter (goodU ht)).filter
    (fun U : Submodule F2 (W t) => Module.finrank F2 U = d)
  let A0 := (Finset.univ : Finset (Submodule F2 (W t))).filter
    (fun U : Submodule F2 (W t) => goodU ht U ∧ Module.finrank F2 U = d ∧
      U ≤ LinearMap.range (embLane (t := t) 0 (by decide)))
  let A1 := (Finset.univ : Finset (Submodule F2 (W t))).filter
    (fun U : Submodule F2 (W t) => goodU ht U ∧ Module.finrank F2 U = d ∧
      U ≤ LinearMap.range (embLane (t := t) 1 (by decide)))
  have hdis : Disjoint A0 A1 := by
    apply Finset.disjoint_filter.mpr
    intro U _ hU0 hU1
    have hbot : U = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      ext i
      by_cases hp : i.val % 2 = 0
      · exact (mem_range_embLane_iff 1 (by decide) x).mp (hU1.2.2 hx) i (by omega)
      · exact (mem_range_embLane_iff 0 (by decide) x).mp (hU0.2.2 hx) i hp
    rw [hbot, finrank_bot] at hU0
    omega
  have hun : A0 ∪ A1 = A := by
    ext U
    simp only [A0, A1, A, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨hg, hrk, _⟩ | ⟨hg, hrk, _⟩) <;> exact ⟨hg, hrk⟩
    · rintro ⟨hg, hrk⟩
      have hnmix : ¬ (0 < sitesOf (suppU U) 0 ∧ 0 < sitesOf (suppU U) 1) := by
        intro hmix
        have hle := mixed_finrank_le ht hg hmix.1 hmix.2
        omega
      by_cases h1 : sitesOf (suppU U) 1 = 0
      · left
        refine ⟨hg, hrk, ?_⟩
        intro x hx
        rw [mem_range_embLane_iff 0 (by decide)]
        intro i hi
        have hi1 : i.val % 2 = 1 := by omega
        by_contra hx0
        have hiS : i ∈ suppU U := Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, hx0⟩
        have hpos : 0 < sitesOf (suppU U) 1 :=
          Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hiS, hi1⟩⟩
        omega
      · have h0 : sitesOf (suppU U) 0 = 0 := by omega
        right
        refine ⟨hg, hrk, ?_⟩
        intro x hx
        rw [mem_range_embLane_iff 1 (by decide)]
        intro i hi
        have hi0 : i.val % 2 = 0 := by omega
        by_contra hx0
        have hiS : i ∈ suppU U := Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, hx0⟩
        have hpos : 0 < sitesOf (suppU U) 0 :=
          Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hiS, hi0⟩⟩
        omega
  change A.card = _
  rw [← hun, Finset.card_union_of_disjoint hdis, card_lane_eq ht 0 (by decide) d,
    card_lane_eq ht 1 (by decide) d, two_mul]

end PureCount

end PEqualNP.Outside.L_lib_888_aux

theorem PEqualNP.Outside.L_lib_888 : (∀ (t : ℕ) (hpos : 0 < t),
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let n := 6*t
  let a := 3*t
  let W := Fin n → F
  letI : Fintype (Submodule F W) := Fintype.ofFinite _
  let next := fun i : Fin n =>
    (⟨(i.val+1) % n, Nat.mod_lt _ (Nat.mul_pos (Nat.succ_pos 5) hpos)⟩ : Fin n)
  let h := fun (i : Fin n) (b : Fin 4) =>
    if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2)
    then (1:F) else 0
  let good := fun U : Submodule F W =>
    (∀ x ∈ U, ∀ b : Fin 4, (∑ i, h i b * x i) = 0) ∧
    (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
  let supp := fun U : Submodule F W =>
    Finset.univ.filter (fun i : Fin n => ∃ x ∈ U, x i ≠ 0)
  let sites := fun (S : Finset (Fin n)) (p : ℕ) =>
    (S.filter (fun i => i.val % 2 = p)).card
  let spaces := (Finset.univ : Finset (Submodule F W)).filter good
  let mixed := spaces.filter (fun U => 0 < sites (supp U) 0 ∧ 0 < sites (supp U) 1)
  let threshold := if t = 1 then 1 else if t = 2 then 2 else a-5
  mixed.sup (fun U => Module.finrank F U) = threshold ∧
    ∀ d : ℕ, threshold < d →
      (spaces.filter (fun U : Submodule F W => Module.finrank F U = d)).card =
        2 * Nat.card {U : Submodule F (Fin (a-2) → F) // Module.finrank F U = d}) := by
  intro t hpos F n a W next h good supp sites spaces mixed threshold
  have hnext : ∀ i : Fin n, next i = PEqualNP.Outside.L_lib_888_aux.nxt hpos i := fun _ => rfl
  have hh : ∀ i b, h i b = PEqualNP.Outside.L_lib_888_aux.hVec i b := fun i b => by
    dsimp only [h, PEqualNP.Outside.L_lib_888_aux.hVec]
    split_ifs <;> rfl
  have hgood : ∀ U : Submodule F W, good U ↔ PEqualNP.Outside.L_lib_888_aux.goodU hpos U := fun U => by
    dsimp only [good, PEqualNP.Outside.L_lib_888_aux.goodU]
    simp only [hh, hnext]
    exact Iff.rfl
  have hsupp : ∀ U : Submodule F W, supp U = PEqualNP.Outside.L_lib_888_aux.suppU U := fun U => by
    ext i
    simp only [supp, PEqualNP.Outside.L_lib_888_aux.suppU, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.rfl
  have hsites : ∀ (S : Finset (Fin n)) (p : ℕ), sites S p = PEqualNP.Outside.L_lib_888_aux.sitesOf S p := by
    intro S p
    dsimp only [sites, PEqualNP.Outside.L_lib_888_aux.sitesOf]
    congr 1
    ext i
    simp
  have hthresh : threshold = PEqualNP.Outside.L_lib_888_aux.thresh t := by
    dsimp only [threshold, PEqualNP.Outside.L_lib_888_aux.thresh, a]
    split_ifs <;> rfl
  constructor
  · apply Nat.le_antisymm
    · apply Finset.sup_le
      intro U hU
      have hU' : good U ∧ 0 < sites (supp U) 0 ∧ 0 < sites (supp U) 1 := by
        simpa only [mixed, spaces, Finset.mem_filter, Finset.mem_univ, true_and] using hU
      rw [hgood, hsupp, hsites, hsites] at hU'
      rw [hthresh]
      exact PEqualNP.Outside.L_lib_888_aux.mixed_finrank_le hpos hU'.1 hU'.2.1 hU'.2.2
    · obtain ⟨U, hg, h0, h1, hrk⟩ := PEqualNP.Outside.L_lib_888_aux.witness_exists hpos
      refine Finset.le_sup_of_le (b := U) ?_ (by rw [hthresh, ← hrk])
      simp only [mixed, spaces, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hgood, hsupp, hsites, hsites]
      exact ⟨hg, h0, h1⟩
  · intro d hd
    have hd' : PEqualNP.Outside.L_lib_888_aux.thresh t < d := hthresh ▸ hd
    have hpc := PEqualNP.Outside.L_lib_888_aux.pure_lane_count hpos hd'
    rw [← hpc]
    congr 1
    ext U
    simp only [spaces, Finset.mem_filter, Finset.mem_univ, true_and, hgood]
    exact Iff.rfl
