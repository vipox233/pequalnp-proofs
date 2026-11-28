import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1217

def dOf (m : Nat) : Nat := 3 * m + 2

def MOf (m : Nat) : Nat := Nat.fib (dOf m - 1) + Nat.fib (dOf m + 1)

def cOf (m : Nat) : Nat :=
  (Nat.fib (2 * dOf m - 1) ^ 2 * Nat.fib (dOf m) ^ 2 * ((MOf m - 1) / 2)) % MOf m

def BOf (m : Nat) : Nat := 6 * dOf m - 4

lemma dOf_ge_two (m : Nat) : 2 ≤ dOf m := by
  unfold dOf
  omega

lemma BOf_ge_eight (m : Nat) : 8 ≤ BOf m := by
  unfold BOf dOf
  omega

lemma BOf_pos (m : Nat) : 0 < BOf m := by
  have := BOf_ge_eight m
  omega

lemma fib_mod_two_triple (k : Nat) :
    Nat.fib (3 * k + 1) % 2 = 1 ∧
    Nat.fib (3 * k + 2) % 2 = 1 ∧
    Nat.fib (3 * k + 3) % 2 = 0 := by
  induction k with
  | zero =>
    simp [Nat.fib_add_two]
  | succ k ih =>
    rcases ih with ⟨h1, h2, h3⟩
    have e1 : Nat.fib (3 * (k + 1) + 1) = Nat.fib (3 * k + 2) + Nat.fib (3 * k + 3) := by
      have : 3 * (k + 1) + 1 = (3 * k + 2) + 2 := by omega
      rw [this, Nat.fib_add_two]
    have e2 : Nat.fib (3 * (k + 1) + 2) = Nat.fib (3 * k + 3) + Nat.fib (3 * (k + 1) + 1) := by
      have : 3 * (k + 1) + 2 = (3 * k + 3) + 2 := by omega
      rw [this, Nat.fib_add_two]
      have : 3 * k + 3 + 1 = 3 * (k + 1) + 1 := by omega
      rw [this]
    have e3 : Nat.fib (3 * (k + 1) + 3) = Nat.fib (3 * (k + 1) + 1) + Nat.fib (3 * (k + 1) + 2) := by
      have : 3 * (k + 1) + 3 = (3 * (k + 1) + 1) + 2 := by omega
      rw [this, Nat.fib_add_two]
    omega

lemma MOf_mod_two (m : Nat) : MOf m % 2 = 1 := by
  unfold MOf dOf
  have h := fib_mod_two_triple m
  have e1 : 3 * m + 2 - 1 = 3 * m + 1 := by omega
  have e2 : 3 * m + 2 + 1 = 3 * m + 3 := by omega
  rw [e1, e2]
  omega

lemma two_pow_lt_MOf (m : Nat) : 2 ^ m < MOf m := by
  induction m with
  | zero =>
    unfold MOf dOf
    simp [Nat.fib_add_two]
  | succ m ih =>
    have hstep : 2 * MOf m ≤ MOf (m + 1) := by
      unfold MOf dOf
      set k := 3 * m + 1
      have a1 : 3 * m + 2 - 1 = k := by omega
      have a2 : 3 * m + 2 + 1 = k + 2 := by omega
      have a3 : 3 * (m + 1) + 2 - 1 = k + 3 := by omega
      have a4 : 3 * (m + 1) + 2 + 1 = k + 5 := by omega
      rw [a1, a2, a3, a4]
      have f2 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
      have f3 : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
      have f4 : Nat.fib (k + 4) = Nat.fib (k + 2) + Nat.fib (k + 3) := Nat.fib_add_two
      have f5 : Nat.fib (k + 5) = Nat.fib (k + 3) + Nat.fib (k + 4) := Nat.fib_add_two
      omega
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    omega

lemma MOf_pos (m : Nat) : 0 < MOf m := by
  have h := two_pow_lt_MOf m
  have hp : 0 < 2 ^ m := Nat.pow_pos (by omega)
  omega

lemma two_mul_half_MOf (m : Nat) : 2 * ((MOf m - 1) / 2) = MOf m - 1 := by
  have h1 := MOf_mod_two m
  have h2 := MOf_pos m
  omega

lemma coprime_two_MOf (m : Nat) : Nat.Coprime 2 (MOf m) := by
  have h1 := MOf_mod_two m
  rw [Nat.coprime_two_left]
  exact Nat.odd_iff.mpr h1

lemma fib_two_mul_dOf (m : Nat) : Nat.fib (2 * dOf m) = Nat.fib (dOf m) * MOf m := by
  have hd := dOf_ge_two m
  have h1 : 2 * dOf m = (dOf m - 1) + dOf m + 1 := by omega
  have h2 : dOf m - 1 + 1 = dOf m := by omega
  rw [h1, Nat.fib_add, h2]
  unfold MOf
  ring

lemma coprime_fib_dOf_MOf (m : Nat) : Nat.Coprime (Nat.fib (dOf m)) (MOf m) := by
  have hd := dOf_ge_two m
  have hadd : Nat.fib (dOf m + 1) = Nat.fib (dOf m - 1) + Nat.fib (dOf m) :=
    Nat.fib_add_one (by omega)
  have hM : MOf m = 2 * Nat.fib (dOf m - 1) + Nat.fib (dOf m) := by
    unfold MOf
    omega
  rw [hM, Nat.coprime_add_self_right]
  have hodd : Nat.fib (dOf m) % 2 = 1 := by
    unfold dOf
    exact (fib_mod_two_triple m).2.1
  have hcop2 : Nat.Coprime (Nat.fib (dOf m)) 2 := by
    rw [Nat.coprime_two_right]
    exact Nat.odd_iff.mpr hodd
  have hcopf : Nat.Coprime (Nat.fib (dOf m)) (Nat.fib (dOf m - 1)) := by
    have h := (Nat.fib_coprime_fib_succ (dOf m - 1)).symm
    have heq : dOf m - 1 + 1 = dOf m := by omega
    rwa [heq] at h
  exact hcop2.mul_right hcopf

lemma coprime_fib_two_dOf_sub_one_MOf (m : Nat) :
    Nat.Coprime (Nat.fib (2 * dOf m - 1)) (MOf m) := by
  have hd := dOf_ge_two m
  have h := Nat.fib_coprime_fib_succ (2 * dOf m - 1)
  have heq : 2 * dOf m - 1 + 1 = 2 * dOf m := by omega
  rw [heq, fib_two_mul_dOf] at h
  exact h.coprime_dvd_right (dvd_mul_left (MOf m) (Nat.fib (dOf m)))

lemma coprime_half_MOf (m : Nat) : Nat.Coprime ((MOf m - 1) / 2) (MOf m) := by
  have h1 := two_mul_half_MOf m
  have h2 := MOf_pos m
  set q := (MOf m - 1) / 2
  have hM : MOf m = 1 + 2 * q := by omega
  rw [hM, Nat.coprime_add_mul_right_right]
  exact Nat.coprime_one_right q

lemma coprime_cOf_MOf (m : Nat) : Nat.Coprime (cOf m) (MOf m) := by
  unfold cOf
  set X := Nat.fib (2 * dOf m - 1) ^ 2 * Nat.fib (dOf m) ^ 2 * ((MOf m - 1) / 2)
  have hX : Nat.Coprime X (MOf m) := by
    exact (((coprime_fib_two_dOf_sub_one_MOf m).pow_left 2).mul_left
      ((coprime_fib_dOf_MOf m).pow_left 2)).mul_left (coprime_half_MOf m)
  rw [Nat.coprime_iff_gcd_eq_one] at hX ⊢
  rw [← Nat.gcd_rec (MOf m) X, Nat.gcd_comm]
  exact hX

def vtx (m : Nat) (i : Fin m) (off : Fin (BOf m)) : Fin (m * BOf m) :=
  ⟨i.val * BOf m + off.val, by
    have hi : i.val + 1 ≤ m := i.isLt
    have ho : off.val < BOf m := off.isLt
    have hmul : (i.val + 1) * BOf m ≤ m * BOf m := Nat.mul_le_mul_right (BOf m) hi
    have hexp : (i.val + 1) * BOf m = i.val * BOf m + BOf m := Nat.succ_mul i.val (BOf m)
    omega⟩

def ownerOf (m : Nat) (v : Fin (m * BOf m)) : Fin m :=
  ⟨v.val / BOf m, Nat.div_lt_of_lt_mul (lt_of_lt_of_eq v.isLt (Nat.mul_comm m (BOf m)))⟩

def offOf (m : Nat) (v : Fin (m * BOf m)) : Fin (BOf m) :=
  ⟨v.val % BOf m, Nat.mod_lt v.val (BOf_pos m)⟩

def portOf (m : Nat) (p : Fin m × Bool) : Fin (m * BOf m) :=
  vtx m p.1 ⟨if p.2 then 1 else 0, by
    have := BOf_ge_eight m
    cases p.2 <;> simp <;> omega⟩

lemma ownerOf_vtx (m : Nat) (i : Fin m) (off : Fin (BOf m)) :
    ownerOf m (vtx m i off) = i := by
  ext
  simp only [ownerOf, vtx]
  rw [Nat.mul_comm i.val (BOf m), Nat.mul_add_div (BOf_pos m), Nat.div_eq_of_lt off.isLt, Nat.add_zero]

lemma offOf_vtx (m : Nat) (i : Fin m) (off : Fin (BOf m)) :
    offOf m (vtx m i off) = off := by
  ext
  simp only [offOf, vtx]
  rw [Nat.mul_comm i.val (BOf m), Nat.mul_add_mod, Nat.mod_eq_of_lt off.isLt]

lemma vtx_ownerOf_offOf (m : Nat) (v : Fin (m * BOf m)) :
    vtx m (ownerOf m v) (offOf m v) = v := by
  ext
  simp only [vtx, ownerOf, offOf]
  rw [Nat.mul_comm (v.val / BOf m) (BOf m)]
  exact Nat.div_add_mod v.val (BOf m)

lemma vtx_eq_iff (m : Nat) (i1 i2 : Fin m) (o1 o2 : Fin (BOf m)) :
    vtx m i1 o1 = vtx m i2 o2 ↔ i1 = i2 ∧ o1 = o2 := by
  constructor
  · intro h
    constructor
    · have := congrArg (ownerOf m) h
      simpa [ownerOf_vtx] using this
    · have := congrArg (offOf m) h
      simpa [offOf_vtx] using this
  · rintro ⟨rfl, rfl⟩
    rfl

lemma ownerOf_portOf (m : Nat) (p : Fin m × Bool) : ownerOf m (portOf m p) = p.1 := by
  unfold portOf
  exact ownerOf_vtx m p.1 _

lemma offOf_portOf_val (m : Nat) (p : Fin m × Bool) :
    (offOf m (portOf m p)).val = if p.2 then 1 else 0 := by
  unfold portOf
  rw [offOf_vtx]

lemma portOf_injective (m : Nat) : Function.Injective (portOf m) := by
  intro p1 p2 h
  have h1 : p1.1 = p2.1 := by
    have := congrArg (ownerOf m) h
    simpa [ownerOf_portOf] using this
  have h2 : p1.2 = p2.2 := by
    have := congrArg (fun v => (offOf m v).val) h
    simp only [offOf_portOf_val] at this
    cases hp1 : p1.2 <;> cases hp2 : p2.2 <;> simp [hp1, hp2] at this ⊢
  exact Prod.ext h1 h2

lemma eq_portOf_of_off_lt_two (m : Nat) (v : Fin (m * BOf m)) (h : (offOf m v).val < 2) :
    v = portOf m (ownerOf m v, Nat.beq (offOf m v).val 1) := by
  have hvo := (vtx_ownerOf_offOf m v).symm
  conv_lhs => rw [hvo]
  unfold portOf
  congr 1
  ext
  simp only []
  by_cases h0 : (offOf m v).val = 0
  · simp [h0]
  · have h1 : (offOf m v).val = 1 := by omega
    simp [h1]

def s0Of (_m : Nat) : Nat := 6
def s3Of (m : Nat) : Nat := 2 * dOf m + 3
def s1Of (m : Nat) : Nat := 4 * dOf m
def s2Of (m : Nat) : Nat := 5 * dOf m - 2

def L0Of (m : Nat) : Nat := 2 * dOf m - 3
def L1Of (m : Nat) : Nat := dOf m - 2

def blockDir (m : Nat) (x y : Nat) : Prop :=
  let s0 := s0Of m
  let s3 := s3Of m
  let s1 := s1Of m
  let s2 := s2Of m
  let B := BOf m
  (x = 0 ∧ y = 2) ∨ (x = 2 ∧ y = 3) ∨ (x = 3 ∧ y = 4) ∨ (x = 4 ∧ y = 5) ∨ (x = 1 ∧ y = 5) ∨
  (x = 2 ∧ y = s0) ∨ (s0 ≤ x ∧ x + 1 < s3 ∧ y = x + 1) ∨
  (x = 5 ∧ y = s3) ∨ (s3 ≤ x ∧ x + 1 < s1 ∧ y = x + 1) ∨
  (s1 < s2 ∧ x = 3 ∧ y = s1) ∨ (s1 ≤ x ∧ x + 1 < s2 ∧ y = x + 1) ∨
  (s2 < B ∧ x = 4 ∧ y = s2) ∨ (s2 ≤ x ∧ x + 1 < B ∧ y = x + 1)

def blockAdj (m : Nat) (a b : Fin (BOf m)) : Prop :=
  blockDir m a.val b.val ∨ blockDir m b.val a.val

lemma blockDir_lt (m : Nat) {x y : Nat} (h : blockDir m x y) : x < y := by
  unfold blockDir s0Of s3Of s1Of s2Of BOf dOf at h
  omega

lemma blockAdj_irrefl (m : Nat) (a : Fin (BOf m)) : ¬ blockAdj m a a := by
  rintro (h | h) <;> exact Nat.lt_irrefl a.val (blockDir_lt m h)

lemma blockAdj_symm (m : Nat) (a b : Fin (BOf m)) : blockAdj m a b ↔ blockAdj m b a := by
  unfold blockAdj
  tauto

def offShore (m : Nat) (x : Nat) : Bool :=
  if x = 0 then false
  else if x = 1 then true
  else if x = 2 then true
  else if x = 3 then false
  else if x = 4 then true
  else if x = 5 then false
  else if x < s3Of m then (x - s0Of m) % 2 == 1
  else if x < s1Of m then (x - s3Of m) % 2 == 0
  else if x < s2Of m then (x - s1Of m) % 2 == 0
  else (x - s2Of m) % 2 == 1

def shoreOf (m : Nat) (v : Fin (m * BOf m)) : Bool :=
  offShore m (offOf m v).val

lemma offShore_blockDir_ne (m : Nat) {x y : Nat} (h : blockDir m x y) :
    offShore m x ≠ offShore m y := by
  unfold blockDir at h
  have hd : 2 ≤ dOf m := dOf_ge_two m
  have hs0 : s0Of m = 6 := rfl
  have hs3 : s3Of m = 2 * dOf m + 3 := rfl
  have hs1 : s1Of m = 4 * dOf m := rfl
  have hs2 : s2Of m = 5 * dOf m - 2 := rfl
  have hB : BOf m = 6 * dOf m - 4 := rfl
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨h1, h2, rfl⟩ | ⟨rfl, rfl⟩ | ⟨h1, h2, rfl⟩ |
    ⟨hl, rfl, rfl⟩ | ⟨h1, h2, rfl⟩ | ⟨hl, rfl, rfl⟩ | ⟨h1, h2, rfl⟩
  · simp [offShore]
  · simp [offShore]
  · simp [offShore]
  · simp [offShore]
  · simp [offShore]
  · simp only [offShore]
    have c1 : ¬ (s0Of m = 0) := by omega
    have c2 : ¬ (s0Of m = 1) := by omega
    have c3 : ¬ (s0Of m = 2) := by omega
    have c4 : ¬ (s0Of m = 3) := by omega
    have c5 : ¬ (s0Of m = 4) := by omega
    have c6 : ¬ (s0Of m = 5) := by omega
    have c7 : s0Of m < s3Of m := by omega
    simp [c1, c2, c3, c4, c5, c6, c7]
  · simp only [offShore]
    have bx0 : ¬ (x = 0) := by omega
    have bx1 : ¬ (x = 1) := by omega
    have bx2 : ¬ (x = 2) := by omega
    have bx3 : ¬ (x = 3) := by omega
    have bx4 : ¬ (x = 4) := by omega
    have bx5 : ¬ (x = 5) := by omega
    have bx7 : x < s3Of m := by omega
    have by0 : ¬ (x + 1 = 0) := by omega
    have by1 : ¬ (x + 1 = 1) := by omega
    have by2 : ¬ (x + 1 = 2) := by omega
    have by3 : ¬ (x + 1 = 3) := by omega
    have by4 : ¬ (x + 1 = 4) := by omega
    have by5 : ¬ (x + 1 = 5) := by omega
    simp only [bx0, bx1, bx2, bx3, bx4, bx5, bx7, by0, by1, by2, by3, by4, by5, h2, ↓reduceIte]
    intro heq
    have : (x - s0Of m) % 2 = (x + 1 - s0Of m) % 2 := by
      cases hpar : (x - s0Of m) % 2 == 1 <;> simp_all
    omega
  · simp only [offShore]
    have c1 : ¬ (s3Of m = 0) := by omega
    have c2 : ¬ (s3Of m = 1) := by omega
    have c3 : ¬ (s3Of m = 2) := by omega
    have c4 : ¬ (s3Of m = 3) := by omega
    have c5 : ¬ (s3Of m = 4) := by omega
    have c6 : ¬ (s3Of m = 5) := by omega
    have c8 : s3Of m < s1Of m := by omega
    simp [c1, c2, c3, c4, c5, c6, c8]
  · simp only [offShore]
    have bx0 : ¬ (x = 0) := by omega
    have bx1 : ¬ (x = 1) := by omega
    have bx2 : ¬ (x = 2) := by omega
    have bx3 : ¬ (x = 3) := by omega
    have bx4 : ¬ (x = 4) := by omega
    have bx5 : ¬ (x = 5) := by omega
    have bx7 : ¬ (x < s3Of m) := by omega
    have bx8 : x < s1Of m := by omega
    have by0 : ¬ (x + 1 = 0) := by omega
    have by1 : ¬ (x + 1 = 1) := by omega
    have by2 : ¬ (x + 1 = 2) := by omega
    have by3 : ¬ (x + 1 = 3) := by omega
    have by4 : ¬ (x + 1 = 4) := by omega
    have by5 : ¬ (x + 1 = 5) := by omega
    have by7 : ¬ (x + 1 < s3Of m) := by omega
    simp only [bx0, bx1, bx2, bx3, bx4, bx5, bx7, bx8, by0, by1, by2, by3, by4, by5, by7, h2, ↓reduceIte]
    intro heq
    have : (x - s3Of m) % 2 = (x + 1 - s3Of m) % 2 := by
      cases hpar : (x - s3Of m) % 2 == 0 <;> simp_all
    omega
  · simp only [offShore]
    have c1 : ¬ (s1Of m = 0) := by omega
    have c2 : ¬ (s1Of m = 1) := by omega
    have c3 : ¬ (s1Of m = 2) := by omega
    have c4 : ¬ (s1Of m = 3) := by omega
    have c5 : ¬ (s1Of m = 4) := by omega
    have c6 : ¬ (s1Of m = 5) := by omega
    have c7 : ¬ (s1Of m < s3Of m) := by omega
    simp [c1, c2, c3, c4, c5, c6, c7, hl]
  · simp only [offShore]
    have bx0 : ¬ (x = 0) := by omega
    have bx1 : ¬ (x = 1) := by omega
    have bx2 : ¬ (x = 2) := by omega
    have bx3 : ¬ (x = 3) := by omega
    have bx4 : ¬ (x = 4) := by omega
    have bx5 : ¬ (x = 5) := by omega
    have bx7 : ¬ (x < s3Of m) := by omega
    have bx8 : ¬ (x < s1Of m) := by omega
    have bx9 : x < s2Of m := by omega
    have by0 : ¬ (x + 1 = 0) := by omega
    have by1 : ¬ (x + 1 = 1) := by omega
    have by2 : ¬ (x + 1 = 2) := by omega
    have by3 : ¬ (x + 1 = 3) := by omega
    have by4 : ¬ (x + 1 = 4) := by omega
    have by5 : ¬ (x + 1 = 5) := by omega
    have by7 : ¬ (x + 1 < s3Of m) := by omega
    have by8 : ¬ (x + 1 < s1Of m) := by omega
    simp only [bx0, bx1, bx2, bx3, bx4, bx5, bx7, bx8, bx9, by0, by1, by2, by3, by4, by5, by7, by8, h2, ↓reduceIte]
    intro heq
    have : (x - s1Of m) % 2 = (x + 1 - s1Of m) % 2 := by
      cases hpar : (x - s1Of m) % 2 == 0 <;> simp_all
    omega
  · simp only [offShore]
    have c1 : ¬ (s2Of m = 0) := by omega
    have c2 : ¬ (s2Of m = 1) := by omega
    have c3 : ¬ (s2Of m = 2) := by omega
    have c4 : ¬ (s2Of m = 3) := by omega
    have c5 : ¬ (s2Of m = 4) := by omega
    have c6 : ¬ (s2Of m = 5) := by omega
    have c7 : ¬ (s2Of m < s3Of m) := by omega
    have c8 : ¬ (s2Of m < s1Of m) := by omega
    simp [c1, c2, c3, c4, c5, c6, c7, c8]
  · simp only [offShore]
    have bx0 : ¬ (x = 0) := by omega
    have bx1 : ¬ (x = 1) := by omega
    have bx2 : ¬ (x = 2) := by omega
    have bx3 : ¬ (x = 3) := by omega
    have bx4 : ¬ (x = 4) := by omega
    have bx5 : ¬ (x = 5) := by omega
    have bx7 : ¬ (x < s3Of m) := by omega
    have bx8 : ¬ (x < s1Of m) := by omega
    have bx9 : ¬ (x < s2Of m) := by omega
    have by0 : ¬ (x + 1 = 0) := by omega
    have by1 : ¬ (x + 1 = 1) := by omega
    have by2 : ¬ (x + 1 = 2) := by omega
    have by3 : ¬ (x + 1 = 3) := by omega
    have by4 : ¬ (x + 1 = 4) := by omega
    have by5 : ¬ (x + 1 = 5) := by omega
    have by7 : ¬ (x + 1 < s3Of m) := by omega
    have by8 : ¬ (x + 1 < s1Of m) := by omega
    have by9 : ¬ (x + 1 < s2Of m) := by omega
    simp only [bx0, bx1, bx2, bx3, bx4, bx5, bx7, bx8, bx9, by0, by1, by2, by3, by4, by5, by7, by8, by9, ↓reduceIte]
    intro heq
    have : (x - s2Of m) % 2 = (x + 1 - s2Of m) % 2 := by
      cases hpar : (x - s2Of m) % 2 == 1 <;> simp_all
    omega

lemma offShore_blockAdj_ne (m : Nat) (a b : Fin (BOf m)) (h : blockAdj m a b) :
    offShore m a.val ≠ offShore m b.val := by
  rcases h with h | h
  · exact offShore_blockDir_ne m h
  · exact (offShore_blockDir_ne m h).symm

lemma offShore_port (m : Nat) (x : Nat) (hx : x < 2) : offShore m x = Nat.beq x 1 := by
  by_cases h0 : x = 0
  · simp [h0, offShore]; rfl
  · have h1 : x = 1 := by omega
    simp [h1, offShore]

def HAdj (m : Nat) (G : (Fin m × Bool) → Finset (Fin m × Bool))
    (u v : Fin (m * BOf m)) : Prop :=
  (ownerOf m u = ownerOf m v ∧ blockAdj m (offOf m u) (offOf m v)) ∨
  (ownerOf m u ≠ ownerOf m v ∧ (offOf m u).val < 2 ∧ (offOf m v).val < 2 ∧
    (ownerOf m v, Nat.beq (offOf m v).val 1) ∈ G (ownerOf m u, Nat.beq (offOf m u).val 1))

noncomputable def HOf (m : Nat) (G : (Fin m × Bool) → Finset (Fin m × Bool))
    (u : Fin (m * BOf m)) : Finset (Fin (m * BOf m)) :=
  letI := Classical.propDecidable
  Finset.univ.filter (fun v => HAdj m G u v)

lemma mem_HOf_iff (m : Nat) (G : (Fin m × Bool) → Finset (Fin m × Bool))
    (u v : Fin (m * BOf m)) : v ∈ HOf m G u ↔ HAdj m G u v := by
  classical
  unfold HOf
  simp

lemma HOf_irrefl (m : Nat) (G : (Fin m × Bool) → Finset (Fin m × Bool))
    (v : Fin (m * BOf m)) : v ∉ HOf m G v := by
  rw [mem_HOf_iff]
  rintro (⟨_, h⟩ | ⟨hne, _⟩)
  · exact blockAdj_irrefl m (offOf m v) h
  · exact hne rfl

lemma HOf_symm (m : Nat) (G : (Fin m × Bool) → Finset (Fin m × Bool))
    (hG_symm : ∀ p r, r ∈ G p ↔ p ∈ G r)
    (u v : Fin (m * BOf m)) : v ∈ HOf m G u ↔ u ∈ HOf m G v := by
  rw [mem_HOf_iff, mem_HOf_iff]
  unfold HAdj
  constructor
  · rintro (⟨ho, ha⟩ | ⟨ho, hu, hv, hg⟩)
    · exact Or.inl ⟨ho.symm, (blockAdj_symm m _ _).mp ha⟩
    · exact Or.inr ⟨ho.symm, hv, hu, (hG_symm _ _).mp hg⟩
  · rintro (⟨ho, ha⟩ | ⟨ho, hv, hu, hg⟩)
    · exact Or.inl ⟨ho.symm, (blockAdj_symm m _ _).mp ha⟩
    · exact Or.inr ⟨ho.symm, hu, hv, (hG_symm _ _).mp hg⟩

lemma HOf_bipartite (m : Nat) (G : (Fin m × Bool) → Finset (Fin m × Bool))
    (hG_bip : ∀ p, ∀ r ∈ G p, p.2 ≠ r.2)
    (u v : Fin (m * BOf m)) (hv : v ∈ HOf m G u) : shoreOf m u ≠ shoreOf m v := by
  rw [mem_HOf_iff] at hv
  unfold shoreOf
  rcases hv with ⟨_, ha⟩ | ⟨_, hu, hv', hg⟩
  · exact offShore_blockAdj_ne m _ _ ha
  · rw [offShore_port m _ hu, offShore_port m _ hv']
    exact hG_bip _ _ hg

lemma blockAdj_card_le_three (m : Nat) (a : Fin (BOf m)) :
    letI := Classical.propDecidable
    ((Finset.univ : Finset (Fin (BOf m))).filter (fun b => blockAdj m a b)).card ≤ 3 := by
  classical
  have hd : 2 ≤ dOf m := dOf_ge_two m
  have hs0 : s0Of m = 6 := rfl
  have hs3 : s3Of m = 2 * dOf m + 3 := rfl
  have hs1 : s1Of m = 4 * dOf m := rfl
  have hs2 : s2Of m = 5 * dOf m - 2 := rfl
  have hB : BOf m = 6 * dOf m - 4 := rfl
  have hbound : ∃ n1 n2 n3 : Nat, ∀ b : Fin (BOf m), blockAdj m a b →
      b.val = n1 ∨ b.val = n2 ∨ b.val = n3 := by
    by_cases h0 : a.val = 0
    · refine ⟨2, 2, 2, fun b hb => ?_⟩
      unfold blockAdj blockDir at hb
      omega
    by_cases h1 : a.val = 1
    · refine ⟨5, 5, 5, fun b hb => ?_⟩
      unfold blockAdj blockDir at hb
      omega
    by_cases h2 : a.val = 2
    · refine ⟨0, 3, s0Of m, fun b hb => ?_⟩
      unfold blockAdj blockDir at hb
      omega
    by_cases h3 : a.val = 3
    · refine ⟨2, 4, s1Of m, fun b hb => ?_⟩
      unfold blockAdj blockDir at hb
      omega
    by_cases h4 : a.val = 4
    · refine ⟨3, 5, s2Of m, fun b hb => ?_⟩
      unfold blockAdj blockDir at hb
      omega
    by_cases h5 : a.val = 5
    · refine ⟨1, 4, s3Of m, fun b hb => ?_⟩
      unfold blockAdj blockDir at hb
      omega
    by_cases h6 : a.val = s0Of m
    · refine ⟨2, a.val + 1, 2, fun b hb => ?_⟩
      unfold blockAdj blockDir at hb
      omega
    by_cases h7 : a.val = s3Of m
    · refine ⟨5, a.val + 1, 5, fun b hb => ?_⟩
      unfold blockAdj blockDir at hb
      omega
    by_cases h8 : a.val = s1Of m
    · refine ⟨3, a.val + 1, 3, fun b hb => ?_⟩
      unfold blockAdj blockDir at hb
      omega
    by_cases h9 : a.val = s2Of m
    · refine ⟨4, a.val + 1, 4, fun b hb => ?_⟩
      unfold blockAdj blockDir at hb
      omega
    · refine ⟨a.val - 1, a.val + 1, a.val - 1, fun b hb => ?_⟩
      unfold blockAdj blockDir at hb
      omega
  rcases hbound with ⟨n1, n2, n3, hsub⟩
  set S := (Finset.univ : Finset (Fin (BOf m))).filter (fun b => blockAdj m a b)
  have hinj : (S.image Fin.val).card = S.card :=
    Finset.card_image_of_injective S Fin.val_injective
  have hsub' : S.image Fin.val ⊆ ({n1, n2, n3} : Finset Nat) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨b, hb, rfl⟩
    have hba : blockAdj m a b := (Finset.mem_filter.mp hb).2
    have hor := hsub b hba
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hor
  calc S.card = (S.image Fin.val).card := hinj.symm
    _ ≤ ({n1, n2, n3} : Finset Nat).card := Finset.card_le_card hsub'
    _ ≤ 3 := by
      have c1 := Finset.card_insert_le n1 ({n2, n3} : Finset Nat)
      have c2 := Finset.card_insert_le n2 ({n3} : Finset Nat)
      simp at c1 c2
      omega

lemma HOf_card_le_three (m : Nat) (G : (Fin m × Bool) → Finset (Fin m × Bool))
    (hG_deg : ∀ p, p ∉ G p ∧ (G p).card ≤ 3)
    (hG_symm : ∀ p r, r ∈ G p ↔ p ∈ G r)
    (hG_mark : ∀ i, (i, true) ∈ G (i, false))
    (u : Fin (m * BOf m)) : (HOf m G u).card ≤ 3 := by
  classical
  by_cases hport : (offOf m u).val < 2
  · set i := ownerOf m u
    set b := Nat.beq (offOf m u).val 1
    have hmark : (i, !b) ∈ G (i, b) := by
      cases hb : b
      · simpa using hG_mark i
      · exact (hG_symm _ _).mp (hG_mark i)
    set extSet := ((G (i, b)).erase (i, !b)).image (portOf m)
    set intVtx : Fin (m * BOf m) :=
      vtx m i ⟨if b then 5 else 2, by have := BOf_ge_eight m; cases b <;> simp <;> omega⟩
    have hsub : HOf m G u ⊆ insert intVtx extSet := by
      intro v hv
      rw [mem_HOf_iff] at hv
      rw [Finset.mem_insert]
      rcases hv with ⟨ho, ha⟩ | ⟨ho, hu, hv', hg⟩
      · left
        have hv_eq : v = vtx m i (offOf m v) := by
          rw [show i = ownerOf m v from ho]
          exact (vtx_ownerOf_offOf m v).symm
        rw [hv_eq]
        congr 1
        ext
        have hd : 2 ≤ dOf m := dOf_ge_two m
        have hs0 : s0Of m = 6 := rfl
        have hs3 : s3Of m = 2 * dOf m + 3 := rfl
        have hs1 : s1Of m = 4 * dOf m := rfl
        have hs2 : s2Of m = 5 * dOf m - 2 := rfl
        have hB : BOf m = 6 * dOf m - 4 := rfl
        unfold blockAdj blockDir at ha
        by_cases h0 : (offOf m u).val = 0
        · have hb0 : b = false := by simp [b, h0]; rfl
          simp [hb0]
          omega
        · have h1 : (offOf m u).val = 1 := by omega
          have hb1 : b = true := by simp [b, h1]
          simp [hb1]
          omega
      · right
        rw [Finset.mem_image]
        refine ⟨(ownerOf m v, Nat.beq (offOf m v).val 1), ?_, (eq_portOf_of_off_lt_two m v hv').symm⟩
        rw [Finset.mem_erase]
        refine ⟨?_, hg⟩
        intro heq
        exact ho (congrArg Prod.fst heq).symm
    have hcard_erase : ((G (i, b)).erase (i, !b)).card ≤ 2 := by
      rw [Finset.card_erase_of_mem hmark]
      have := (hG_deg (i, b)).2
      omega
    calc (HOf m G u).card ≤ (insert intVtx extSet).card := Finset.card_le_card hsub
      _ ≤ extSet.card + 1 := Finset.card_insert_le _ _
      _ ≤ ((G (i, b)).erase (i, !b)).card + 1 := Nat.add_le_add_right Finset.card_image_le 1
      _ ≤ 3 := by omega
  · set blkSet := (Finset.univ : Finset (Fin (BOf m))).filter (fun b => blockAdj m (offOf m u) b)
    have hsub : HOf m G u ⊆ blkSet.image (vtx m (ownerOf m u)) := by
      intro v hv
      rw [mem_HOf_iff] at hv
      rcases hv with ⟨ho, ha⟩ | ⟨_, hu, _, _⟩
      · rw [Finset.mem_image]
        refine ⟨offOf m v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, ?_⟩
        rw [ho]
        exact vtx_ownerOf_offOf m v
      · exact (hport hu).elim
    calc (HOf m G u).card ≤ (blkSet.image (vtx m (ownerOf m u))).card := Finset.card_le_card hsub
      _ ≤ blkSet.card := Finset.card_image_le
      _ ≤ 3 := blockAdj_card_le_three m (offOf m u)

def isPathIndep (k : Nat) (A : Finset (Fin k)) : Prop :=
  ∀ i : Fin k, ∀ j : Fin k, i.val + 1 = j.val → i ∈ A → j ∉ A

noncomputable def pathSet (k : Nat) (forbidZero : Bool) : Finset (Finset (Fin k)) :=
  letI := Classical.propDecidable
  Finset.univ.filter (fun A =>
    isPathIndep k A ∧ (forbidZero = true → ∀ h : 0 < k, ⟨0, h⟩ ∉ A))

lemma card_pathSet_pair (k : Nat) :
    (pathSet k false).card = Nat.fib (k + 2) ∧
    (pathSet k true).card = Nat.fib (k + 1) := by
  classical
  induction k with
  | zero =>
    constructor
    · have heq : pathSet 0 false = {∅} := by
        ext A
        simp only [pathSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro _
          ext x
          exact Fin.elim0 x
        · rintro rfl
          refine ⟨fun i => Fin.elim0 i, fun h => by simp at h⟩
      rw [heq]
      simp [Nat.fib_add_two]
    · have heq : pathSet 0 true = {∅} := by
        ext A
        simp only [pathSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro _
          ext x
          exact Fin.elim0 x
        · rintro rfl
          refine ⟨fun i => Fin.elim0 i, fun _ h => by omega⟩
      rw [heq]
      simp
  | succ k ih =>
    have htrue : (pathSet (k + 1) true).card = (pathSet k false).card := by
      refine Finset.card_bij'
        (fun A _ => Finset.univ.filter (fun i : Fin k => i.succ ∈ A))
        (fun A' _ => A'.image Fin.succ)
        ?_ ?_ ?_ ?_
      · intro A hA
        simp only [pathSet, Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
        refine ⟨?_, fun h => by simp at h⟩
        intro i j hij hi hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
        exact hA.1 i.succ j.succ (by simp [Fin.val_succ, hij]) hi hj
      · intro A' hA'
        simp only [pathSet, Finset.mem_filter, Finset.mem_univ, true_and] at hA' ⊢
        refine ⟨?_, ?_⟩
        · intro i j hij hi hj
          rcases Finset.mem_image.mp hi with ⟨i', hi', rfl⟩
          rcases Finset.mem_image.mp hj with ⟨j', hj', rfl⟩
          have hij' : i'.val + 1 = j'.val := by simp [Fin.val_succ] at hij; omega
          exact hA'.1 i' j' hij' hi' hj'
        · intro _ _ h0
          rcases Finset.mem_image.mp h0 with ⟨i', _, hi'⟩
          have := congrArg Fin.val hi'
          simp [Fin.val_succ] at this
      · intro A hA
        simp only [pathSet, Finset.mem_filter, Finset.mem_univ, true_and] at hA
        ext x
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨i, hi, rfl⟩
          exact hi
        · intro hx
          rcases Fin.eq_zero_or_eq_succ x with rfl | ⟨i, rfl⟩
          · exact (hA.2 trivial (Nat.succ_pos k) hx).elim
          · exact ⟨i, hx, rfl⟩
      · intro A' _
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · rintro ⟨j, hj, hjeq⟩
          have : j = i := Fin.succ_injective _ hjeq
          rwa [← this]
        · intro hi
          exact ⟨i, hi, rfl⟩
    have hfalse : (pathSet (k + 1) false).card =
        (pathSet (k + 1) true).card + (pathSet k true).card := by
      set S0 := (pathSet (k + 1) false).filter (fun A => (⟨0, Nat.succ_pos k⟩ : Fin (k + 1)) ∉ A)
      set S1 := (pathSet (k + 1) false).filter (fun A => (⟨0, Nat.succ_pos k⟩ : Fin (k + 1)) ∈ A)
      have hsplit : (pathSet (k + 1) false).card = S0.card + S1.card := by
        have h := Finset.card_filter_add_card_filter_not
          (s := pathSet (k + 1) false)
          (p := fun A => (⟨0, Nat.succ_pos k⟩ : Fin (k + 1)) ∈ A)
        dsimp only [S0, S1]
        omega
      have hS0 : S0 = pathSet (k + 1) true := by
        ext A
        simp only [S0, pathSet, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨hi, _⟩, h0⟩
          exact ⟨hi, fun _ _ => h0⟩
        · rintro ⟨hi, h0⟩
          exact ⟨⟨hi, fun h => by simp at h⟩, h0 trivial (Nat.succ_pos k)⟩
      have hS1 : S1.card = (pathSet k true).card := by
        refine Finset.card_bij'
          (fun A _ => Finset.univ.filter (fun i : Fin k => i.succ ∈ A))
          (fun A' _ => insert ⟨0, Nat.succ_pos k⟩ (A'.image Fin.succ))
          ?_ ?_ ?_ ?_
        · intro A hA
          simp only [S1, pathSet, Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
          refine ⟨?_, ?_⟩
          · intro i j hij hi hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
            exact hA.1.1 i.succ j.succ (by simp [Fin.val_succ, hij]) hi hj
          · intro _ hk h0
            exact hA.1.1 ⟨0, Nat.succ_pos k⟩ (⟨0, hk⟩ : Fin k).succ (by simp [Fin.val_succ]) hA.2 h0
        · intro A' hA'
          simp only [S1, pathSet, Finset.mem_filter, Finset.mem_univ, true_and] at hA' ⊢
          refine ⟨⟨?_, fun h => by simp at h⟩, Finset.mem_insert_self _ _⟩
          intro i j hij hi hj
          rw [Finset.mem_insert] at hi hj
          rcases hi with rfl | hi
          · rcases hj with rfl | hj
            · simp at hij
            · rcases Finset.mem_image.mp hj with ⟨j', hj', hjeq⟩
              have hjval : j'.val = 0 := by
                have := congrArg Fin.val hjeq
                simp [Fin.val_succ] at this hij
                omega
              have hk : 0 < k := by omega
              have hj'eq : j' = ⟨0, hk⟩ := Fin.ext hjval
              rw [hj'eq] at hj'
              exact hA'.2 trivial hk hj'
          · rcases Finset.mem_image.mp hi with ⟨i', hi', rfl⟩
            rcases hj with rfl | hj
            · simp [Fin.val_succ] at hij
            · rcases Finset.mem_image.mp hj with ⟨j', hj', rfl⟩
              have hij' : i'.val + 1 = j'.val := by simp [Fin.val_succ] at hij; omega
              exact hA'.1 i' j' hij' hi' hj'
        · intro A hA
          simp only [S1, pathSet, Finset.mem_filter, Finset.mem_univ, true_and] at hA
          ext x
          simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro (rfl | ⟨i, hi, rfl⟩)
            · exact hA.2
            · exact hi
          · intro hx
            rcases Fin.eq_zero_or_eq_succ x with rfl | ⟨i, rfl⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨i, hx, rfl⟩
        · intro A' _
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_image]
          constructor
          · rintro (h0 | ⟨j, hj, hjeq⟩)
            · have := congrArg Fin.val h0
              simp [Fin.val_succ] at this
            · have : j = i := Fin.succ_injective _ hjeq
              rwa [← this]
          · intro hi
            exact Or.inr ⟨i, hi, rfl⟩
      rw [hsplit, hS0, hS1]
    constructor
    · rw [hfalse, htrue, ih.1, ih.2]
      have hfib : Nat.fib (k + 1 + 2) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
      omega
    · rw [htrue, ih.1]

lemma card_pathSet (k : Nat) (forbidZero : Bool) :
    (pathSet k forbidZero).card = if forbidZero then Nat.fib (k + 1) else Nat.fib (k + 2) := by
  cases forbidZero
  · exact (card_pathSet_pair k).1
  · exact (card_pathSet_pair k).2

def isBlockIndep (m : Nat) (A : Finset (Fin (BOf m))) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ¬ blockAdj m a b

def off0 (m : Nat) : Fin (BOf m) := ⟨0, by have := BOf_ge_eight m; omega⟩
def off1 (m : Nat) : Fin (BOf m) := ⟨1, by have := BOf_ge_eight m; omega⟩

noncomputable def ZSet (m : Nat) (b0 b1 : Bool) : Finset (Finset (Fin (BOf m))) :=
  letI := Classical.propDecidable
  Finset.univ.filter (fun A =>
    isBlockIndep m A ∧
    (off0 m ∈ A ↔ b0 = true) ∧
    (off1 m ∈ A ↔ b1 = true))

noncomputable def ZCount (m : Nat) (b0 b1 : Bool) : Nat := (ZSet m b0 b1).card

def spineOk (b0 b1 c0 c1 c2 c3 : Bool) : Bool :=
  !(b0 && c0) && !(c0 && c1) && !(c1 && c2) && !(c2 && c3) && !(b1 && c3)

def tailVal (L : Nat) (c : Bool) : Nat :=
  if c then Nat.fib (L + 1) else Nat.fib (L + 2)

lemma univ_bool4_eq :
    (Finset.univ : Finset (Bool × Bool × Bool × Bool)) =
    {(false, false, false, false), (false, false, false, true),
     (false, false, true, false), (false, false, true, true),
     (false, true, false, false), (false, true, false, true),
     (false, true, true, false), (false, true, true, true),
     (true, false, false, false), (true, false, false, true),
     (true, false, true, false), (true, false, true, true),
     (true, true, false, false), (true, true, false, true),
     (true, true, true, false), (true, true, true, true)} := by
  decide

lemma ZCount_eq_sum (m : Nat) (b0 b1 : Bool) :
    ZCount m b0 b1 =
      ∑ q : Bool × Bool × Bool × Bool,
        if spineOk b0 b1 q.1 q.2.1 q.2.2.1 q.2.2.2 = true then
          tailVal (L0Of m) q.1 * tailVal (L0Of m) q.2.2.2 *
          tailVal (L1Of m) q.2.1 * tailVal (L1Of m) q.2.2.1
        else 0 := by
  classical
  have hd : 2 ≤ dOf m := dOf_ge_two m
  have hB8 : 8 ≤ BOf m := BOf_ge_eight m
  have hs0 : s0Of m = 6 := rfl
  have hs3 : s3Of m = 2 * dOf m + 3 := rfl
  have hs1 : s1Of m = 4 * dOf m := rfl
  have hs2 : s2Of m = 5 * dOf m - 2 := rfl
  have hB : BOf m = 6 * dOf m - 4 := rfl
  have hL0 : L0Of m = 2 * dOf m - 3 := rfl
  have hL1 : L1Of m = dOf m - 2 := rfl
  let f : Finset (Fin (BOf m)) → Bool × Bool × Bool × Bool := fun A =>
    (decide (⟨2, by omega⟩ ∈ A), decide (⟨3, by omega⟩ ∈ A),
     decide (⟨4, by omega⟩ ∈ A), decide (⟨5, by omega⟩ ∈ A))
  unfold ZCount
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl ?_
  intro q _
  rcases q with ⟨c0, c1, c2, c3⟩
  by_cases hsp : spineOk b0 b1 c0 c1 c2 c3 = true
  · simp only [hsp, ↓reduceIte]
    set P0 := pathSet (L0Of m) c0
    set P3 := pathSet (L0Of m) c3
    set P1 := pathSet (L1Of m) c1
    set P2 := pathSet (L1Of m) c2
    have hprod : (P0 ×ˢ P3 ×ˢ P1 ×ˢ P2).card =
        tailVal (L0Of m) c0 * tailVal (L0Of m) c3 * tailVal (L1Of m) c1 * tailVal (L1Of m) c2 := by
      simp only [Finset.card_product, P0, P3, P1, P2, card_pathSet, tailVal]
      ring
    rw [← hprod]
    let toTup : Finset (Fin (BOf m)) →
        Finset (Fin (L0Of m)) × Finset (Fin (L0Of m)) ×
        Finset (Fin (L1Of m)) × Finset (Fin (L1Of m)) := fun A =>
      (Finset.univ.filter (fun k : Fin (L0Of m) => ⟨s0Of m + k.val, by omega⟩ ∈ A),
       Finset.univ.filter (fun k : Fin (L0Of m) => ⟨s3Of m + k.val, by omega⟩ ∈ A),
       Finset.univ.filter (fun k : Fin (L1Of m) => ⟨s1Of m + k.val, by omega⟩ ∈ A),
       Finset.univ.filter (fun k : Fin (L1Of m) => ⟨s2Of m + k.val, by omega⟩ ∈ A))
    let fromTup : Finset (Fin (L0Of m)) × Finset (Fin (L0Of m)) ×
        Finset (Fin (L1Of m)) × Finset (Fin (L1Of m)) → Finset (Fin (BOf m)) := fun T =>
      Finset.univ.filter (fun x : Fin (BOf m) =>
        if x.val = 0 then b0 = true
        else if x.val = 1 then b1 = true
        else if x.val = 2 then c0 = true
        else if x.val = 3 then c1 = true
        else if x.val = 4 then c2 = true
        else if x.val = 5 then c3 = true
        else if h0 : x.val < s3Of m then ⟨x.val - s0Of m, by omega⟩ ∈ T.1
        else if h3 : x.val < s1Of m then ⟨x.val - s3Of m, by omega⟩ ∈ T.2.1
        else if h1 : x.val < s2Of m then ⟨x.val - s1Of m, by omega⟩ ∈ T.2.2.1
        else ⟨x.val - s2Of m, by omega⟩ ∈ T.2.2.2)
    refine Finset.card_bij' (fun A _ => toTup A) (fun T _ => fromTup T) ?_ ?_ ?_ ?_
    · intro A hA
      simp only [Finset.mem_filter, ZSet, Finset.mem_univ, true_and] at hA
      rcases hA with ⟨⟨hind, hb0, hb1⟩, hfq⟩
      have hc0 : (⟨2, by omega⟩ : Fin (BOf m)) ∈ A ↔ c0 = true := by
        have := congrArg Prod.fst hfq
        simp only [f, decide_eq_true_iff] at this
        exact ⟨fun h => by simpa [h] using this.symm, fun h => by
          have : decide (⟨2, by omega⟩ ∈ A) = true := this.trans h
          exact of_decide_eq_true this⟩
      have hc1 : (⟨3, by omega⟩ : Fin (BOf m)) ∈ A ↔ c1 = true := by
        have := congrArg (fun p => p.2.1) hfq
        simp only [f] at this
        exact ⟨fun h => by simpa [h] using this.symm, fun h => of_decide_eq_true (this.trans h)⟩
      have hc2 : (⟨4, by omega⟩ : Fin (BOf m)) ∈ A ↔ c2 = true := by
        have := congrArg (fun p => p.2.2.1) hfq
        simp only [f] at this
        exact ⟨fun h => by simpa [h] using this.symm, fun h => of_decide_eq_true (this.trans h)⟩
      have hc3 : (⟨5, by omega⟩ : Fin (BOf m)) ∈ A ↔ c3 = true := by
        have := congrArg (fun p => p.2.2.2) hfq
        simp only [f] at this
        exact ⟨fun h => by simpa [h] using this.symm, fun h => of_decide_eq_true (this.trans h)⟩
      simp only [Finset.mem_product, P0, P3, P1, P2, pathSet, toTup, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · intro i j hij hi hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
        refine hind _ hi _ hj (Or.inl ?_)
        unfold blockDir
        right; right; right; right; right; right; left
        dsimp only []
        have := i.isLt; have := j.isLt; omega
      · intro hc0t hk h0
        refine hind ⟨2, by omega⟩ (hc0.mpr hc0t) ⟨s0Of m + 0, by omega⟩ h0 (Or.inl ?_)
        unfold blockDir
        right; right; right; right; right; left
        dsimp only []
        omega
      · intro i j hij hi hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
        refine hind _ hi _ hj (Or.inl ?_)
        unfold blockDir
        right; right; right; right; right; right; right; right; left
        dsimp only []
        have := i.isLt; have := j.isLt; omega
      · intro hc3t hk h0
        refine hind ⟨5, by omega⟩ (hc3.mpr hc3t) ⟨s3Of m + 0, by omega⟩ h0 (Or.inl ?_)
        unfold blockDir
        right; right; right; right; right; right; right; left
        dsimp only []
        omega
      · intro i j hij hi hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
        refine hind _ hi _ hj (Or.inl ?_)
        unfold blockDir
        right; right; right; right; right; right; right; right; right; right; left
        dsimp only []
        have := i.isLt; have := j.isLt; omega
      · intro hc1t hk h0
        refine hind ⟨3, by omega⟩ (hc1.mpr hc1t) ⟨s1Of m + 0, by omega⟩ h0 (Or.inl ?_)
        unfold blockDir
        right; right; right; right; right; right; right; right; right; left
        dsimp only []
        omega
      · intro i j hij hi hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
        refine hind _ hi _ hj (Or.inl ?_)
        unfold blockDir
        right; right; right; right; right; right; right; right; right; right; right; right
        dsimp only []
        have := i.isLt; have := j.isLt; omega
      · intro hc2t hk h0
        refine hind ⟨4, by omega⟩ (hc2.mpr hc2t) ⟨s2Of m + 0, by omega⟩ h0 (Or.inl ?_)
        unfold blockDir
        right; right; right; right; right; right; right; right; right; right; right; left
        dsimp only []
        omega
    · intro T hT
      simp only [Finset.mem_product, P0, P3, P1, P2, pathSet, Finset.mem_filter, Finset.mem_univ, true_and] at hT
      rcases hT with ⟨⟨hp0, hz0⟩, ⟨hp3, hz3⟩, ⟨hp1, hz1⟩, ⟨hp2, hz2⟩⟩
      simp only [Finset.mem_filter, ZSet, Finset.mem_univ, true_and]
      have hdir : ∀ a b : Fin (BOf m), a ∈ fromTup T → b ∈ fromTup T → ¬ blockDir m a.val b.val := by
        intro a b ha hb hbd
        simp only [fromTup, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        unfold spineOk at hsp
        unfold blockDir at hbd
        rcases hbd with ⟨ha0, hb2⟩ | ⟨ha2, hb3⟩ | ⟨ha3, hb4⟩ | ⟨ha4, hb5⟩ | ⟨ha1, hb5⟩ |
          ⟨ha2, hbs0⟩ | ⟨h1, h2, hxy⟩ | ⟨ha5, hbs3⟩ | ⟨h1, h2, hxy⟩ |
          ⟨hl, ha3, hbs1⟩ | ⟨h1, h2, hxy⟩ | ⟨hl, ha4, hbs2⟩ | ⟨h1, h2, hxy⟩
        · simp [ha0] at ha; simp [hb2] at hb; simp [ha, hb] at hsp
        · simp [ha2] at ha; simp [hb3] at hb; simp [ha, hb] at hsp
        · simp [ha3] at ha; simp [hb4] at hb; simp [ha, hb] at hsp
        · simp [ha4] at ha; simp [hb5] at hb; simp [ha, hb] at hsp
        · simp [ha1] at ha; simp [hb5] at hb; simp [ha, hb] at hsp
        · simp [ha2] at ha
          have b0 : ¬ (b.val = 0) := by omega
          have b1' : ¬ (b.val = 1) := by omega
          have b2 : ¬ (b.val = 2) := by omega
          have b3 : ¬ (b.val = 3) := by omega
          have b4 : ¬ (b.val = 4) := by omega
          have b5 : ¬ (b.val = 5) := by omega
          have bs : b.val < s3Of m := by omega
          simp only [b0, b1', b2, b3, b4, b5, bs, ↓reduceDIte, ↓reduceIte] at hb
          have heq : (⟨b.val - s0Of m, by omega⟩ : Fin (L0Of m)) = ⟨0, by omega⟩ :=
            Fin.ext (by dsimp only []; omega)
          rw [heq] at hb
          exact hz0 ha (by omega) hb
        · have a0 : ¬ (a.val = 0) := by omega
          have a1 : ¬ (a.val = 1) := by omega
          have a2 : ¬ (a.val = 2) := by omega
          have a3 : ¬ (a.val = 3) := by omega
          have a4 : ¬ (a.val = 4) := by omega
          have a5 : ¬ (a.val = 5) := by omega
          have as : a.val < s3Of m := by omega
          have b0 : ¬ (b.val = 0) := by omega
          have b1' : ¬ (b.val = 1) := by omega
          have b2 : ¬ (b.val = 2) := by omega
          have b3 : ¬ (b.val = 3) := by omega
          have b4 : ¬ (b.val = 4) := by omega
          have b5 : ¬ (b.val = 5) := by omega
          have bs : b.val < s3Of m := by omega
          simp only [a0, a1, a2, a3, a4, a5, as, ↓reduceDIte, ↓reduceIte] at ha
          simp only [b0, b1', b2, b3, b4, b5, bs, ↓reduceDIte, ↓reduceIte] at hb
          exact hp0 ⟨a.val - s0Of m, by omega⟩ ⟨b.val - s0Of m, by omega⟩ (by simp; omega) ha hb
        · simp [ha5] at ha
          have b0 : ¬ (b.val = 0) := by omega
          have b1' : ¬ (b.val = 1) := by omega
          have b2 : ¬ (b.val = 2) := by omega
          have b3 : ¬ (b.val = 3) := by omega
          have b4 : ¬ (b.val = 4) := by omega
          have b5 : ¬ (b.val = 5) := by omega
          have bs3' : ¬ (b.val < s3Of m) := by omega
          have bs1' : b.val < s1Of m := by omega
          simp only [b0, b1', b2, b3, b4, b5, bs3', bs1', ↓reduceDIte, ↓reduceIte] at hb
          have heq : (⟨b.val - s3Of m, by omega⟩ : Fin (L0Of m)) = ⟨0, by omega⟩ :=
            Fin.ext (by dsimp only []; omega)
          rw [heq] at hb
          exact hz3 ha (by omega) hb
        · have a0 : ¬ (a.val = 0) := by omega
          have a1 : ¬ (a.val = 1) := by omega
          have a2 : ¬ (a.val = 2) := by omega
          have a3 : ¬ (a.val = 3) := by omega
          have a4 : ¬ (a.val = 4) := by omega
          have a5 : ¬ (a.val = 5) := by omega
          have as3 : ¬ (a.val < s3Of m) := by omega
          have as1 : a.val < s1Of m := by omega
          have b0 : ¬ (b.val = 0) := by omega
          have b1' : ¬ (b.val = 1) := by omega
          have b2 : ¬ (b.val = 2) := by omega
          have b3 : ¬ (b.val = 3) := by omega
          have b4 : ¬ (b.val = 4) := by omega
          have b5 : ¬ (b.val = 5) := by omega
          have bs3' : ¬ (b.val < s3Of m) := by omega
          have bs1' : b.val < s1Of m := by omega
          simp only [a0, a1, a2, a3, a4, a5, as3, as1, ↓reduceDIte, ↓reduceIte] at ha
          simp only [b0, b1', b2, b3, b4, b5, bs3', bs1', ↓reduceDIte, ↓reduceIte] at hb
          exact hp3 ⟨a.val - s3Of m, by omega⟩ ⟨b.val - s3Of m, by omega⟩ (by simp; omega) ha hb
        · simp [ha3] at ha
          have b0 : ¬ (b.val = 0) := by omega
          have b1' : ¬ (b.val = 1) := by omega
          have b2 : ¬ (b.val = 2) := by omega
          have b3 : ¬ (b.val = 3) := by omega
          have b4 : ¬ (b.val = 4) := by omega
          have b5 : ¬ (b.val = 5) := by omega
          have bs3' : ¬ (b.val < s3Of m) := by omega
          have bs1' : ¬ (b.val < s1Of m) := by omega
          have bs2' : b.val < s2Of m := by omega
          simp only [b0, b1', b2, b3, b4, b5, bs3', bs1', bs2', ↓reduceDIte, ↓reduceIte] at hb
          have heq : (⟨b.val - s1Of m, by omega⟩ : Fin (L1Of m)) = ⟨0, by omega⟩ :=
            Fin.ext (by dsimp only []; omega)
          rw [heq] at hb
          exact hz1 ha (by omega) hb
        · have a0 : ¬ (a.val = 0) := by omega
          have a1 : ¬ (a.val = 1) := by omega
          have a2 : ¬ (a.val = 2) := by omega
          have a3 : ¬ (a.val = 3) := by omega
          have a4 : ¬ (a.val = 4) := by omega
          have a5 : ¬ (a.val = 5) := by omega
          have as3 : ¬ (a.val < s3Of m) := by omega
          have as1 : ¬ (a.val < s1Of m) := by omega
          have as2 : a.val < s2Of m := by omega
          have b0 : ¬ (b.val = 0) := by omega
          have b1' : ¬ (b.val = 1) := by omega
          have b2 : ¬ (b.val = 2) := by omega
          have b3 : ¬ (b.val = 3) := by omega
          have b4 : ¬ (b.val = 4) := by omega
          have b5 : ¬ (b.val = 5) := by omega
          have bs3' : ¬ (b.val < s3Of m) := by omega
          have bs1' : ¬ (b.val < s1Of m) := by omega
          have bs2' : b.val < s2Of m := by omega
          simp only [a0, a1, a2, a3, a4, a5, as3, as1, as2, ↓reduceDIte, ↓reduceIte] at ha
          simp only [b0, b1', b2, b3, b4, b5, bs3', bs1', bs2', ↓reduceDIte, ↓reduceIte] at hb
          exact hp1 ⟨a.val - s1Of m, by omega⟩ ⟨b.val - s1Of m, by omega⟩ (by simp; omega) ha hb
        · simp [ha4] at ha
          have b0 : ¬ (b.val = 0) := by omega
          have b1' : ¬ (b.val = 1) := by omega
          have b2 : ¬ (b.val = 2) := by omega
          have b3 : ¬ (b.val = 3) := by omega
          have b4 : ¬ (b.val = 4) := by omega
          have b5 : ¬ (b.val = 5) := by omega
          have bs3' : ¬ (b.val < s3Of m) := by omega
          have bs1' : ¬ (b.val < s1Of m) := by omega
          have bs2' : ¬ (b.val < s2Of m) := by omega
          simp only [b0, b1', b2, b3, b4, b5, bs3', bs1', bs2', ↓reduceDIte, ↓reduceIte] at hb
          have heq : (⟨b.val - s2Of m, by omega⟩ : Fin (L1Of m)) = ⟨0, by omega⟩ :=
            Fin.ext (by dsimp only []; omega)
          rw [heq] at hb
          exact hz2 ha (by omega) hb
        · have a0 : ¬ (a.val = 0) := by omega
          have a1 : ¬ (a.val = 1) := by omega
          have a2 : ¬ (a.val = 2) := by omega
          have a3 : ¬ (a.val = 3) := by omega
          have a4 : ¬ (a.val = 4) := by omega
          have a5 : ¬ (a.val = 5) := by omega
          have as3 : ¬ (a.val < s3Of m) := by omega
          have as1 : ¬ (a.val < s1Of m) := by omega
          have as2 : ¬ (a.val < s2Of m) := by omega
          have b0 : ¬ (b.val = 0) := by omega
          have b1' : ¬ (b.val = 1) := by omega
          have b2 : ¬ (b.val = 2) := by omega
          have b3 : ¬ (b.val = 3) := by omega
          have b4 : ¬ (b.val = 4) := by omega
          have b5 : ¬ (b.val = 5) := by omega
          have bs3' : ¬ (b.val < s3Of m) := by omega
          have bs1' : ¬ (b.val < s1Of m) := by omega
          have bs2' : ¬ (b.val < s2Of m) := by omega
          simp only [a0, a1, a2, a3, a4, a5, as3, as1, as2, ↓reduceDIte, ↓reduceIte] at ha
          simp only [b0, b1', b2, b3, b4, b5, bs3', bs1', bs2', ↓reduceDIte, ↓reduceIte] at hb
          exact hp2 ⟨a.val - s2Of m, by omega⟩ ⟨b.val - s2Of m, by omega⟩ (by simp; omega) ha hb
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · intro a ha b hb hab
        rcases hab with hab | hab
        · exact hdir a b ha hb hab
        · exact hdir b a hb ha hab
      · simp [fromTup, off0]
      · simp [fromTup, off1]
      · simp only [f, fromTup, Finset.mem_filter, Finset.mem_univ, true_and]
        cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;> simp
    · intro A hA
      simp only [Finset.mem_filter, ZSet, Finset.mem_univ, true_and] at hA
      rcases hA with ⟨⟨_, hb0, hb1⟩, hfq⟩
      have hc0 : (⟨2, by omega⟩ : Fin (BOf m)) ∈ A ↔ c0 = true := by
        have := congrArg Prod.fst hfq; simp only [f] at this
        exact ⟨fun h => by simpa [h] using this.symm, fun h => of_decide_eq_true (this.trans h)⟩
      have hc1 : (⟨3, by omega⟩ : Fin (BOf m)) ∈ A ↔ c1 = true := by
        have := congrArg (fun p => p.2.1) hfq; simp only [f] at this
        exact ⟨fun h => by simpa [h] using this.symm, fun h => of_decide_eq_true (this.trans h)⟩
      have hc2 : (⟨4, by omega⟩ : Fin (BOf m)) ∈ A ↔ c2 = true := by
        have := congrArg (fun p => p.2.2.1) hfq; simp only [f] at this
        exact ⟨fun h => by simpa [h] using this.symm, fun h => of_decide_eq_true (this.trans h)⟩
      have hc3 : (⟨5, by omega⟩ : Fin (BOf m)) ∈ A ↔ c3 = true := by
        have := congrArg (fun p => p.2.2.2) hfq; simp only [f] at this
        exact ⟨fun h => by simpa [h] using this.symm, fun h => of_decide_eq_true (this.trans h)⟩
      ext x
      simp only [fromTup, toTup, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases x0 : x.val = 0
      · have hx : x = off0 m := Fin.ext x0
        rw [hx]; simpa [off0] using hb0.symm
      by_cases x1 : x.val = 1
      · have hx : x = off1 m := Fin.ext x1
        rw [hx]; simpa [off1] using hb1.symm
      by_cases x2 : x.val = 2
      · have hx : x = ⟨2, by omega⟩ := Fin.ext x2
        rw [hx]; simpa using hc0.symm
      by_cases x3 : x.val = 3
      · have hx : x = ⟨3, by omega⟩ := Fin.ext x3
        rw [hx]; simpa using hc1.symm
      by_cases x4 : x.val = 4
      · have hx : x = ⟨4, by omega⟩ := Fin.ext x4
        rw [hx]; simpa using hc2.symm
      by_cases x5 : x.val = 5
      · have hx : x = ⟨5, by omega⟩ := Fin.ext x5
        rw [hx]; simpa using hc3.symm
      by_cases xs3 : x.val < s3Of m
      · simp only [x0, x1, x2, x3, x4, x5, xs3, ↓reduceDIte, ↓reduceIte]
        have hx : (⟨s0Of m + (x.val - s0Of m), by omega⟩ : Fin (BOf m)) = x :=
          Fin.ext (by dsimp only []; omega)
        rw [hx]
      by_cases xs1 : x.val < s1Of m
      · simp only [x0, x1, x2, x3, x4, x5, xs3, xs1, ↓reduceDIte, ↓reduceIte]
        have hx : (⟨s3Of m + (x.val - s3Of m), by omega⟩ : Fin (BOf m)) = x :=
          Fin.ext (by dsimp only []; omega)
        rw [hx]
      by_cases xs2 : x.val < s2Of m
      · simp only [x0, x1, x2, x3, x4, x5, xs3, xs1, xs2, ↓reduceDIte, ↓reduceIte]
        have hx : (⟨s1Of m + (x.val - s1Of m), by omega⟩ : Fin (BOf m)) = x :=
          Fin.ext (by dsimp only []; omega)
        rw [hx]
      · simp only [x0, x1, x2, x3, x4, x5, xs3, xs1, xs2, ↓reduceDIte, ↓reduceIte]
        have hx : (⟨s2Of m + (x.val - s2Of m), by omega⟩ : Fin (BOf m)) = x :=
          Fin.ext (by dsimp only []; omega)
        rw [hx]
    · intro T _
      rcases T with ⟨T0, T3, T1, T2⟩
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
      · ext k
        simp only [toTup, fromTup, Finset.mem_filter, Finset.mem_univ, true_and]
        have c0' : ¬ (s0Of m + k.val = 0) := by omega
        have c1' : ¬ (s0Of m + k.val = 1) := by omega
        have c2' : ¬ (s0Of m + k.val = 2) := by omega
        have c3' : ¬ (s0Of m + k.val = 3) := by omega
        have c4' : ¬ (s0Of m + k.val = 4) := by omega
        have c5' : ¬ (s0Of m + k.val = 5) := by omega
        have cs : s0Of m + k.val < s3Of m := by omega
        simp only [c0', c1', c2', c3', c4', c5', cs, ↓reduceDIte, ↓reduceIte]
        have hk : (⟨s0Of m + k.val - s0Of m, by omega⟩ : Fin (L0Of m)) = k :=
          Fin.ext (by dsimp only []; omega)
        rw [hk]
      · ext k
        simp only [toTup, fromTup, Finset.mem_filter, Finset.mem_univ, true_and]
        have c0' : ¬ (s3Of m + k.val = 0) := by omega
        have c1' : ¬ (s3Of m + k.val = 1) := by omega
        have c2' : ¬ (s3Of m + k.val = 2) := by omega
        have c3' : ¬ (s3Of m + k.val = 3) := by omega
        have c4' : ¬ (s3Of m + k.val = 4) := by omega
        have c5' : ¬ (s3Of m + k.val = 5) := by omega
        have cs3 : ¬ (s3Of m + k.val < s3Of m) := by omega
        have cs1 : s3Of m + k.val < s1Of m := by omega
        simp only [c0', c1', c2', c3', c4', c5', cs3, cs1, ↓reduceDIte, ↓reduceIte]
        have hk : (⟨s3Of m + k.val - s3Of m, by omega⟩ : Fin (L0Of m)) = k :=
          Fin.ext (by dsimp only []; omega)
        rw [hk]
      · ext k
        simp only [toTup, fromTup, Finset.mem_filter, Finset.mem_univ, true_and]
        have c0' : ¬ (s1Of m + k.val = 0) := by omega
        have c1' : ¬ (s1Of m + k.val = 1) := by omega
        have c2' : ¬ (s1Of m + k.val = 2) := by omega
        have c3' : ¬ (s1Of m + k.val = 3) := by omega
        have c4' : ¬ (s1Of m + k.val = 4) := by omega
        have c5' : ¬ (s1Of m + k.val = 5) := by omega
        have cs3 : ¬ (s1Of m + k.val < s3Of m) := by omega
        have cs1 : ¬ (s1Of m + k.val < s1Of m) := by omega
        have cs2 : s1Of m + k.val < s2Of m := by omega
        simp only [c0', c1', c2', c3', c4', c5', cs3, cs1, cs2, ↓reduceDIte, ↓reduceIte]
        have hk : (⟨s1Of m + k.val - s1Of m, by omega⟩ : Fin (L1Of m)) = k :=
          Fin.ext (by dsimp only []; omega)
        rw [hk]
      · ext k
        simp only [toTup, fromTup, Finset.mem_filter, Finset.mem_univ, true_and]
        have c0' : ¬ (s2Of m + k.val = 0) := by omega
        have c1' : ¬ (s2Of m + k.val = 1) := by omega
        have c2' : ¬ (s2Of m + k.val = 2) := by omega
        have c3' : ¬ (s2Of m + k.val = 3) := by omega
        have c4' : ¬ (s2Of m + k.val = 4) := by omega
        have c5' : ¬ (s2Of m + k.val = 5) := by omega
        have cs3 : ¬ (s2Of m + k.val < s3Of m) := by omega
        have cs1 : ¬ (s2Of m + k.val < s1Of m) := by omega
        have cs2 : ¬ (s2Of m + k.val < s2Of m) := by omega
        simp only [c0', c1', c2', c3', c4', c5', cs3, cs1, cs2, ↓reduceDIte, ↓reduceIte]
        have hk : (⟨s2Of m + k.val - s2Of m, by omega⟩ : Fin (L1Of m)) = k :=
          Fin.ext (by dsimp only []; omega)
        rw [hk]
  · simp only [hsp, Bool.false_eq_true, ↓reduceIte]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro A hA hfq
    simp only [ZSet, Finset.mem_filter, Finset.mem_univ, true_and] at hA
    rcases hA with ⟨hind, hb0, hb1⟩
    have hc0 : (⟨2, by omega⟩ : Fin (BOf m)) ∈ A ↔ c0 = true := by
      have := congrArg Prod.fst hfq; simp only [f] at this
      exact ⟨fun h => by simpa [h] using this.symm, fun h => of_decide_eq_true (this.trans h)⟩
    have hc1 : (⟨3, by omega⟩ : Fin (BOf m)) ∈ A ↔ c1 = true := by
      have := congrArg (fun p => p.2.1) hfq; simp only [f] at this
      exact ⟨fun h => by simpa [h] using this.symm, fun h => of_decide_eq_true (this.trans h)⟩
    have hc2 : (⟨4, by omega⟩ : Fin (BOf m)) ∈ A ↔ c2 = true := by
      have := congrArg (fun p => p.2.2.1) hfq; simp only [f] at this
      exact ⟨fun h => by simpa [h] using this.symm, fun h => of_decide_eq_true (this.trans h)⟩
    have hc3 : (⟨5, by omega⟩ : Fin (BOf m)) ∈ A ↔ c3 = true := by
      have := congrArg (fun p => p.2.2.2) hfq; simp only [f] at this
      exact ⟨fun h => by simpa [h] using this.symm, fun h => of_decide_eq_true (this.trans h)⟩
    have e0 : ¬ (b0 = true ∧ c0 = true) := by
      rintro ⟨h1, h2⟩
      exact hind (off0 m) (hb0.mpr h1) ⟨2, by omega⟩ (hc0.mpr h2) (Or.inl (by unfold blockDir off0; left; exact ⟨rfl, rfl⟩))
    have e1 : ¬ (c0 = true ∧ c1 = true) := by
      rintro ⟨h1, h2⟩
      exact hind ⟨2, by omega⟩ (hc0.mpr h1) ⟨3, by omega⟩ (hc1.mpr h2) (Or.inl (by unfold blockDir; right; left; exact ⟨rfl, rfl⟩))
    have e2 : ¬ (c1 = true ∧ c2 = true) := by
      rintro ⟨h1, h2⟩
      exact hind ⟨3, by omega⟩ (hc1.mpr h1) ⟨4, by omega⟩ (hc2.mpr h2) (Or.inl (by unfold blockDir; right; right; left; exact ⟨rfl, rfl⟩))
    have e3 : ¬ (c2 = true ∧ c3 = true) := by
      rintro ⟨h1, h2⟩
      exact hind ⟨4, by omega⟩ (hc2.mpr h1) ⟨5, by omega⟩ (hc3.mpr h2) (Or.inl (by unfold blockDir; right; right; right; left; exact ⟨rfl, rfl⟩))
    have e4 : ¬ (b1 = true ∧ c3 = true) := by
      rintro ⟨h1, h2⟩
      exact hind (off1 m) (hb1.mpr h1) ⟨5, by omega⟩ (hc3.mpr h2) (Or.inl (by unfold blockDir off1; right; right; right; right; left; exact ⟨rfl, rfl⟩))
    apply hsp
    unfold spineOk
    cases b0 <;> cases b1 <;> cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;> simp_all

lemma ZCount_formulas (m : Nat) :
    let a := Nat.fib (2 * dOf m - 1)
    let b := Nat.fib (2 * dOf m - 2)
    let x := Nat.fib (dOf m)
    ZCount m true true = a ^ 2 * x * MOf m ∧
    ZCount m true false = a ^ 2 * x * MOf m + a * b * x * Nat.fib (dOf m + 1) ∧
    ZCount m false true = a ^ 2 * x * MOf m + a * b * x * Nat.fib (dOf m + 1) ∧
    ZCount m false false =
      a ^ 2 * x * MOf m + 2 * a * b * x * Nat.fib (dOf m + 1) + b ^ 2 * x ^ 2 := by
  have hd : 2 ≤ dOf m := dOf_ge_two m
  have ha : tailVal (L0Of m) false = Nat.fib (2 * dOf m - 1) := by
    unfold tailVal L0Of
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show 2 * dOf m - 3 + 2 = 2 * dOf m - 1 by omega]
  have hb : tailVal (L0Of m) true = Nat.fib (2 * dOf m - 2) := by
    unfold tailVal L0Of
    simp only [↓reduceIte]
    rw [show 2 * dOf m - 3 + 1 = 2 * dOf m - 2 by omega]
  have hx : tailVal (L1Of m) false = Nat.fib (dOf m) := by
    unfold tailVal L1Of
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show dOf m - 2 + 2 = dOf m by omega]
  have hy : tailVal (L1Of m) true = Nat.fib (dOf m - 1) := by
    unfold tailVal L1Of
    simp only [↓reduceIte]
    rw [show dOf m - 2 + 1 = dOf m - 1 by omega]
  have hfadd : Nat.fib (dOf m + 1) = Nat.fib (dOf m - 1) + Nat.fib (dOf m) :=
    Nat.fib_add_one (by omega)
  have hM : MOf m = Nat.fib (dOf m) + 2 * Nat.fib (dOf m - 1) := by
    unfold MOf
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ZCount_eq_sum, univ_bool4_eq]
    simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq, reduceCtorEq, and_false, false_and, or_self, not_false_eq_true,
      spineOk, Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and,
      Bool.not_true, Bool.not_false, ↓reduceIte, Bool.false_eq_true, ha, hb, hx, hy]
    rw [hM]; ring
  · rw [ZCount_eq_sum, univ_bool4_eq]
    simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq, reduceCtorEq, and_false, false_and, or_self, not_false_eq_true,
      spineOk, Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and,
      Bool.not_true, Bool.not_false, ↓reduceIte, Bool.false_eq_true, ha, hb, hx, hy]
    rw [hM, hfadd]; ring
  · rw [ZCount_eq_sum, univ_bool4_eq]
    simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq, reduceCtorEq, and_false, false_and, or_self, not_false_eq_true,
      spineOk, Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and,
      Bool.not_true, Bool.not_false, ↓reduceIte, Bool.false_eq_true, ha, hb, hx, hy]
    rw [hM, hfadd]; ring
  · rw [ZCount_eq_sum, univ_bool4_eq]
    simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq, reduceCtorEq, and_false, false_and, or_self, not_false_eq_true,
      spineOk, Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and,
      Bool.not_true, Bool.not_false, ↓reduceIte, Bool.false_eq_true, ha, hb, hx, hy]
    rw [hM, hfadd]; ring

lemma ZCount_zmod (m : Nat) :
    ((ZCount m true true : Nat) : ZMod (MOf m)) = 0 ∧
    ((ZCount m true false : Nat) : ZMod (MOf m)) = (cOf m : ZMod (MOf m)) ∧
    ((ZCount m false true : Nat) : ZMod (MOf m)) = (cOf m : ZMod (MOf m)) ∧
    ((ZCount m false false : Nat) : ZMod (MOf m)) = 0 := by
  have hd : 2 ≤ dOf m := dOf_ge_two m
  have hf := ZCount_formulas m
  rcases hf with ⟨htt, htf, hft, hff⟩
  set M := MOf m
  set a := Nat.fib (2 * dOf m - 1)
  set b := Nat.fib (2 * dOf m - 2)
  set x := Nat.fib (dOf m)
  set f1 := Nat.fib (dOf m + 1)
  have hM0 : ((M : Nat) : ZMod M) = 0 := ZMod.natCast_self M
  have hfib2d : ((Nat.fib (2 * dOf m) : Nat) : ZMod M) = 0 := by
    rw [fib_two_mul_dOf]
    push_cast
    rw [hM0, mul_zero]
  have hba : (b : ZMod M) = -(a : ZMod M) := by
    have hsum : b + a = Nat.fib (2 * dOf m) := by
      have h1 : 2 * dOf m = (2 * dOf m - 2) + 2 := by omega
      have h2 : 2 * dOf m - 2 + 1 = 2 * dOf m - 1 := by omega
      rw [h1, Nat.fib_add_two, h2]
    have hcast : (b : ZMod M) + (a : ZMod M) = 0 := by
      have := congrArg (fun n : Nat => (n : ZMod M)) hsum
      push_cast at this
      rw [hfib2d] at this
      exact this
    exact eq_neg_of_add_eq_zero_left hcast
  have h2f1 : (2 : ZMod M) * (f1 : ZMod M) = (x : ZMod M) := by
    have hnat : 2 * f1 = M + x := by
      have h1 : f1 = Nat.fib (dOf m - 1) + x := Nat.fib_add_one (by omega)
      have h2 : M = Nat.fib (dOf m - 1) + f1 := rfl
      omega
    have := congrArg (fun n : Nat => (n : ZMod M)) hnat
    push_cast at this
    rw [hM0, zero_add] at this
    exact this
  have h2half : (2 : ZMod M) * (((M - 1) / 2 : Nat) : ZMod M) = -1 := by
    have hnat : 2 * ((M - 1) / 2) + 1 = M := by
      have := two_mul_half_MOf m
      have := MOf_pos m
      omega
    have := congrArg (fun n : Nat => (n : ZMod M)) hnat
    push_cast at this
    rw [hM0] at this
    exact eq_neg_of_add_eq_zero_left this
  have hunit2 : IsUnit (2 : ZMod M) := by
    have := (ZMod.isUnit_iff_coprime 2 M).mpr (coprime_two_MOf m)
    simpa using this
  have hc_cast : ((cOf m : Nat) : ZMod M) =
      (a : ZMod M) ^ 2 * (x : ZMod M) ^ 2 * (((M - 1) / 2 : Nat) : ZMod M) := by
    unfold cOf
    rw [ZMod.natCast_mod]
    push_cast
    rfl
  have htf_zmod : ((ZCount m true false : Nat) : ZMod M) = (cOf m : ZMod M) := by
    apply hunit2.mul_left_cancel
    rw [htf, hc_cast]
    push_cast
    rw [hM0, hba]
    calc (2 : ZMod M) * ((a : ZMod M) ^ 2 * (x : ZMod M) * 0 +
            (a : ZMod M) * -(a : ZMod M) * (x : ZMod M) * (f1 : ZMod M))
        = -((a : ZMod M) ^ 2 * (x : ZMod M) * ((2 : ZMod M) * (f1 : ZMod M))) := by ring
      _ = -((a : ZMod M) ^ 2 * (x : ZMod M) ^ 2) := by rw [h2f1]; ring
      _ = (a : ZMod M) ^ 2 * (x : ZMod M) ^ 2 * (-1) := by ring
      _ = (a : ZMod M) ^ 2 * (x : ZMod M) ^ 2 *
            ((2 : ZMod M) * (((M - 1) / 2 : Nat) : ZMod M)) := by rw [h2half]
      _ = (2 : ZMod M) * ((a : ZMod M) ^ 2 * (x : ZMod M) ^ 2 *
            (((M - 1) / 2 : Nat) : ZMod M)) := by ring
  refine ⟨?_, htf_zmod, ?_, ?_⟩
  · rw [htt]
    push_cast
    rw [hM0, mul_zero]
  · rw [hft, ← htf]
    exact htf_zmod
  · rw [hff]
    push_cast
    rw [hM0, hba]
    calc (a : ZMod M) ^ 2 * (x : ZMod M) * 0 +
          2 * (a : ZMod M) * -(a : ZMod M) * (x : ZMod M) * (f1 : ZMod M) +
          (-(a : ZMod M)) ^ 2 * (x : ZMod M) ^ 2
        = -((a : ZMod M) ^ 2 * (x : ZMod M) * ((2 : ZMod M) * (f1 : ZMod M))) +
          (a : ZMod M) ^ 2 * (x : ZMod M) ^ 2 := by ring
      _ = 0 := by rw [h2f1]; ring

lemma eq_one_of_lt_two_ne_zero {n : Nat} (h2 : n < 2) (h0 : n ≠ 0) : n = 1 := by
  omega

lemma step4_recovery (m : Nat) (G : (Fin m × Bool) → Finset (Fin m × Bool))
    (hG_bip : ∀ p, ∀ r ∈ G p, p.2 ≠ r.2)
    (hG_mark : ∀ i, (i, true) ∈ G (i, false))
    (S : Finset (Fin m)) :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    let live := (Finset.univ : Finset (Fin m × Bool)).filter (fun p => p.1 ∈ S)
    let cover := fun (C : Finset (Fin m × Bool)) => C ⊆ live ∧
      ∀ p ∈ live, ∀ r ∈ G p, r ∈ live → p ∈ C ∨ r ∈ C
    let opt := ((Finset.univ : Finset (Finset (Fin m × Bool))).filter
      (fun C => cover C ∧ ∀ W, cover W → C.card ≤ W.card)).card
    let total := ((Finset.univ : Finset (Finset (Fin (m * BOf m)))).filter
      (fun I => (∀ v ∈ I, ownerOf m v ∈ S) ∧ ∀ u ∈ I, ∀ v ∈ HOf m G u, v ∉ I)).card
    opt ≤ 2 ^ S.card ∧
    total % MOf m = (cOf m ^ S.card * opt) % MOf m ∧
    ∀ t : Nat, t < MOf m → total % MOf m = (cOf m ^ S.card * t) % MOf m → t = opt := by
  dsimp only []
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  set live := (Finset.univ : Finset (Fin m × Bool)).filter (fun p => p.1 ∈ S)
  let cover : Finset (Fin m × Bool) → Prop := fun C =>
    C ⊆ live ∧ ∀ p ∈ live, ∀ r ∈ G p, r ∈ live → p ∈ C ∨ r ∈ C
  set optSet := (Finset.univ : Finset (Finset (Fin m × Bool))).filter
    (fun C => cover C ∧ ∀ W, cover W → C.card ≤ W.card)
  set totalSet := (Finset.univ : Finset (Finset (Fin (m * BOf m)))).filter
    (fun I => (∀ v ∈ I, ownerOf m v ∈ S) ∧ ∀ u ∈ I, ∀ v ∈ HOf m G u, v ∉ I)
  have hshore_cover : cover (S.image (fun i => (i, false))) := by
    refine ⟨?_, ?_⟩
    · intro p hp
      rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    · intro p hp r hrG hr
      have hne : p.2 ≠ r.2 := hG_bip p r hrG
      cases hp2 : p.2
      · left
        rw [Finset.mem_image]
        exact ⟨p.1, (Finset.mem_filter.mp hp).2, Prod.ext rfl hp2.symm⟩
      · right
        have hr2 : r.2 = false := by cases hr2' : r.2 <;> simp_all
        rw [Finset.mem_image]
        exact ⟨r.1, (Finset.mem_filter.mp hr).2, Prod.ext rfl hr2.symm⟩
  have hshore_card : (S.image (fun i => (i, false))).card = S.card :=
    Finset.card_image_of_injective S (fun _ _ h => congrArg Prod.fst h)
  have hcov_ge : ∀ W, cover W → S.card ≤ W.card := by
    intro W hW
    have hsub : S ⊆ W.image Prod.fst := by
      intro i hi
      have hpf : (i, false) ∈ live := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      have hpt : (i, true) ∈ live := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      rcases hW.2 (i, false) hpf (i, true) (hG_mark i) hpt with h | h
      · exact Finset.mem_image.mpr ⟨(i, false), h, rfl⟩
      · exact Finset.mem_image.mpr ⟨(i, true), h, rfl⟩
    calc S.card ≤ (W.image Prod.fst).card := Finset.card_le_card hsub
      _ ≤ W.card := Finset.card_image_le
  set transSet := (Finset.univ : Finset (Finset (Fin m × Bool))).filter (fun P =>
    P ⊆ live ∧
    (∀ i ∈ S, ((i, false) ∈ P ↔ (i, true) ∉ P)) ∧
    (∀ p ∈ P, ∀ r ∈ G p, r ∉ P))
  have hopt_eq_trans : optSet.card = transSet.card := by
    refine Finset.card_bij' (fun C _ => live \ C) (fun P _ => live \ P) ?_ ?_ ?_ ?_
    · intro C hC
      simp only [optSet, Finset.mem_filter, Finset.mem_univ, true_and] at hC
      rcases hC with ⟨hcov, hmin⟩
      have hcard : C.card = S.card := by
        have h1 : C.card ≤ S.card := by
          rw [← hshore_card]
          exact hmin _ hshore_cover
        have h2 : S.card ≤ C.card := hcov_ge C hcov
        exact Nat.le_antisymm h1 h2
      have himg_eq : (C.image Prod.fst).card = C.card := by
        have hsub : S ⊆ C.image Prod.fst := by
          intro i hi
          have hpf : (i, false) ∈ live := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
          have hpt : (i, true) ∈ live := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
          rcases hcov.2 (i, false) hpf (i, true) (hG_mark i) hpt with h | h
          · exact Finset.mem_image.mpr ⟨(i, false), h, rfl⟩
          · exact Finset.mem_image.mpr ⟨(i, true), h, rfl⟩
        have h1 : C.card ≤ (C.image Prod.fst).card := by
          rw [hcard]; exact Finset.card_le_card hsub
        have h2 : (C.image Prod.fst).card ≤ C.card := Finset.card_image_le
        exact Nat.le_antisymm h2 h1
      have hinj := Finset.injOn_of_card_image_eq himg_eq
      simp only [transSet, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨Finset.sdiff_subset, ?_, ?_⟩
      · intro i hi
        have hpf : (i, false) ∈ live := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
        have hpt : (i, true) ∈ live := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
        simp only [Finset.mem_sdiff, hpf, hpt, true_and]
        constructor
        · intro hfn htn
          rcases hcov.2 (i, false) hpf (i, true) (hG_mark i) hpt with h | h
          · exact hfn h
          · exact htn h
        · intro hnt hfC
          by_cases htC : (i, true) ∈ C
          · have heq := hinj hfC htC rfl
            simp at heq
          · exact hnt htC
      · intro p hp r hrG hr
        rw [Finset.mem_sdiff] at hp hr
        rcases hcov.2 p hp.1 r hrG hr.1 with h | h
        · exact hp.2 h
        · exact hr.2 h
    · intro P hP
      simp only [transSet, Finset.mem_filter, Finset.mem_univ, true_and] at hP
      rcases hP with ⟨hPsub, hPopp, hPind⟩
      simp only [optSet, Finset.mem_filter, Finset.mem_univ, true_and]
      have hcov : cover (live \ P) := by
        refine ⟨Finset.sdiff_subset, ?_⟩
        intro p hp r hrG hr
        by_cases hpP : p ∈ P
        · right
          exact Finset.mem_sdiff.mpr ⟨hr, hPind p hpP r hrG⟩
        · left
          exact Finset.mem_sdiff.mpr ⟨hp, hpP⟩
      have hcard : (live \ P).card = S.card := by
        refine Finset.card_bij'
          (fun p _ => p.1)
          (fun i _ => (i, if (i, false) ∈ P then true else false))
          ?_ ?_ ?_ ?_
        · intro p hp
          exact (Finset.mem_filter.mp (Finset.sdiff_subset hp)).2
        · intro i hi
          rw [Finset.mem_sdiff]
          refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, ?_⟩
          by_cases hf : (i, false) ∈ P
          · rw [if_pos hf]
            exact (hPopp i hi).mp hf
          · rw [if_neg hf]
            exact hf
        · intro p hp
          rw [Finset.mem_sdiff] at hp
          have hi : p.1 ∈ S := (Finset.mem_filter.mp hp.1).2
          apply Prod.ext
          · rfl
          · cases hp2 : p.2
            · by_cases hf : (p.1, false) ∈ P
              · have hp_eq : p = (p.1, false) := Prod.ext rfl hp2
                rw [← hp_eq] at hf
                exact (hp.2 hf).elim
              · simp [hf]
            · by_cases hf : (p.1, false) ∈ P
              · simp [hf]
              · have ht : (p.1, true) ∈ P := by
                  by_contra hnt
                  exact hf ((hPopp p.1 hi).mpr hnt)
                have hp_eq : p = (p.1, true) := Prod.ext rfl hp2
                rw [← hp_eq] at ht
                exact (hp.2 ht).elim
        · intro i _
          rfl
      refine ⟨hcov, fun W hW => ?_⟩
      rw [hcard]
      exact hcov_ge W hW
    · intro C hC
      simp only [optSet, Finset.mem_filter, Finset.mem_univ, true_and] at hC
      exact Finset.sdiff_sdiff_eq_self hC.1.1
    · intro P hP
      simp only [transSet, Finset.mem_filter, Finset.mem_univ, true_and] at hP
      exact Finset.sdiff_sdiff_eq_self hP.1
  have hopt_le : optSet.card ≤ 2 ^ S.card := by
    rw [hopt_eq_trans, ← Finset.card_powerset S]
    refine Finset.card_le_card_of_injOn (fun P => S.filter (fun i => (i, true) ∈ P)) ?_ ?_
    · intro P _
      exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
    · intro P1 hP1 P2 hP2 heq
      dsimp only [] at heq
      simp only [Finset.mem_coe, transSet, Finset.mem_filter, Finset.mem_univ, true_and] at hP1 hP2
      ext ⟨i, b⟩
      by_cases hi : i ∈ S
      · have htrue : (i, true) ∈ P1 ↔ (i, true) ∈ P2 := by
          have hmem : i ∈ S.filter (fun j => (j, true) ∈ P1) ↔
              i ∈ S.filter (fun j => (j, true) ∈ P2) := by rw [heq]
          simpa [hi] using hmem
        cases b
        · rw [hP1.2.1 i hi, hP2.2.1 i hi, htrue]
        · exact htrue
      · have hnot : (i, b) ∉ live := by
          simp [live, hi]
        exact ⟨fun h => (hnot (hP1.1 h)).elim, fun h => (hnot (hP2.1 h)).elim⟩
  set extSet := (Finset.univ : Finset (Finset (Fin m × Bool))).filter (fun P =>
    P ⊆ live ∧ ∀ p ∈ P, ∀ r ∈ G p, p.1 ≠ r.1 → r ∉ P)
  let portProj : Finset (Fin (m * BOf m)) → Finset (Fin m × Bool) := fun I =>
    live.filter (fun p => portOf m p ∈ I)
  have hproj_mem : ∀ I ∈ totalSet, portProj I ∈ extSet := by
    intro I hI
    simp only [totalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hI
    simp only [extSet, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro p hp r hrG hne hr
    simp only [portProj, Finset.mem_filter] at hp hr
    have hadj : portOf m r ∈ HOf m G (portOf m p) := by
      rw [mem_HOf_iff]
      right
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [ownerOf_portOf] using hne
      · rw [offOf_portOf_val]; cases p.2 <;> simp
      · rw [offOf_portOf_val]; cases r.2 <;> simp
      · have hp1 : (ownerOf m (portOf m p), Nat.beq (offOf m (portOf m p)).val 1) = p := by
          apply Prod.ext
          · exact ownerOf_portOf m p
          · rw [offOf_portOf_val]; cases p.2 <;> simp <;> rfl
        have hr1 : (ownerOf m (portOf m r), Nat.beq (offOf m (portOf m r)).val 1) = r := by
          apply Prod.ext
          · exact ownerOf_portOf m r
          · rw [offOf_portOf_val]; cases r.2 <;> simp <;> rfl
        rw [hp1, hr1]
        exact hrG
    exact hI.2 (portOf m p) hp.2 (portOf m r) hadj hr.2
  have hfiber_card : ∀ P ∈ extSet,
      (totalSet.filter (fun I => portProj I = P)).card =
      ∏ i ∈ S, ZCount m (decide ((i, false) ∈ P)) (decide ((i, true) ∈ P)) := by
    intro P hP
    simp only [extSet, Finset.mem_filter, Finset.mem_univ, true_and] at hP
    set piSet := Fintype.piFinset (fun i : S => ZSet m (decide ((i.1, false) ∈ P)) (decide ((i.1, true) ∈ P)))
    have hpi_card : piSet.card =
        ∏ i ∈ S, ZCount m (decide ((i, false) ∈ P)) (decide ((i, true) ∈ P)) := by
      rw [Fintype.card_piFinset]
      exact Finset.prod_coe_sort S (fun i => ZCount m (decide ((i, false) ∈ P)) (decide ((i, true) ∈ P)))
    rw [← hpi_card]
    refine Finset.card_bij'
      (fun I _ => fun i : S => Finset.univ.filter (fun o : Fin (BOf m) => vtx m i.1 o ∈ I))
      (fun f _ => Finset.univ.filter (fun v : Fin (m * BOf m) =>
        ∃ hi : ownerOf m v ∈ S, offOf m v ∈ f ⟨ownerOf m v, hi⟩))
      ?_ ?_ ?_ ?_
    · intro I hI
      simp only [Finset.mem_filter, totalSet, Finset.mem_univ, true_and] at hI
      rcases hI with ⟨⟨hown, hind⟩, hproj⟩
      rw [Fintype.mem_piFinset]
      intro i
      simp only [ZSet, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_, ?_⟩
      · intro a ha b hb hab
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        have hH : vtx m i.1 b ∈ HOf m G (vtx m i.1 a) := by
          rw [mem_HOf_iff]
          left
          refine ⟨by simp [ownerOf_vtx], ?_⟩
          simpa [offOf_vtx] using hab
        exact hind (vtx m i.1 a) ha (vtx m i.1 b) hH hb
      · simp only [decide_eq_true_iff]
        have hmemP : (i.1, false) ∈ P ↔ (i.1, false) ∈ portProj I := by rw [hproj]
        rw [hmemP]
        have hlive : (i.1, false) ∈ live := Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.2⟩
        simp only [portProj, Finset.mem_filter, hlive, true_and]
        have heq : vtx m i.1 (off0 m) = portOf m (i.1, false) := by
          unfold portOf off0; rfl
        rw [heq]
      · simp only [decide_eq_true_iff]
        have hmemP : (i.1, true) ∈ P ↔ (i.1, true) ∈ portProj I := by rw [hproj]
        rw [hmemP]
        have hlive : (i.1, true) ∈ live := Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.2⟩
        simp only [portProj, Finset.mem_filter, hlive, true_and]
        have heq : vtx m i.1 (off1 m) = portOf m (i.1, true) := by
          unfold portOf off1; rfl
        rw [heq]
    · intro f hf
      rw [Fintype.mem_piFinset] at hf
      simp only [Finset.mem_filter, totalSet, Finset.mem_univ, true_and]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro v hv
        exact hv.1
      · intro u hu v hvH hv
        rcases hu with ⟨huS, huA⟩
        rcases hv with ⟨hvS, hvA⟩
        rw [mem_HOf_iff] at hvH
        rcases hvH with ⟨ho, hab⟩ | ⟨ho, huo, hvo, hg⟩
        · have hf_u := hf ⟨ownerOf m u, huS⟩
          simp only [ZSet, Finset.mem_filter, Finset.mem_univ, true_and] at hf_u
          have hvA' : offOf m v ∈ f ⟨ownerOf m u, huS⟩ := by
            convert hvA using 1
            · congr 1
              exact Subtype.ext ho
          exact hf_u.1 (offOf m u) huA (offOf m v) hvA' hab
        · set pu : Fin m × Bool := (ownerOf m u, Nat.beq (offOf m u).val 1)
          set pv : Fin m × Bool := (ownerOf m v, Nat.beq (offOf m v).val 1)
          have hpuP : pu ∈ P := by
            have hf_u := hf ⟨ownerOf m u, huS⟩
            simp only [ZSet, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_iff] at hf_u
            by_cases h0 : (offOf m u).val = 0
            · have hpu_eq : pu = (ownerOf m u, false) := by simp [pu, h0]; rfl
              rw [hpu_eq]
              have ho_eq : offOf m u = off0 m := Fin.ext h0
              rw [ho_eq] at huA
              exact hf_u.2.1.mp huA
            · have h1 : (offOf m u).val = 1 := eq_one_of_lt_two_ne_zero huo h0
              have hpu_eq : pu = (ownerOf m u, true) := by simp [pu, h1]
              rw [hpu_eq]
              have ho_eq : offOf m u = off1 m := Fin.ext h1
              rw [ho_eq] at huA
              exact hf_u.2.2.mp huA
          have hpvP : pv ∈ P := by
            have hf_v := hf ⟨ownerOf m v, hvS⟩
            simp only [ZSet, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_iff] at hf_v
            by_cases h0 : (offOf m v).val = 0
            · have hpv_eq : pv = (ownerOf m v, false) := by simp [pv, h0]; rfl
              rw [hpv_eq]
              have ho_eq : offOf m v = off0 m := Fin.ext h0
              rw [ho_eq] at hvA
              exact hf_v.2.1.mp hvA
            · have h1 : (offOf m v).val = 1 := eq_one_of_lt_two_ne_zero hvo h0
              have hpv_eq : pv = (ownerOf m v, true) := by simp [pv, h1]
              rw [hpv_eq]
              have ho_eq : offOf m v = off1 m := Fin.ext h1
              rw [ho_eq] at hvA
              exact hf_v.2.2.mp hvA
          exact hP.2 pu hpuP pv hg ho hpvP
      · ext p
        simp only [portProj, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hpL, hi, ho⟩
          have hi' : p.1 ∈ S := by simpa [ownerOf_portOf] using hi
          have hf_p := hf ⟨p.1, hi'⟩
          simp only [ZSet, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_iff] at hf_p
          rcases p with ⟨i, b⟩
          cases b
          · have hmem : off0 m ∈ f ⟨i, hi'⟩ := by
              convert ho using 1
              · ext; simp [ownerOf_portOf]
              · exact Fin.ext (by simp [off0, offOf_portOf_val])
            exact hf_p.2.1.mp hmem
          · have hmem : off1 m ∈ f ⟨i, hi'⟩ := by
              convert ho using 1
              · ext; simp [ownerOf_portOf]
              · exact Fin.ext (by simp [off1, offOf_portOf_val])
            exact hf_p.2.2.mp hmem
        · intro hpP
          have hpL : p ∈ live := hP.1 hpP
          have hi : p.1 ∈ S := (Finset.mem_filter.mp hpL).2
          have hf_p := hf ⟨p.1, hi⟩
          simp only [ZSet, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_iff] at hf_p
          refine ⟨hpL, by simpa [ownerOf_portOf] using hi, ?_⟩
          rcases p with ⟨i, b⟩
          cases b
          · have hmem := hf_p.2.1.mpr hpP
            convert hmem using 1
            · ext; simp [ownerOf_portOf]
            · exact Fin.ext (by simp [off0, offOf_portOf_val])
          · have hmem := hf_p.2.2.mpr hpP
            convert hmem using 1
            · ext; simp [ownerOf_portOf]
            · exact Fin.ext (by simp [off1, offOf_portOf_val])
    · intro I hI
      simp only [Finset.mem_filter, totalSet, Finset.mem_univ, true_and] at hI
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, vtx_ownerOf_offOf]
      exact ⟨fun ⟨_, hv⟩ => hv, fun hv => ⟨hI.1.1 v hv, hv⟩⟩
    · intro f _
      funext i
      ext o
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ownerOf_vtx, offOf_vtx]
      exact ⟨fun ⟨_, ho⟩ => ho, fun ho => ⟨i.2, ho⟩⟩
  have htotal_zmod : ((totalSet.card : Nat) : ZMod (MOf m)) =
      ((cOf m ^ S.card * optSet.card : Nat) : ZMod (MOf m)) := by
    have hsum : totalSet.card =
        ∑ P ∈ extSet, ∏ i ∈ S, ZCount m (decide ((i, false) ∈ P)) (decide ((i, true) ∈ P)) := by
      rw [Finset.card_eq_sum_card_fiberwise hproj_mem]
      exact Finset.sum_congr rfl hfiber_card
    rw [hsum]
    push_cast
    have hZ := ZCount_zmod m
    have hsub : transSet ⊆ extSet := by
      intro P hP
      simp only [transSet, extSet, Finset.mem_filter, Finset.mem_univ, true_and] at hP ⊢
      exact ⟨hP.1, fun p hp r hrG _ => hP.2.2 p hp r hrG⟩
    rw [← Finset.sum_subset hsub]
    · have hterm : ∀ P ∈ transSet,
          ∏ i ∈ S, ((ZCount m (decide ((i, false) ∈ P)) (decide ((i, true) ∈ P)) : Nat) : ZMod (MOf m)) =
          (cOf m : ZMod (MOf m)) ^ S.card := by
        intro P hP
        simp only [transSet, Finset.mem_filter, Finset.mem_univ, true_and] at hP
        calc ∏ i ∈ S, ((ZCount m (decide ((i, false) ∈ P)) (decide ((i, true) ∈ P)) : Nat) : ZMod (MOf m))
            = ∏ _i ∈ S, (cOf m : ZMod (MOf m)) := by
              refine Finset.prod_congr rfl ?_
              intro i hi
              by_cases hf : (i, false) ∈ P
              · have hnt : (i, true) ∉ P := (hP.2.1 i hi).mp hf
                simp [hf, hnt, hZ.2.1]
              · have ht : (i, true) ∈ P := by
                  by_contra hnt
                  exact hf ((hP.2.1 i hi).mpr hnt)
                simp [hf, ht, hZ.2.2.1]
          _ = (cOf m : ZMod (MOf m)) ^ S.card := Finset.prod_const _
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, hopt_eq_trans]
      ring
    · intro P hPext hPntrans
      simp only [extSet, Finset.mem_filter, Finset.mem_univ, true_and] at hPext
      have hex : ∃ i ∈ S, ¬ ((i, false) ∈ P ↔ (i, true) ∉ P) := by
        by_contra hall
        push Not at hall
        apply hPntrans
        simp only [transSet, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hPext.1, hall, ?_⟩
        intro p hp r hrG hrP
        by_cases h1 : p.1 = r.1
        · have hi : p.1 ∈ S := (Finset.mem_filter.mp (hPext.1 hp)).2
          have hne : p.2 ≠ r.2 := hG_bip p r hrG
          cases hp2 : p.2
          · have hr2 : r.2 = true := by cases hr2' : r.2 <;> simp_all
            have hp_eq : p = (p.1, false) := Prod.ext rfl hp2
            have hr_eq : r = (p.1, true) := Prod.ext h1.symm hr2
            rw [hp_eq] at hp; rw [hr_eq] at hrP
            exact (hall p.1 hi).mp hp hrP
          · have hr2 : r.2 = false := by cases hr2' : r.2 <;> simp_all
            have hp_eq : p = (p.1, true) := Prod.ext rfl hp2
            have hr_eq : r = (p.1, false) := Prod.ext h1.symm hr2
            rw [hp_eq] at hp; rw [hr_eq] at hrP
            exact (hall p.1 hi).mp hrP hp
        · exact hPext.2 p hp r hrG h1 hrP
      rcases hex with ⟨i, hi, hbad⟩
      refine Finset.prod_eq_zero hi ?_
      by_cases hf : (i, false) ∈ P
      · have ht : (i, true) ∈ P := by
          by_contra hnt
          exact hbad ⟨fun _ => hnt, fun _ => hf⟩
        simp [hf, ht, hZ.1]
      · have hnt : (i, true) ∉ P := by
          intro ht
          exact hbad ⟨fun h => (hf h).elim, fun h => (h ht).elim⟩
        simp [hf, hnt, hZ.2.2.2]
  have hmod : totalSet.card % MOf m = (cOf m ^ S.card * optSet.card) % MOf m :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).mp htotal_zmod
  refine ⟨hopt_le, hmod, ?_⟩
  intro t ht hteq
  have htz : ((cOf m ^ S.card * t : Nat) : ZMod (MOf m)) =
      ((cOf m ^ S.card * optSet.card : Nat) : ZMod (MOf m)) := by
    rw [ZMod.natCast_eq_natCast_iff']
    rw [← hteq, hmod]
  push_cast at htz
  have hunit : IsUnit ((cOf m : ZMod (MOf m)) ^ S.card) := by
    have hcop : Nat.Coprime (cOf m ^ S.card) (MOf m) := (coprime_cOf_MOf m).pow_left S.card
    have := (ZMod.isUnit_iff_coprime (cOf m ^ S.card) (MOf m)).mpr hcop
    simpa using this
  have htz' : (t : ZMod (MOf m)) = (optSet.card : ZMod (MOf m)) := hunit.mul_left_cancel htz
  have hmod' : t % MOf m = optSet.card % MOf m :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).mp htz'
  have hS_le : S.card ≤ m := by
    have := Finset.card_le_univ S
    simpa using this
  have hopt_lt : optSet.card < MOf m := by
    calc optSet.card ≤ 2 ^ S.card := hopt_le
      _ ≤ 2 ^ m := Nat.pow_le_pow_right Nat.zero_lt_two hS_le
      _ < MOf m := two_pow_lt_MOf m
  rw [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hopt_lt] at hmod'
  exact hmod'

def Contig {α : Type} (Bs : List (Finset α)) (v : α) : Prop :=
  ∀ s t u (hs : s < Bs.length) (ht : t < Bs.length) (hu : u < Bs.length),
    s ≤ t → t ≤ u → v ∈ Bs[s] → v ∈ Bs[u] → v ∈ Bs[t]

lemma contig_of_all_mem {α : Type} (Bs : List (Finset α)) (v : α)
    (h : ∀ B ∈ Bs, v ∈ B) : Contig Bs v := by
  intro _ t _ _ ht _ _ _ _ _
  exact h Bs[t] (List.getElem_mem ht)

lemma contig_of_none_mem {α : Type} (Bs : List (Finset α)) (v : α)
    (h : ∀ B ∈ Bs, v ∉ B) : Contig Bs v := by
  intro s _ _ hs _ _ _ _ hvs _
  exact (h Bs[s] (List.getElem_mem hs) hvs).elim

lemma contig_append_left {α : Type} (L1 L2 : List (Finset α)) (v : α)
    (h1 : Contig L1 v) (h2 : ∀ B ∈ L2, v ∉ B) : Contig (L1 ++ L2) v := by
  intro s t u hs ht hu hst htu hvs hvu
  have hu1 : u < L1.length := by
    by_contra hge
    have hge' : L1.length ≤ u := Nat.le_of_not_lt hge
    rw [List.getElem_append_right hge'] at hvu
    exact h2 _ (List.getElem_mem _) hvu
  have hs1 : s < L1.length := by omega
  have ht1 : t < L1.length := by omega
  rw [List.getElem_append_left hs1] at hvs
  rw [List.getElem_append_left hu1] at hvu
  rw [List.getElem_append_left ht1]
  exact h1 s t u hs1 ht1 hu1 hst htu hvs hvu

lemma contig_append_right {α : Type} (L1 L2 : List (Finset α)) (v : α)
    (h1 : ∀ B ∈ L1, v ∉ B) (h2 : Contig L2 v) : Contig (L1 ++ L2) v := by
  intro s t u hs ht hu hst htu hvs hvu
  have hs1 : L1.length ≤ s := by
    by_contra hlt
    have hlt' : s < L1.length := Nat.lt_of_not_ge hlt
    rw [List.getElem_append_left hlt'] at hvs
    exact h1 _ (List.getElem_mem _) hvs
  have ht1 : L1.length ≤ t := by omega
  have hu1 : L1.length ≤ u := by omega
  rw [List.getElem_append_right hs1] at hvs
  rw [List.getElem_append_right hu1] at hvu
  rw [List.getElem_append_right ht1]
  exact h2 (s - L1.length) (t - L1.length) (u - L1.length)
    (by simp at hs; omega) (by simp at ht; omega) (by simp at hu; omega)
    (by omega) (by omega) hvs hvu

lemma contig_flatMap_unique {α β : Type} (xs : List β) (f : β → List (Finset α))
    (v : α) (x0 : β) (hnodup : xs.Nodup)
    (hc : Contig (f x0) v) (hother : ∀ x ∈ xs, x ≠ x0 → ∀ B ∈ f x, v ∉ B) :
    Contig (xs.flatMap f) v := by
  induction xs with
  | nil =>
    exact contig_of_none_mem [] v (fun _ h => by simp at h)
  | cons x rest ih =>
    rw [List.nodup_cons] at hnodup
    rw [List.flatMap_cons]
    by_cases hx : x = x0
    · subst hx
      refine contig_append_left (f x) (rest.flatMap f) v hc ?_
      intro B hB
      rcases List.mem_flatMap.mp hB with ⟨y, hy, hBy⟩
      have hne : y ≠ x := fun heq => hnodup.1 (heq ▸ hy)
      exact hother y (List.mem_cons_of_mem x hy) hne B hBy
    · refine contig_append_right (f x) (rest.flatMap f) v
        (hother x (List.mem_cons_self ..) hx)
        (ih hnodup.2 (fun y hy => hother y (List.mem_cons_of_mem x hy)))

lemma contig_map_union_left {α : Type} [DecidableEq α] (L : List (Finset α)) (A : Finset α) (v : α)
    (hvA : v ∉ A) (hL : Contig L v) : Contig (L.map (fun B => A ∪ B)) v := by
  intro s t u hs ht hu hst htu hvs hvu
  simp only [List.length_map] at hs ht hu
  simp only [List.getElem_map, Finset.mem_union, hvA, false_or] at hvs hvu ⊢
  exact hL s t u hs ht hu hst htu hvs hvu

lemma contig_eraseIdx {α : Type} (Bs : List (Finset α)) (r : Nat) (v : α)
    (h : Contig Bs v) : Contig (Bs.eraseIdx r) v := by
  intro s t u hs ht hu hst htu hvs hvu
  by_cases hr : r < Bs.length
  · have hlen : (Bs.eraseIdx r).length = Bs.length - 1 := List.length_eraseIdx_of_lt hr
    let φ : Nat → Nat := fun i => if i < r then i else i + 1
    have hget : ∀ i (hi : i < (Bs.eraseIdx r).length),
        (Bs.eraseIdx r)[i] = Bs[φ i]'(by dsimp [φ]; split_ifs <;> omega) := by
      intro i hi
      dsimp [φ]
      split_ifs with hir
      · exact List.getElem_eraseIdx_of_lt hi hir
      · exact List.getElem_eraseIdx_of_ge hi (Nat.le_of_not_lt hir)
    rw [hget s hs] at hvs
    rw [hget u hu] at hvu
    rw [hget t ht]
    refine h (φ s) (φ t) (φ u) (by dsimp [φ]; split_ifs <;> omega)
      (by dsimp [φ]; split_ifs <;> omega) (by dsimp [φ]; split_ifs <;> omega)
      ?_ ?_ hvs hvu
    · dsimp [φ]; split_ifs <;> omega
    · dsimp [φ]; split_ifs <;> omega
  · have heq : Bs.eraseIdx r = Bs := List.eraseIdx_of_length_le (Nat.le_of_not_lt hr)
    simp only [heq] at hs ht hu hvs hvu ⊢
    exact h s t u hs ht hu hst htu hvs hvu

def GoodDecomp (N w' : Nat) (H : Fin N → Finset (Fin N)) (Bs : List (Finset (Fin N))) : Prop :=
  Bs ≠ [] ∧
  (∀ B ∈ Bs, B.card ≤ w') ∧
  (∀ v : Fin N, ∃ B ∈ Bs, v ∈ B) ∧
  (∀ u v : Fin N, v ∈ H u → ∃ B ∈ Bs, u ∈ B ∧ v ∈ B) ∧
  (∀ v : Fin N, Contig Bs v)

lemma goodDecomp_eraseIdx_succ {N w' : Nat} {H : Fin N → Finset (Fin N)}
    {Bs : List (Finset (Fin N))} (hg : GoodDecomp N w' H Bs)
    (k : Nat) (hk : k + 1 < Bs.length) (hsub : Bs[k + 1] ⊆ Bs[k]) :
    GoodDecomp N w' H (Bs.eraseIdx (k + 1)) := by
  rcases hg with ⟨_, hcard, hv, he, hcont⟩
  have hlen : (Bs.eraseIdx (k + 1)).length = Bs.length - 1 := List.length_eraseIdx_of_lt hk
  have hk_mem : Bs[k] ∈ Bs.eraseIdx (k + 1) := by
    have hk' : k < (Bs.eraseIdx (k + 1)).length := by omega
    have hget : (Bs.eraseIdx (k + 1))[k]'hk' = Bs[k] :=
      List.getElem_eraseIdx_of_lt hk' (by omega)
    rw [← hget]
    exact List.getElem_mem hk'
  have hkeep : ∀ B ∈ Bs, ∃ B' ∈ Bs.eraseIdx (k + 1), B ⊆ B' := by
    intro B hB
    rcases List.getElem_of_mem hB with ⟨j, hj, rfl⟩
    by_cases hjk : j = k + 1
    · subst hjk
      exact ⟨Bs[k], hk_mem, hsub⟩
    · by_cases hlt : j < k + 1
      · refine ⟨Bs[j], ?_, Finset.Subset.refl _⟩
        have hj' : j < (Bs.eraseIdx (k + 1)).length := by omega
        have hget : (Bs.eraseIdx (k + 1))[j]'hj' = Bs[j] :=
          List.getElem_eraseIdx_of_lt hj' hlt
        rw [← hget]
        exact List.getElem_mem hj'
      · refine ⟨Bs[j], ?_, Finset.Subset.refl _⟩
        have hj' : j - 1 < (Bs.eraseIdx (k + 1)).length := by omega
        have hget : (Bs.eraseIdx (k + 1))[j - 1]'hj' = Bs[j] := by
          have h1 := List.getElem_eraseIdx_of_ge hj' (by omega)
          have h2 : j - 1 + 1 = j := by omega
          simpa [h2] using h1
        rw [← hget]
        exact List.getElem_mem hj'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hnil
    have : (Bs.eraseIdx (k + 1)).length = 0 := by simp [hnil]
    omega
  · intro B hB
    exact hcard B (List.mem_of_mem_eraseIdx hB)
  · intro v
    rcases hv v with ⟨B, hB, hvB⟩
    rcases hkeep B hB with ⟨B', hB', hBB'⟩
    exact ⟨B', hB', hBB' hvB⟩
  · intro u v huv
    rcases he u v huv with ⟨B, hB, huB, hvB⟩
    rcases hkeep B hB with ⟨B', hB', hBB'⟩
    exact ⟨B', hB', hBB' huB, hBB' hvB⟩
  · intro v
    exact contig_eraseIdx Bs (k + 1) v (hcont v)

lemma compress_goodDecomp {N w' : Nat} {H : Fin N → Finset (Fin N)} :
    ∀ n : Nat, ∀ Bs : List (Finset (Fin N)), Bs.length = n → GoodDecomp N w' H Bs →
      ∃ Bs' : List (Finset (Fin N)), Bs'.length ≤ N + 1 ∧ GoodDecomp N w' H Bs' := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro Bs hlen hg
    classical
    by_cases hred : ∃ k : Nat, ∃ hk : k + 1 < Bs.length, Bs[k + 1] ⊆ Bs[k]
    · rcases hred with ⟨k, hk, hsub⟩
      have hlen' : (Bs.eraseIdx (k + 1)).length = n - 1 := by
        rw [List.length_eraseIdx_of_lt hk, hlen]
      have hlt : n - 1 < n := by omega
      exact ih (n - 1) hlt (Bs.eraseIdx (k + 1)) hlen'
        (goodDecomp_eraseIdx_succ hg k hk hsub)
    · refine ⟨Bs, ?_, hg⟩
      have hne : 0 < Bs.length := List.length_pos_of_ne_nil hg.1
      have hnotSub : ∀ k : Fin (Bs.length - 1), ∃ v : Fin N,
          v ∈ Bs[k.val + 1]'(by omega) ∧ v ∉ Bs[k.val]'(by omega) := by
        intro k
        have hns : ¬ (Bs[k.val + 1]'(by omega) ⊆ Bs[k.val]'(by omega)) :=
          fun hsub => hred ⟨k.val, by omega, hsub⟩
        rw [Finset.not_subset] at hns
        exact hns
      let f : Fin (Bs.length - 1) → Fin N := fun k => Classical.choose (hnotSub k)
      have hf : ∀ k : Fin (Bs.length - 1),
          f k ∈ Bs[k.val + 1]'(by omega) ∧ f k ∉ Bs[k.val]'(by omega) :=
        fun k => Classical.choose_spec (hnotSub k)
      have hinj : Function.Injective f := by
        intro j k hjk
        by_contra hne_jk
        have hlt_or : j.val < k.val ∨ k.val < j.val := by
          have : j.val ≠ k.val := fun h => hne_jk (Fin.ext h)
          omega
        rcases hlt_or with hlt | hlt
        · have hj1 := (hf j).1
          rw [hjk] at hj1
          have hk1 := (hf k).1
          have hmem := hg.2.2.2.2 (f k) (j.val + 1) k.val (k.val + 1)
            (by omega) (by omega) (by omega) (by omega) (by omega) hj1 hk1
          exact (hf k).2 hmem
        · have hk1 := (hf k).1
          rw [← hjk] at hk1
          have hj1 := (hf j).1
          have hmem := hg.2.2.2.2 (f j) (k.val + 1) j.val (j.val + 1)
            (by omega) (by omega) (by omega) (by omega) (by omega) hk1 hj1
          exact (hf j).2 hmem
      have hcard := Fintype.card_le_of_injective f hinj
      simp only [Fintype.card_fin] at hcard
      omega

def spineSet (m : Nat) (i : Fin m) : Finset (Fin (m * BOf m)) :=
  {vtx m i ⟨2, by have := BOf_ge_eight m; omega⟩,
   vtx m i ⟨3, by have := BOf_ge_eight m; omega⟩,
   vtx m i ⟨4, by have := BOf_ge_eight m; omega⟩,
   vtx m i ⟨5, by have := BOf_ge_eight m; omega⟩}

lemma spineSet_card_le (m : Nat) (i : Fin m) : (spineSet m i).card ≤ 4 := by
  unfold spineSet
  have c1 := Finset.card_insert_le (vtx m i ⟨2, by have := BOf_ge_eight m; omega⟩)
    ({vtx m i ⟨3, by have := BOf_ge_eight m; omega⟩,
      vtx m i ⟨4, by have := BOf_ge_eight m; omega⟩,
      vtx m i ⟨5, by have := BOf_ge_eight m; omega⟩} : Finset (Fin (m * BOf m)))
  have c2 := Finset.card_insert_le (vtx m i ⟨3, by have := BOf_ge_eight m; omega⟩)
    ({vtx m i ⟨4, by have := BOf_ge_eight m; omega⟩,
      vtx m i ⟨5, by have := BOf_ge_eight m; omega⟩} : Finset (Fin (m * BOf m)))
  have c3 := Finset.card_insert_le (vtx m i ⟨4, by have := BOf_ge_eight m; omega⟩)
    ({vtx m i ⟨5, by have := BOf_ge_eight m; omega⟩} : Finset (Fin (m * BOf m)))
  simp at c1 c2 c3
  omega

def tailBag (m : Nat) (i : Fin m) (start len : Nat) (hlen : start + len ≤ BOf m)
    (k : Fin len) : Finset (Fin (m * BOf m)) :=
  if k.val = 0 then
    spineSet m i ∪ {vtx m i ⟨start, by have := k.isLt; omega⟩}
  else
    spineSet m i ∪ {vtx m i ⟨start + k.val - 1, by have := k.isLt; omega⟩,
      vtx m i ⟨start + k.val, by have := k.isLt; omega⟩}

def tailBags (m : Nat) (i : Fin m) (start len : Nat) (hlen : start + len ≤ BOf m) :
    List (Finset (Fin (m * BOf m))) :=
  (List.finRange len).map (tailBag m i start len hlen)

lemma tailBag_card_le (m : Nat) (i : Fin m) (start len : Nat) (hlen : start + len ≤ BOf m)
    (k : Fin len) : (tailBag m i start len hlen k).card ≤ 6 := by
  have hs := spineSet_card_le m i
  unfold tailBag
  split_ifs
  · refine le_trans (Finset.card_union_le _ _) ?_
    simp only [Finset.card_singleton]
    omega
  · refine le_trans (Finset.card_union_le _ _) ?_
    have h2 := Finset.card_insert_le
      (vtx m i ⟨start + k.val - 1, by have := k.isLt; omega⟩)
      ({vtx m i ⟨start + k.val, by have := k.isLt; omega⟩} : Finset (Fin (m * BOf m)))
    simp only [Finset.card_singleton] at h2
    omega

lemma tailBags_contig (m : Nat) (i : Fin m) (start len : Nat) (hlen : start + len ≤ BOf m)
    (hstart : 6 ≤ start) (v : Fin (m * BOf m)) :
    Contig (tailBags m i start len hlen) v := by
  by_cases hvsp : v ∈ spineSet m i
  · refine contig_of_all_mem _ _ ?_
    intro B hB
    rcases List.mem_map.mp hB with ⟨k, _, rfl⟩
    unfold tailBag
    split_ifs <;> exact Finset.mem_union_left _ hvsp
  · intro s t u hs ht hu hst htu hvs hvu
    unfold tailBags at hs ht hu hvs hvu ⊢
    simp only [List.length_map, List.length_finRange] at hs ht hu
    simp only [List.getElem_map, List.getElem_finRange] at hvs hvu ⊢
    have hmem_range : ∀ k (hk : k < len),
        v ∈ tailBag m i start len hlen ⟨k, hk⟩ →
        ownerOf m v = i ∧
        ((offOf m v).val = start + k ∨ (0 < k ∧ (offOf m v).val = start + k - 1)) := by
      intro k hk hvk
      unfold tailBag at hvk
      split_ifs at hvk with hk0
      · dsimp only [] at hk0
        rw [Finset.mem_union] at hvk
        rcases hvk with h | h
        · exact (hvsp h).elim
        · rw [Finset.mem_singleton] at h
          subst h
          exact ⟨ownerOf_vtx _ _ _, Or.inl (by simp [offOf_vtx, hk0])⟩
      · dsimp only [] at hk0
        rw [Finset.mem_union] at hvk
        rcases hvk with h | h
        · exact (hvsp h).elim
        · rw [Finset.mem_insert, Finset.mem_singleton] at h
          rcases h with rfl | rfl
          · exact ⟨ownerOf_vtx _ _ _, Or.inr ⟨by omega, by simp [offOf_vtx]⟩⟩
          · exact ⟨ownerOf_vtx _ _ _, Or.inl (by simp [offOf_vtx])⟩
    rcases hmem_range s hs hvs with ⟨_, hs_eq⟩
    rcases hmem_range u hu hvu with ⟨_, hu_eq⟩
    have hcase : t = s ∨ t = u := by omega
    rcases hcase with rfl | rfl
    · exact hvs
    · exact hvu

def localBags (m : Nat) (i : Fin m) : List (Finset (Fin (m * BOf m))) :=
  have hd : 2 ≤ dOf m := dOf_ge_two m
  have hs0 : s0Of m = 6 := rfl
  have hs3 : s3Of m = 2 * dOf m + 3 := rfl
  have hs1 : s1Of m = 4 * dOf m := rfl
  have hs2 : s2Of m = 5 * dOf m - 2 := rfl
  have hB : BOf m = 6 * dOf m - 4 := rfl
  have hL0 : L0Of m = 2 * dOf m - 3 := rfl
  have hL1 : L1Of m = dOf m - 2 := rfl
  [spineSet m i] ++
  tailBags m i (s0Of m) (L0Of m) (by omega) ++
  tailBags m i (s3Of m) (L0Of m) (by omega) ++
  tailBags m i (s1Of m) (L1Of m) (by omega) ++
  tailBags m i (s2Of m) (L1Of m) (by omega)

lemma localBags_card_le (m : Nat) (i : Fin m) :
    ∀ B ∈ localBags m i, B.card ≤ 6 := by
  intro B hB
  unfold localBags at hB
  simp only [List.mem_append, List.mem_singleton] at hB
  rcases hB with (((rfl | h0) | h3) | h1) | h2
  · have := spineSet_card_le m i; omega
  · rcases List.mem_map.mp h0 with ⟨k, _, rfl⟩; exact tailBag_card_le _ _ _ _ _ k
  · rcases List.mem_map.mp h3 with ⟨k, _, rfl⟩; exact tailBag_card_le _ _ _ _ _ k
  · rcases List.mem_map.mp h1 with ⟨k, _, rfl⟩; exact tailBag_card_le _ _ _ _ _ k
  · rcases List.mem_map.mp h2 with ⟨k, _, rfl⟩; exact tailBag_card_le _ _ _ _ _ k

lemma localBags_mem_bounds (m : Nat) (i : Fin m) (B : Finset (Fin (m * BOf m)))
    (hB : B ∈ localBags m i) (v : Fin (m * BOf m)) (hv : v ∈ B) :
    ownerOf m v = i ∧ 2 ≤ (offOf m v).val := by
  have hd : 2 ≤ dOf m := dOf_ge_two m
  have hs0 : s0Of m = 6 := rfl
  have hs3 : s3Of m = 2 * dOf m + 3 := rfl
  have hs1 : s1Of m = 4 * dOf m := rfl
  have hs2 : s2Of m = 5 * dOf m - 2 := rfl
  have hB' : BOf m = 6 * dOf m - 4 := rfl
  have hL0 : L0Of m = 2 * dOf m - 3 := rfl
  have hL1 : L1Of m = dOf m - 2 := rfl
  have hsp : ∀ w ∈ spineSet m i, ownerOf m w = i ∧ 2 ≤ (offOf m w).val := by
    intro w hw
    unfold spineSet at hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> simp [ownerOf_vtx, offOf_vtx]
  have htail : ∀ start len hlen, 6 ≤ start →
      ∀ B' ∈ tailBags m i start len hlen, v ∈ B' →
      ownerOf m v = i ∧ 2 ≤ (offOf m v).val := by
    intro start len hlen hst B' hB' hv'
    rcases List.mem_map.mp hB' with ⟨k, _, rfl⟩
    unfold tailBag at hv'
    split_ifs at hv' with hk0
    · rcases Finset.mem_union.mp hv' with h | h
      · exact hsp v h
      · rw [Finset.mem_singleton] at h; subst h; simp [ownerOf_vtx, offOf_vtx]; omega
    · rcases Finset.mem_union.mp hv' with h | h
      · exact hsp v h
      · rw [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl <;> simp [ownerOf_vtx, offOf_vtx] <;> omega
  unfold localBags at hB
  simp only [List.mem_append, List.mem_singleton] at hB
  rcases hB with (((rfl | h0) | h3) | h1) | h2
  · exact hsp v hv
  · exact htail _ _ _ (by omega) B h0 hv
  · exact htail _ _ _ (by omega) B h3 hv
  · exact htail _ _ _ (by omega) B h1 hv
  · exact htail _ _ _ (by omega) B h2 hv

lemma tailBags_not_mem_outside (m : Nat) (i : Fin m) (start len : Nat) (hlen : start + len ≤ BOf m)
    (hstart : 6 ≤ start) (v : Fin (m * BOf m)) (hvsp : v ∉ spineSet m i)
    (hout : ownerOf m v ≠ i ∨ (offOf m v).val < start ∨ start + len ≤ (offOf m v).val) :
    ∀ B ∈ tailBags m i start len hlen, v ∉ B := by
  intro B hB hvB
  rcases List.mem_map.mp hB with ⟨k, _, rfl⟩
  unfold tailBag at hvB
  split_ifs at hvB with hk0
  · rcases Finset.mem_union.mp hvB with h | h
    · exact hvsp h
    · rw [Finset.mem_singleton] at h; subst h
      simp only [ownerOf_vtx, offOf_vtx, ne_eq, not_true_eq_false, false_or] at hout
      omega
  · rcases Finset.mem_union.mp hvB with h | h
    · exact hvsp h
    · rw [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl
      · simp only [ownerOf_vtx, offOf_vtx, ne_eq, not_true_eq_false, false_or] at hout
        omega
      · simp only [ownerOf_vtx, offOf_vtx, ne_eq, not_true_eq_false, false_or] at hout
        omega

lemma localBags_contig (m : Nat) (i : Fin m) (v : Fin (m * BOf m)) :
    Contig (localBags m i) v := by
  have hd : 2 ≤ dOf m := dOf_ge_two m
  have hs0 : s0Of m = 6 := rfl
  have hs3 : s3Of m = 2 * dOf m + 3 := rfl
  have hs1 : s1Of m = 4 * dOf m := rfl
  have hs2 : s2Of m = 5 * dOf m - 2 := rfl
  have hB' : BOf m = 6 * dOf m - 4 := rfl
  have hL0 : L0Of m = 2 * dOf m - 3 := rfl
  have hL1 : L1Of m = dOf m - 2 := rfl
  by_cases hvsp : v ∈ spineSet m i
  · refine contig_of_all_mem _ _ ?_
    intro B hB
    unfold localBags at hB
    simp only [List.mem_append, List.mem_singleton] at hB
    rcases hB with (((rfl | h0) | h3) | h1) | h2
    · exact hvsp
    · rcases List.mem_map.mp h0 with ⟨k, _, rfl⟩; unfold tailBag; split_ifs <;> exact Finset.mem_union_left _ hvsp
    · rcases List.mem_map.mp h3 with ⟨k, _, rfl⟩; unfold tailBag; split_ifs <;> exact Finset.mem_union_left _ hvsp
    · rcases List.mem_map.mp h1 with ⟨k, _, rfl⟩; unfold tailBag; split_ifs <;> exact Finset.mem_union_left _ hvsp
    · rcases List.mem_map.mp h2 with ⟨k, _, rfl⟩; unfold tailBag; split_ifs <;> exact Finset.mem_union_left _ hvsp
  · have hb0 : s0Of m + L0Of m ≤ BOf m := by omega
    have hb3 : s3Of m + L0Of m ≤ BOf m := by omega
    have hb1 : s1Of m + L1Of m ≤ BOf m := by omega
    have hb2 : s2Of m + L1Of m ≤ BOf m := by omega
    have hs0_6 : 6 ≤ s0Of m := by omega
    have hs3_6 : 6 ≤ s3Of m := by omega
    have hs1_6 : 6 ≤ s1Of m := by omega
    have hs2_6 : 6 ≤ s2Of m := by omega
    unfold localBags
    set T0 := tailBags m i (s0Of m) (L0Of m) hb0
    set T3 := tailBags m i (s3Of m) (L0Of m) hb3
    set T1 := tailBags m i (s1Of m) (L1Of m) hb1
    set T2 := tailBags m i (s2Of m) (L1Of m) hb2
    have hn_sp : ∀ B ∈ [spineSet m i], v ∉ B := by
      intro B hB; simp only [List.mem_singleton] at hB; subst hB; exact hvsp
    by_cases h0 : ownerOf m v = i ∧ s0Of m ≤ (offOf m v).val ∧ (offOf m v).val < s3Of m
    · have hn3 : ∀ B ∈ T3, v ∉ B := tailBags_not_mem_outside m i (s3Of m) (L0Of m) hb3 hs3_6 v hvsp (Or.inr (Or.inl (by omega)))
      have hn1 : ∀ B ∈ T1, v ∉ B := tailBags_not_mem_outside m i (s1Of m) (L1Of m) hb1 hs1_6 v hvsp (Or.inr (Or.inl (by omega)))
      have hn2 : ∀ B ∈ T2, v ∉ B := tailBags_not_mem_outside m i (s2Of m) (L1Of m) hb2 hs2_6 v hvsp (Or.inr (Or.inl (by omega)))
      have hc0 := tailBags_contig m i (s0Of m) (L0Of m) hb0 hs0_6 v
      exact contig_append_left _ _ v
        (contig_append_left _ _ v
          (contig_append_left _ _ v
            (contig_append_right _ _ v hn_sp hc0) hn3) hn1) hn2
    by_cases h3 : ownerOf m v = i ∧ s3Of m ≤ (offOf m v).val ∧ (offOf m v).val < s1Of m
    · have hn0 : ∀ B ∈ T0, v ∉ B := tailBags_not_mem_outside m i (s0Of m) (L0Of m) hb0 hs0_6 v hvsp (Or.inr (Or.inr (by omega)))
      have hn1 : ∀ B ∈ T1, v ∉ B := tailBags_not_mem_outside m i (s1Of m) (L1Of m) hb1 hs1_6 v hvsp (Or.inr (Or.inl (by omega)))
      have hn2 : ∀ B ∈ T2, v ∉ B := tailBags_not_mem_outside m i (s2Of m) (L1Of m) hb2 hs2_6 v hvsp (Or.inr (Or.inl (by omega)))
      have hc3 := tailBags_contig m i (s3Of m) (L0Of m) hb3 hs3_6 v
      have hn_left : ∀ B ∈ [spineSet m i] ++ T0, v ∉ B := by
        intro B hB; rcases List.mem_append.mp hB with h | h
        · exact hn_sp B h
        · exact hn0 B h
      exact contig_append_left _ _ v
        (contig_append_left _ _ v
          (contig_append_right _ _ v hn_left hc3) hn1) hn2
    by_cases h1 : ownerOf m v = i ∧ s1Of m ≤ (offOf m v).val ∧ (offOf m v).val < s2Of m
    · have hn0 : ∀ B ∈ T0, v ∉ B := tailBags_not_mem_outside m i (s0Of m) (L0Of m) hb0 hs0_6 v hvsp (Or.inr (Or.inr (by omega)))
      have hn3 : ∀ B ∈ T3, v ∉ B := tailBags_not_mem_outside m i (s3Of m) (L0Of m) hb3 hs3_6 v hvsp (Or.inr (Or.inr (by omega)))
      have hn2 : ∀ B ∈ T2, v ∉ B := tailBags_not_mem_outside m i (s2Of m) (L1Of m) hb2 hs2_6 v hvsp (Or.inr (Or.inl (by omega)))
      have hc1 := tailBags_contig m i (s1Of m) (L1Of m) hb1 hs1_6 v
      have hn_left : ∀ B ∈ [spineSet m i] ++ T0 ++ T3, v ∉ B := by
        intro B hB
        simp only [List.mem_append] at hB
        rcases hB with (h | h) | h
        · exact hn_sp B h
        · exact hn0 B h
        · exact hn3 B h
      exact contig_append_left _ _ v (contig_append_right _ _ v hn_left hc1) hn2
    by_cases h2 : ownerOf m v = i ∧ s2Of m ≤ (offOf m v).val ∧ (offOf m v).val < BOf m
    · have hn0 : ∀ B ∈ T0, v ∉ B := tailBags_not_mem_outside m i (s0Of m) (L0Of m) hb0 hs0_6 v hvsp (Or.inr (Or.inr (by omega)))
      have hn3 : ∀ B ∈ T3, v ∉ B := tailBags_not_mem_outside m i (s3Of m) (L0Of m) hb3 hs3_6 v hvsp (Or.inr (Or.inr (by omega)))
      have hn1 : ∀ B ∈ T1, v ∉ B := tailBags_not_mem_outside m i (s1Of m) (L1Of m) hb1 hs1_6 v hvsp (Or.inr (Or.inr (by omega)))
      have hc2 := tailBags_contig m i (s2Of m) (L1Of m) hb2 hs2_6 v
      have hn_left : ∀ B ∈ [spineSet m i] ++ T0 ++ T3 ++ T1, v ∉ B := by
        intro B hB
        simp only [List.mem_append] at hB
        rcases hB with ((h | h) | h) | h
        · exact hn_sp B h
        · exact hn0 B h
        · exact hn3 B h
        · exact hn1 B h
      exact contig_append_right _ _ v hn_left hc2
    · refine contig_of_none_mem _ _ ?_
      have hout0 : ownerOf m v ≠ i ∨ (offOf m v).val < s0Of m ∨ s0Of m + L0Of m ≤ (offOf m v).val := by
        by_cases ho : ownerOf m v = i; · right; omega
        · left; exact ho
      have hout3 : ownerOf m v ≠ i ∨ (offOf m v).val < s3Of m ∨ s3Of m + L0Of m ≤ (offOf m v).val := by
        by_cases ho : ownerOf m v = i; · right; omega
        · left; exact ho
      have hout1 : ownerOf m v ≠ i ∨ (offOf m v).val < s1Of m ∨ s1Of m + L1Of m ≤ (offOf m v).val := by
        by_cases ho : ownerOf m v = i; · right; omega
        · left; exact ho
      have hout2 : ownerOf m v ≠ i ∨ (offOf m v).val < s2Of m ∨ s2Of m + L1Of m ≤ (offOf m v).val := by
        by_cases ho : ownerOf m v = i; · right; have := (offOf m v).isLt; omega
        · left; exact ho
      have hn0 : ∀ B ∈ T0, v ∉ B := tailBags_not_mem_outside m i (s0Of m) (L0Of m) hb0 hs0_6 v hvsp hout0
      have hn3 : ∀ B ∈ T3, v ∉ B := tailBags_not_mem_outside m i (s3Of m) (L0Of m) hb3 hs3_6 v hvsp hout3
      have hn1 : ∀ B ∈ T1, v ∉ B := tailBags_not_mem_outside m i (s1Of m) (L1Of m) hb1 hs1_6 v hvsp hout1
      have hn2 : ∀ B ∈ T2, v ∉ B := tailBags_not_mem_outside m i (s2Of m) (L1Of m) hb2 hs2_6 v hvsp hout2
      intro B hB
      simp only [List.mem_append] at hB
      rcases hB with (((h | h) | h) | h) | h
      · exact hn_sp B h
      · exact hn0 B h
      · exact hn3 B h
      · exact hn1 B h
      · exact hn2 B h

lemma step5_path_decomp (m w : Nat) (G : (Fin m × Bool) → Finset (Fin m × Bool))
    (hG_mark : ∀ i, (i, true) ∈ G (i, false))
    (hpd : ∃ (l : Nat) (bag : Fin l → Finset (Fin m × Bool)),
      (∀ t, (bag t).card ≤ w) ∧ (∀ p, ∃ t, p ∈ bag t) ∧
      (∀ p r, r ∈ G p → ∃ t, p ∈ bag t ∧ r ∈ bag t) ∧
      ∀ p s t u, s ≤ t → t ≤ u → p ∈ bag s → p ∈ bag u → p ∈ bag t) :
    ∃ (l : Nat) (bag : Fin l → Finset (Fin (m * BOf m))),
      l ≤ 2 * (m * BOf m) + 1 ∧ (∀ t, (bag t).card ≤ w + 6) ∧
      (∀ v, ∃ t, v ∈ bag t) ∧
      (∀ u v, v ∈ HOf m G u → ∃ t, u ∈ bag t ∧ v ∈ bag t) ∧
      ∀ v s t u, s ≤ t → t ≤ u → v ∈ bag s → v ∈ bag u → v ∈ bag t := by
  classical
  by_cases hm : m = 0
  · subst hm
    refine ⟨1, fun _ => ∅, by simp, fun _ => by simp, fun v => Fin.elim0 v,
      fun u => Fin.elim0 u, fun v => Fin.elim0 v⟩
  · rcases hpd with ⟨l0, bag0, hcard0, hv0, he0, hcont0⟩
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hl0 : 0 < l0 := by
      rcases hv0 (⟨0, hmpos⟩, false) with ⟨t, _⟩
      exact Nat.zero_lt_of_lt t.isLt
    have hanc_ex : ∀ i : Fin m, ∃ t : Fin l0, (i, false) ∈ bag0 t ∧ (i, true) ∈ bag0 t :=
      fun i => he0 (i, false) (i, true) (hG_mark i)
    let anchor : Fin m → Fin l0 := fun i => Classical.choose (hanc_ex i)
    have hanchor : ∀ i : Fin m, (i, false) ∈ bag0 (anchor i) ∧ (i, true) ∈ bag0 (anchor i) :=
      fun i => Classical.choose_spec (hanc_ex i)
    let liftBag : Fin l0 → Finset (Fin (m * BOf m)) := fun t => (bag0 t).image (portOf m)
    let blockSection : Fin l0 → List (Finset (Fin (m * BOf m))) := fun t =>
      [liftBag t] ++
      ((List.finRange m).filter (fun i => anchor i = t)).flatMap (fun i =>
        (localBags m i).map (fun B => liftBag t ∪ B))
    let rawBags : List (Finset (Fin (m * BOf m))) :=
      (List.finRange l0).flatMap blockSection
    have hlift_card : ∀ t, (liftBag t).card ≤ w := fun t =>
      le_trans Finset.card_image_le (hcard0 t)
    have hlift_port : ∀ t p, portOf m p ∈ liftBag t ↔ p ∈ bag0 t := by
      intro t p
      simp only [liftBag, Finset.mem_image]
      exact ⟨fun ⟨q, hq, heq⟩ => by rwa [portOf_injective m heq] at hq, fun hp => ⟨p, hp, rfl⟩⟩
    have hlift_no_int : ∀ t v, 2 ≤ (offOf m v).val → v ∉ liftBag t := by
      intro t v hge hv
      rcases Finset.mem_image.mp hv with ⟨p, _, rfl⟩
      rw [offOf_portOf_val] at hge
      cases hp2 : p.2 <;> simp [hp2] at hge
    have hd : 2 ≤ dOf m := dOf_ge_two m
    have hs0 : s0Of m = 6 := rfl
    have hs3 : s3Of m = 2 * dOf m + 3 := rfl
    have hs1 : s1Of m = 4 * dOf m := rfl
    have hs2 : s2Of m = 5 * dOf m - 2 := rfl
    have hB' : BOf m = 6 * dOf m - 4 := rfl
    have hL0 : L0Of m = 2 * dOf m - 3 := rfl
    have hL1 : L1Of m = dOf m - 2 := rfl
    have hlocal_in_raw : ∀ i : Fin m, ∀ B ∈ localBags m i, liftBag (anchor i) ∪ B ∈ rawBags := by
      intro i B hB
      refine List.mem_flatMap.mpr ⟨anchor i, List.mem_finRange _, ?_⟩
      refine List.mem_append_right _ ?_
      refine List.mem_flatMap.mpr ⟨i, ?_, List.mem_map.mpr ⟨B, hB, rfl⟩⟩
      simp [List.mem_filter, List.mem_finRange]
    have hlift_in_raw : ∀ t : Fin l0, liftBag t ∈ rawBags := by
      intro t
      refine List.mem_flatMap.mpr ⟨t, List.mem_finRange _, List.mem_append_left _ (List.mem_singleton_self _)⟩
    have hgood : GoodDecomp (m * BOf m) (w + 6) (HOf m G) rawBags := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro hnil
        have hmem := hlift_in_raw ⟨0, hl0⟩
        rw [hnil] at hmem
        simp at hmem
      · intro B hB
        rcases List.mem_flatMap.mp hB with ⟨t, _, hBt⟩
        rcases List.mem_append.mp hBt with h1 | h2
        · simp only [List.mem_singleton] at h1
          subst h1
          have := hlift_card t; omega
        · rcases List.mem_flatMap.mp h2 with ⟨i, _, hBi⟩
          rcases List.mem_map.mp hBi with ⟨B', hB', rfl⟩
          have c1 := Finset.card_union_le (liftBag t) B'
          have c2 := hlift_card t
          have c3 := localBags_card_le m i B' hB'
          omega
      · intro v
        by_cases hport : (offOf m v).val < 2
        · set p : Fin m × Bool := (ownerOf m v, Nat.beq (offOf m v).val 1)
          have hvp : v = portOf m p := eq_portOf_of_off_lt_two m v hport
          rcases hv0 p with ⟨t, hpt⟩
          refine ⟨liftBag t, hlift_in_raw t, ?_⟩
          rw [hvp, hlift_port]
          exact hpt
        · set i := ownerOf m v
          set x := (offOf m v).val
          have hv_eq : v = vtx m i (offOf m v) := (vtx_ownerOf_offOf m v).symm
          by_cases hxsp : x < 6
          · refine ⟨liftBag (anchor i) ∪ spineSet m i,
              hlocal_in_raw i (spineSet m i) (by unfold localBags; simp),
              Finset.mem_union_right _ ?_⟩
            rw [hv_eq]
            unfold spineSet
            have hcases : offOf m v = ⟨2, by omega⟩ ∨ offOf m v = ⟨3, by omega⟩ ∨
                offOf m v = ⟨4, by omega⟩ ∨ offOf m v = ⟨5, by omega⟩ := by
              have : x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by omega
              rcases this with h | h | h | h
              · exact Or.inl (Fin.ext h)
              · exact Or.inr (Or.inl (Fin.ext h))
              · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
              · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))
            rcases hcases with h | h | h | h <;> rw [h] <;> simp
          · have htail_cov : ∀ start len hlen, start ≤ x → x < start + len →
                ∃ B ∈ tailBags m i start len hlen, v ∈ B := by
              intro start len hlen hlo hhi
              let k : Fin len := ⟨x - start, by omega⟩
              refine ⟨tailBag m i start len hlen k,
                List.mem_map.mpr ⟨k, List.mem_finRange _, rfl⟩, ?_⟩
              unfold tailBag
              split_ifs with hk0
              · refine Finset.mem_union_right _ (Finset.mem_singleton.mpr ?_)
                rw [hv_eq]; congr 1; exact Fin.ext (by dsimp only [k, x] at hk0 ⊢; omega)
              · refine Finset.mem_union_right _ (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr ?_)))
                rw [hv_eq]; congr 1; exact Fin.ext (by dsimp only [k, x]; omega)
            by_cases hx3 : x < s3Of m
            · rcases htail_cov (s0Of m) (L0Of m) (by omega) (by omega) (by omega) with ⟨B, hB, hvB⟩
              exact ⟨liftBag (anchor i) ∪ B, hlocal_in_raw i B (by unfold localBags; simp [hB]),
                Finset.mem_union_right _ hvB⟩
            by_cases hx1 : x < s1Of m
            · rcases htail_cov (s3Of m) (L0Of m) (by omega) (by omega) (by omega) with ⟨B, hB, hvB⟩
              exact ⟨liftBag (anchor i) ∪ B, hlocal_in_raw i B (by unfold localBags; simp [hB]),
                Finset.mem_union_right _ hvB⟩
            by_cases hx2 : x < s2Of m
            · rcases htail_cov (s1Of m) (L1Of m) (by omega) (by omega) (by omega) with ⟨B, hB, hvB⟩
              exact ⟨liftBag (anchor i) ∪ B, hlocal_in_raw i B (by unfold localBags; simp [hB]),
                Finset.mem_union_right _ hvB⟩
            · have hxB : x < BOf m := (offOf m v).isLt
              rcases htail_cov (s2Of m) (L1Of m) (by omega) (by omega) (by omega) with ⟨B, hB, hvB⟩
              exact ⟨liftBag (anchor i) ∪ B, hlocal_in_raw i B (by unfold localBags; simp [hB]),
                Finset.mem_union_right _ hvB⟩
      · intro u v hvH
        rw [mem_HOf_iff] at hvH
        rcases hvH with ⟨ho, hab⟩ | ⟨_, huo, hvo, hg⟩
        · have hdir_cov : ∀ a b : Fin (m * BOf m),
              ownerOf m a = ownerOf m b → blockDir m (offOf m a).val (offOf m b).val →
              ∃ B ∈ rawBags, a ∈ B ∧ b ∈ B := by
            intro a b habo hbd
            set i := ownerOf m a
            have ha_eq : a = vtx m i (offOf m a) := (vtx_ownerOf_offOf m a).symm
            have hb_eq : b = vtx m i (offOf m b) := by
              rw [show i = ownerOf m b from habo]; exact (vtx_ownerOf_offOf m b).symm
            have hp0_mem : vtx m i ⟨0, by omega⟩ ∈ liftBag (anchor i) := by
              have := (hlift_port (anchor i) (i, false)).mpr (hanchor i).1
              simpa [portOf] using this
            have hp1_mem : vtx m i ⟨1, by omega⟩ ∈ liftBag (anchor i) := by
              have := (hlift_port (anchor i) (i, true)).mpr (hanchor i).2
              simpa [portOf] using this
            have hsp_in_raw : liftBag (anchor i) ∪ spineSet m i ∈ rawBags :=
              hlocal_in_raw i (spineSet m i) (by unfold localBags; simp)
            unfold blockDir at hbd
            rcases hbd with ⟨ha0, hb2⟩ | ⟨ha2, hb3⟩ | ⟨ha3, hb4⟩ | ⟨ha4, hb5⟩ | ⟨ha1, hb5⟩ |
              ⟨ha2, hbs0⟩ | ⟨h1, h2, hxy⟩ | ⟨ha5, hbs3⟩ | ⟨h1, h2, hxy⟩ |
              ⟨hl, ha3, hbs1⟩ | ⟨h1, h2, hxy⟩ | ⟨hl, ha4, hbs2⟩ | ⟨h1, h2, hxy⟩
            · refine ⟨liftBag (anchor i) ∪ spineSet m i, hsp_in_raw, ?_, ?_⟩
              · rw [ha_eq, show offOf m a = ⟨0, by omega⟩ from Fin.ext ha0]
                exact Finset.mem_union_left _ hp0_mem
              · rw [hb_eq, show offOf m b = ⟨2, by omega⟩ from Fin.ext hb2]
                exact Finset.mem_union_right _ (by unfold spineSet; simp)
            · refine ⟨liftBag (anchor i) ∪ spineSet m i, hsp_in_raw, ?_, ?_⟩
              · rw [ha_eq, show offOf m a = ⟨2, by omega⟩ from Fin.ext ha2]
                exact Finset.mem_union_right _ (by unfold spineSet; simp)
              · rw [hb_eq, show offOf m b = ⟨3, by omega⟩ from Fin.ext hb3]
                exact Finset.mem_union_right _ (by unfold spineSet; simp)
            · refine ⟨liftBag (anchor i) ∪ spineSet m i, hsp_in_raw, ?_, ?_⟩
              · rw [ha_eq, show offOf m a = ⟨3, by omega⟩ from Fin.ext ha3]
                exact Finset.mem_union_right _ (by unfold spineSet; simp)
              · rw [hb_eq, show offOf m b = ⟨4, by omega⟩ from Fin.ext hb4]
                exact Finset.mem_union_right _ (by unfold spineSet; simp)
            · refine ⟨liftBag (anchor i) ∪ spineSet m i, hsp_in_raw, ?_, ?_⟩
              · rw [ha_eq, show offOf m a = ⟨4, by omega⟩ from Fin.ext ha4]
                exact Finset.mem_union_right _ (by unfold spineSet; simp)
              · rw [hb_eq, show offOf m b = ⟨5, by omega⟩ from Fin.ext hb5]
                exact Finset.mem_union_right _ (by unfold spineSet; simp)
            · refine ⟨liftBag (anchor i) ∪ spineSet m i, hsp_in_raw, ?_, ?_⟩
              · rw [ha_eq, show offOf m a = ⟨1, by omega⟩ from Fin.ext ha1]
                exact Finset.mem_union_left _ hp1_mem
              · rw [hb_eq, show offOf m b = ⟨5, by omega⟩ from Fin.ext hb5]
                exact Finset.mem_union_right _ (by unfold spineSet; simp)
            · let k : Fin (L0Of m) := ⟨0, by omega⟩
              set B := tailBag m i (s0Of m) (L0Of m) (by omega) k
              have hB : B ∈ localBags m i := by
                unfold localBags; simp only [List.mem_append]; left; left; left; right
                exact List.mem_map.mpr ⟨k, List.mem_finRange _, rfl⟩
              refine ⟨liftBag (anchor i) ∪ B, hlocal_in_raw i B hB, ?_, ?_⟩
              · rw [ha_eq, show offOf m a = ⟨2, by omega⟩ from Fin.ext ha2]
                refine Finset.mem_union_right _ ?_
                simp [B, tailBag, k, spineSet]
              · rw [hb_eq, show offOf m b = ⟨s0Of m, by omega⟩ from Fin.ext hbs0]
                refine Finset.mem_union_right _ ?_
                simp [B, tailBag, k]
            · let k : Fin (L0Of m) := ⟨(offOf m a).val - s0Of m + 1, by omega⟩
              set B := tailBag m i (s0Of m) (L0Of m) (by omega) k
              have hB : B ∈ localBags m i := by
                unfold localBags; simp only [List.mem_append]; left; left; left; right
                exact List.mem_map.mpr ⟨k, List.mem_finRange _, rfl⟩
              refine ⟨liftBag (anchor i) ∪ B, hlocal_in_raw i B hB, ?_, ?_⟩
              · refine Finset.mem_union_right _ ?_
                have hk0 : ¬ (k.val = 0) := by simp [k]
                simp only [B, tailBag, hk0, ↓reduceIte, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
                right; left; rw [ha_eq]; congr 1; ext; simp [k]; omega
              · refine Finset.mem_union_right _ ?_
                have hk0 : ¬ (k.val = 0) := by simp [k]
                simp only [B, tailBag, hk0, ↓reduceIte, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
                right; right; rw [hb_eq]; congr 1; ext; simp [k]; omega
            · let k : Fin (L0Of m) := ⟨0, by omega⟩
              set B := tailBag m i (s3Of m) (L0Of m) (by omega) k
              have hB : B ∈ localBags m i := by
                unfold localBags; simp only [List.mem_append]; left; left; right
                exact List.mem_map.mpr ⟨k, List.mem_finRange _, rfl⟩
              refine ⟨liftBag (anchor i) ∪ B, hlocal_in_raw i B hB, ?_, ?_⟩
              · rw [ha_eq, show offOf m a = ⟨5, by omega⟩ from Fin.ext ha5]
                refine Finset.mem_union_right _ ?_
                simp [B, tailBag, k, spineSet]
              · rw [hb_eq, show offOf m b = ⟨s3Of m, by omega⟩ from Fin.ext hbs3]
                refine Finset.mem_union_right _ ?_
                simp [B, tailBag, k]
            · let k : Fin (L0Of m) := ⟨(offOf m a).val - s3Of m + 1, by omega⟩
              set B := tailBag m i (s3Of m) (L0Of m) (by omega) k
              have hB : B ∈ localBags m i := by
                unfold localBags; simp only [List.mem_append]; left; left; right
                exact List.mem_map.mpr ⟨k, List.mem_finRange _, rfl⟩
              refine ⟨liftBag (anchor i) ∪ B, hlocal_in_raw i B hB, ?_, ?_⟩
              · refine Finset.mem_union_right _ ?_
                have hk0 : ¬ (k.val = 0) := by simp [k]
                simp only [B, tailBag, hk0, ↓reduceIte, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
                right; left; rw [ha_eq]; congr 1; ext; simp [k]; omega
              · refine Finset.mem_union_right _ ?_
                have hk0 : ¬ (k.val = 0) := by simp [k]
                simp only [B, tailBag, hk0, ↓reduceIte, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
                right; right; rw [hb_eq]; congr 1; ext; simp [k]; omega
            · let k : Fin (L1Of m) := ⟨0, by omega⟩
              set B := tailBag m i (s1Of m) (L1Of m) (by omega) k
              have hB : B ∈ localBags m i := by
                unfold localBags; simp only [List.mem_append]; left; right
                exact List.mem_map.mpr ⟨k, List.mem_finRange _, rfl⟩
              refine ⟨liftBag (anchor i) ∪ B, hlocal_in_raw i B hB, ?_, ?_⟩
              · rw [ha_eq, show offOf m a = ⟨3, by omega⟩ from Fin.ext ha3]
                refine Finset.mem_union_right _ ?_
                simp [B, tailBag, k, spineSet]
              · rw [hb_eq, show offOf m b = ⟨s1Of m, by omega⟩ from Fin.ext hbs1]
                refine Finset.mem_union_right _ ?_
                simp [B, tailBag, k]
            · let k : Fin (L1Of m) := ⟨(offOf m a).val - s1Of m + 1, by omega⟩
              set B := tailBag m i (s1Of m) (L1Of m) (by omega) k
              have hB : B ∈ localBags m i := by
                unfold localBags; simp only [List.mem_append]; left; right
                exact List.mem_map.mpr ⟨k, List.mem_finRange _, rfl⟩
              refine ⟨liftBag (anchor i) ∪ B, hlocal_in_raw i B hB, ?_, ?_⟩
              · refine Finset.mem_union_right _ ?_
                have hk0 : ¬ (k.val = 0) := by simp [k]
                simp only [B, tailBag, hk0, ↓reduceIte, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
                right; left; rw [ha_eq]; congr 1; ext; simp [k]; omega
              · refine Finset.mem_union_right _ ?_
                have hk0 : ¬ (k.val = 0) := by simp [k]
                simp only [B, tailBag, hk0, ↓reduceIte, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
                right; right; rw [hb_eq]; congr 1; ext; simp [k]; omega
            · let k : Fin (L1Of m) := ⟨0, by omega⟩
              set B := tailBag m i (s2Of m) (L1Of m) (by omega) k
              have hB : B ∈ localBags m i := by
                unfold localBags; simp only [List.mem_append]; right
                exact List.mem_map.mpr ⟨k, List.mem_finRange _, rfl⟩
              refine ⟨liftBag (anchor i) ∪ B, hlocal_in_raw i B hB, ?_, ?_⟩
              · rw [ha_eq, show offOf m a = ⟨4, by omega⟩ from Fin.ext ha4]
                refine Finset.mem_union_right _ ?_
                simp [B, tailBag, k, spineSet]
              · rw [hb_eq, show offOf m b = ⟨s2Of m, by omega⟩ from Fin.ext hbs2]
                refine Finset.mem_union_right _ ?_
                simp [B, tailBag, k]
            · let k : Fin (L1Of m) := ⟨(offOf m a).val - s2Of m + 1, by omega⟩
              set B := tailBag m i (s2Of m) (L1Of m) (by omega) k
              have hB : B ∈ localBags m i := by
                unfold localBags; simp only [List.mem_append]; right
                exact List.mem_map.mpr ⟨k, List.mem_finRange _, rfl⟩
              refine ⟨liftBag (anchor i) ∪ B, hlocal_in_raw i B hB, ?_, ?_⟩
              · refine Finset.mem_union_right _ ?_
                have hk0 : ¬ (k.val = 0) := by simp [k]
                simp only [B, tailBag, hk0, ↓reduceIte, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
                right; left; rw [ha_eq]; congr 1; ext; simp [k]; omega
              · refine Finset.mem_union_right _ ?_
                have hk0 : ¬ (k.val = 0) := by simp [k]
                simp only [B, tailBag, hk0, ↓reduceIte, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
                right; right; rw [hb_eq]; congr 1; ext; simp [k]; omega
          rcases hab with hab | hab
          · exact hdir_cov u v ho hab
          · rcases hdir_cov v u ho.symm hab with ⟨B, hB, hvB, huB⟩
            exact ⟨B, hB, huB, hvB⟩
        · set pu : Fin m × Bool := (ownerOf m u, Nat.beq (offOf m u).val 1)
          set pv : Fin m × Bool := (ownerOf m v, Nat.beq (offOf m v).val 1)
          rcases he0 pu pv hg with ⟨t, hpu, hpv⟩
          refine ⟨liftBag t, hlift_in_raw t, ?_, ?_⟩
          · rw [eq_portOf_of_off_lt_two m u huo, hlift_port]; exact hpu
          · rw [eq_portOf_of_off_lt_two m v hvo, hlift_port]; exact hpv
      · intro v
        by_cases hport : (offOf m v).val < 2
        · set p : Fin m × Bool := (ownerOf m v, Nat.beq (offOf m v).val 1)
          have hvp : v = portOf m p := eq_portOf_of_off_lt_two m v hport
          have hsec_iff : ∀ t : Fin l0, ∀ B ∈ blockSection t, v ∈ B ↔ p ∈ bag0 t := by
            intro t B hB
            rcases List.mem_append.mp hB with h1 | h2
            · simp only [List.mem_singleton] at h1
              subst h1
              rw [hvp, hlift_port]
            · rcases List.mem_flatMap.mp h2 with ⟨i, _, hBi⟩
              rcases List.mem_map.mp hBi with ⟨B', hB', rfl⟩
              have hv_not : portOf m p ∉ B' := by
                intro hvB'
                have := (localBags_mem_bounds m i B' hB' v (hvp.symm ▸ hvB')).2
                omega
              rw [Finset.mem_union, hvp, hlift_port]
              exact ⟨fun h => h.elim id (fun hb => (hv_not hb).elim), Or.inl⟩
          let tagged : List (Fin l0 × Finset (Fin (m * BOf m))) :=
            (List.finRange l0).flatMap (fun t => (blockSection t).map (fun B => (t, B)))
          have hmap_snd : tagged.map Prod.snd = rawBags := by
            simp only [tagged, rawBags, List.map_flatMap, List.map_map]
            congr 1
            funext t
            simp
          have hlen_eq : tagged.length = rawBags.length := by
            rw [← hmap_snd, List.length_map]
          have htag_mem : ∀ k (hk : k < tagged.length),
              v ∈ tagged[k].2 ↔ p ∈ bag0 tagged[k].1 := by
            intro k hk
            have hmem := List.getElem_mem hk
            rcases List.mem_flatMap.mp hmem with ⟨t, _, hmt⟩
            rcases List.mem_map.mp hmt with ⟨B, hB, heq⟩
            have ht1 : tagged[k].1 = t := by rw [← heq]
            have ht2 : tagged[k].2 = B := by rw [← heq]
            rw [ht1, ht2]
            exact hsec_iff t B hB
          have htag_pw : tagged.Pairwise (fun a b => a.1 ≤ b.1) := by
            rw [List.pairwise_flatMap]
            refine ⟨?_, ?_⟩
            · intro t _
              rw [List.pairwise_map]
              exact List.pairwise_iff_getElem.mpr (fun _ _ _ _ _ => le_refl t)
            · have hfr : (List.finRange l0).Pairwise (fun a b => a ≤ b) := by
                rw [List.pairwise_iff_getElem]
                intro i j hi hj hij
                simp only [List.getElem_finRange]
                exact Nat.le_of_lt hij
              refine hfr.imp ?_
              intro t1 t2 hle x hx y hy
              rcases List.mem_map.mp hx with ⟨_, _, rfl⟩
              rcases List.mem_map.mp hy with ⟨_, _, rfl⟩
              exact hle
          intro s t u hs ht hu hst htu hvs hvu
          have hs' : s < tagged.length := by omega
          have ht' : t < tagged.length := by omega
          have hu' : u < tagged.length := by omega
          have hget : ∀ k (hk : k < rawBags.length), rawBags[k] = (tagged[k]'(by omega)).2 := by
            intro k hk
            have hk' : k < (tagged.map Prod.snd).length := by rwa [hmap_snd]
            have h1 : (tagged.map Prod.snd)[k]'hk' = (tagged[k]'(by omega)).2 := by
              simp only [List.getElem_map]
            simpa [hmap_snd] using h1
          rw [hget s hs] at hvs
          rw [hget u hu] at hvu
          rw [hget t ht]
          have hps : p ∈ bag0 tagged[s].1 := (htag_mem s hs').mp hvs
          have hpu : p ∈ bag0 tagged[u].1 := (htag_mem u hu').mp hvu
          have hle1 : tagged[s].1 ≤ tagged[t].1 := by
            by_cases heq : s = t
            · subst heq; exact le_refl _
            · exact List.pairwise_iff_getElem.mp htag_pw s t hs' ht' (by omega)
          have hle2 : tagged[t].1 ≤ tagged[u].1 := by
            by_cases heq : t = u
            · subst heq; exact le_refl _
            · exact List.pairwise_iff_getElem.mp htag_pw t u ht' hu' (by omega)
          exact (htag_mem t ht').mpr (hcont0 p tagged[s].1 tagged[t].1 tagged[u].1 hle1 hle2 hps hpu)
        · set i := ownerOf m v
          have hv_ge : 2 ≤ (offOf m v).val := by omega
          refine contig_flatMap_unique (List.finRange l0) blockSection v (anchor i)
            (List.nodup_finRange l0) ?_ ?_
          · refine contig_append_right [liftBag (anchor i)] _ v ?_ ?_
            · intro B hB
              simp only [List.mem_singleton] at hB
              subst hB
              exact hlift_no_int (anchor i) v hv_ge
            · refine contig_flatMap_unique
                ((List.finRange m).filter (fun j => anchor j = anchor i))
                (fun j => (localBags m j).map (fun B => liftBag (anchor i) ∪ B))
                v i ((List.nodup_finRange m).filter _) ?_ ?_
              · exact contig_map_union_left (localBags m i) (liftBag (anchor i)) v
                  (hlift_no_int (anchor i) v hv_ge) (localBags_contig m i v)
              · intro j _ hjne B hB
                rcases List.mem_map.mp hB with ⟨B', hB', rfl⟩
                rw [Finset.mem_union]
                rintro (h | h)
                · exact hlift_no_int (anchor i) v hv_ge h
                · exact hjne (localBags_mem_bounds m j B' hB' v h).1.symm
          · intro t _ htne B hB
            rcases List.mem_append.mp hB with h1 | h2
            · simp only [List.mem_singleton] at h1
              subst h1
              exact hlift_no_int t v hv_ge
            · rcases List.mem_flatMap.mp h2 with ⟨j, hj, hBj⟩
              have hjanc : anchor j = t := by
                simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at hj
                exact hj
              rcases List.mem_map.mp hBj with ⟨B', hB', rfl⟩
              rw [Finset.mem_union]
              rintro (h | h)
              · exact hlift_no_int t v hv_ge h
              · have hoj : ownerOf m v = j := (localBags_mem_bounds m j B' hB' v h).1
                have hij : i = j := hoj
                rw [← hij] at hjanc
                exact htne hjanc.symm
    rcases compress_goodDecomp rawBags.length rawBags rfl hgood with ⟨Bs', hlen', hg'⟩
    rcases hg' with ⟨_, hcard', hv', he', hcont'⟩
    refine ⟨Bs'.length, fun t => Bs'[t.val]'t.isLt, by omega, ?_, ?_, ?_, ?_⟩
    · intro t
      exact hcard' Bs'[t.val] (List.getElem_mem t.isLt)
    · intro v
      rcases hv' v with ⟨B, hB, hvB⟩
      rcases List.getElem_of_mem hB with ⟨idx, hidx, rfl⟩
      exact ⟨⟨idx, hidx⟩, hvB⟩
    · intro u v huv
      rcases he' u v huv with ⟨B, hB, huB, hvB⟩
      rcases List.getElem_of_mem hB with ⟨idx, hidx, rfl⟩
      exact ⟨⟨idx, hidx⟩, huB, hvB⟩
    · intro v s t u hst htu hvs hvu
      exact hcont' v s.val t.val u.val s.isLt t.isLt u.isLt hst htu hvs hvu

end PEqualNP.Outside.L_lib_1217

theorem PEqualNP.Outside.L_lib_1217 : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (m w : Nat) (G : (Fin m × Bool) → Finset (Fin m × Bool)),
  (∀ p, p ∉ G p ∧ (G p).card ≤ 3) → (∀ p r, r ∈ G p ↔ p ∈ G r) →
  (∀ p, ∀ r ∈ G p, p.2 ≠ r.2) → (∀ i, (i,true) ∈ G (i,false)) →
  (∃ (l : Nat) (bag : Fin l → Finset (Fin m × Bool)),
    (∀ t, (bag t).card ≤ w) ∧ (∀ p, ∃ t, p ∈ bag t) ∧
    (∀ p r, r ∈ G p → ∃ t, p ∈ bag t ∧ r ∈ bag t) ∧
    ∀ p s t u, s ≤ t → t ≤ u → p ∈ bag s → p ∈ bag u → p ∈ bag t) →
  let d := 3*m+2
  let M := Nat.fib (d-1) + Nat.fib (d+1)
  let c := (Nat.fib (2*d-1)^2 * Nat.fib d^2 * ((M-1)/2)) % M
  2^m < M ∧ Nat.Coprime c M ∧
  ∃ (N : Nat) (H : Fin N → Finset (Fin N)) (shore : Fin N → Bool)
    (owner : Fin N → Fin m),
    N = m*(6*d-4) ∧ (∀ v, v ∉ H v ∧ (H v).card ≤ 3) ∧
    (∀ u v, v ∈ H u ↔ u ∈ H v) ∧ (∀ u, ∀ v ∈ H u, shore u ≠ shore v) ∧
    (∃ (l : Nat) (bag : Fin l → Finset (Fin N)),
      l ≤ 2*N+1 ∧ (∀ t, (bag t).card ≤ w+6) ∧ (∀ v, ∃ t, v ∈ bag t) ∧
      (∀ u v, v ∈ H u → ∃ t, u ∈ bag t ∧ v ∈ bag t) ∧
      ∀ v s t u, s ≤ t → t ≤ u → v ∈ bag s → v ∈ bag u → v ∈ bag t) ∧
    ∀ S : Finset (Fin m),
      let live := (Finset.univ : Finset (Fin m × Bool)).filter (fun p => p.1 ∈ S)
      let cover := fun (C : Finset (Fin m × Bool)) => C ⊆ live ∧
        ∀ p ∈ live, ∀ r ∈ G p, r ∈ live → p ∈ C ∨ r ∈ C
      let opt := ((Finset.univ : Finset (Finset (Fin m × Bool))).filter
        (fun C => cover C ∧ ∀ W, cover W → C.card ≤ W.card)).card
      let total := ((Finset.univ : Finset (Finset (Fin N))).filter
        (fun I => (∀ v ∈ I, owner v ∈ S) ∧ ∀ u ∈ I, ∀ v ∈ H u, v ∉ I)).card
      opt ≤ 2^S.card ∧ total % M = (c^S.card * opt) % M ∧
      ∀ t : Nat, t < M → total % M = (c^S.card * t) % M → t = opt) := by
  intro m w G hG_deg hG_symm hG_bip hG_mark hpd
  refine ⟨PEqualNP.Outside.L_lib_1217.two_pow_lt_MOf m,
    PEqualNP.Outside.L_lib_1217.coprime_cOf_MOf m,
    m * PEqualNP.Outside.L_lib_1217.BOf m,
    PEqualNP.Outside.L_lib_1217.HOf m G,
    PEqualNP.Outside.L_lib_1217.shoreOf m,
    PEqualNP.Outside.L_lib_1217.ownerOf m,
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    exact ⟨PEqualNP.Outside.L_lib_1217.HOf_irrefl m G v,
      PEqualNP.Outside.L_lib_1217.HOf_card_le_three m G hG_deg hG_symm hG_mark v⟩
  · exact PEqualNP.Outside.L_lib_1217.HOf_symm m G hG_symm
  · exact PEqualNP.Outside.L_lib_1217.HOf_bipartite m G hG_bip
  · exact PEqualNP.Outside.L_lib_1217.step5_path_decomp m w G hG_mark hpd
  · intro S
    exact PEqualNP.Outside.L_lib_1217.step4_recovery m G hG_bip hG_mark S
