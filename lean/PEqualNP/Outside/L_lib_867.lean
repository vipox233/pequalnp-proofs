import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_867_aux
open Finset
variable {l : ℕ} [NeZero l]

def idx (l : ℕ) [NeZero l] (n : ℕ) : Fin l := ⟨n%l,Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne l))⟩
theorem idx_add (a b : ℕ) : idx l (a+b) = idx l a + idx l b := by
  apply Fin.ext
  exact Nat.add_mod _ _ _
theorem idx_lt_ne (five : 5 ≤ l) (n : ℕ) {a b : ℕ} (ha : a < 5) (hb : b < 5) (ne : a ≠ b) :
    idx l (n+a) ≠ idx l (n+b) := by
  rw [idx_add,idx_add,ne_eq,add_right_inj]
  intro eq
  have eqv := congrArg Fin.val eq
  apply ne
  simpa [idx,Nat.mod_eq_of_lt (show a < l by omega),
    Nat.mod_eq_of_lt (show b < l by omega)] using eqv
theorem index_val (i : Fin l) : idx l i.val = i := by apply Fin.ext; simp [idx,Nat.mod_eq_of_lt i.isLt]
theorem shiftIdx (i : Fin l) (d : ℕ) (h : 0 < l) :
    (⟨(i.val+d)%l,Nat.mod_lt _ h⟩ : Fin l) = idx l (i.val+d) := by rfl
theorem addMod (a b : ℕ) : idx l (a%l+b) = idx l (a+b) := by
  apply Fin.ext
  simp [idx,Nat.mod_add_mod]
theorem periodic (n : ℕ) : idx l (n+l) = idx l n := by apply Fin.ext; simp [idx]
theorem shiftedSum (f : Fin l → ℕ) (d : ℕ) :
    (∑ i : Fin l, f (idx l (i.val+d))) = ∑ i : Fin l, f i := by
  simp_rw [idx_add,index_val]
  exact Equiv.sum_comp (Equiv.addRight (idx l d)) f

section
variable (e : Fin l → Fin l → Prop)
variable (five : 5 ≤ l) (sym : ∀ x y, e x y → e y x)
variable (uniq : ∀ x y z, e x y → e x z → y=z)
def adj (n : ℕ) := e (idx l n) (idx l (n+1))
def jump (n : ℕ) := e (idx l n) (idx l (n+2))
include five sym uniq in

theorem conflicts (n : ℕ) :
    (¬ (adj e n ∧ adj e (n+1))) ∧
    (jump e n → ¬ adj e n ∧ ¬ adj e (n+1) ∧ ¬ adj e (n+2) ∧ ¬ jump e (n+2)) := by
  have diff (a b : ℕ) (ha : a<5) (hb : b<5) (ne : a≠b) := idx_lt_ne (l:=l) five n ha hb ne
  have d02 : idx l n ≠ idx l (n+2) := by simpa using diff 0 2 (by decide) (by decide) (by decide)
  have d21 := diff 2 1 (by decide) (by decide) (by decide)
  have d01 : idx l n ≠ idx l (n+1) := by simpa using diff 0 1 (by decide) (by decide) (by decide)
  have d03 : idx l n ≠ idx l (n+3) := by simpa using diff 0 3 (by decide) (by decide) (by decide)
  have d04 : idx l n ≠ idx l (n+4) := by simpa using diff 0 4 (by decide) (by decide) (by decide)
  constructor
  · exact fun ⟨a,b⟩ => d02 (uniq _ _ _ (sym _ _ a) b)
  · intro j
    exact ⟨fun a => d21 (uniq _ _ _ j a),
      fun a => d01 (uniq _ _ _ (sym _ _ j) (sym _ _ a)),
      fun a => d03 (uniq _ _ _ (sym _ _ j) a),
      fun a => d04 (uniq _ _ _ (sym _ _ j) a)⟩

include five sym uniq in

theorem alternating (cover : ∀ n, adj e n ∨ jump e n ∨ adj e (n+1)) :
    ∀ n, adj e (n+1) ↔ ¬ adj e n := by
  have C := conflicts e five sym uniq
  have noJ (n : ℕ) : ¬jump e n := by
    intro h
    obtain ⟨_,hn1,hn2,hnj⟩ := (C n).2 h
    have hj1 := (cover (n+1)).resolve_left hn1
    have j1 := hj1.resolve_right hn2
    exact ((cover (n+2)).resolve_left hn2).elim hnj ((C (n+1)).2 j1).2.2.1
  intro n
  exact ⟨fun b a => (C n).1 ⟨a,b⟩,
    fun a => ((cover n).resolve_left a).resolve_left (noJ n)⟩

theorem parityPhase (A : ℕ → Prop) (alt : ∀ n, A (n+1) ↔ ¬ A n) (per : A l ↔ A 0) :
    l%2=0 ∧ ∃ b : Fin 2, ∀ n, A n ↔ n%2 = b.val := by
  classical
  let b : Fin 2 := if A 0 then 0 else 1
  have spec (n : ℕ) : A n ↔ n%2=b.val := by
    induction n with
    | zero => by_cases a : A 0 <;> simp [a,b]
    | succ n ih =>
      rw [alt,ih]
      have h := b.isLt
      omega
  have eq := per.trans (spec 0)
  have eq' := (spec l).symm.trans eq
  have hb := b.isLt
  refine ⟨by simp only [Nat.zero_mod] at eq'; omega,b,spec⟩
end
end PEqualNP.Outside.L_lib_867_aux

namespace PEqualNP.Outside.L_lib_867_aux
open Finset
variable {l : ℕ} [NeZero l]
theorem idxMod (n : ℕ) : idx l (n%l) = idx l n := by apply Fin.ext; simp [idx]
theorem adjMod (e : Fin l → Fin l → Prop) (n : ℕ) : adj e (n%l) ↔ adj e n := by
  simp only [adj,idxMod,addMod]
theorem jumpMod (e : Fin l → Fin l → Prop) (n : ℕ) : jump e (n%l) ↔ jump e n := by
  simp only [jump,idxMod,addMod]
theorem adjModPlus (e : Fin l → Fin l → Prop) (n d : ℕ) : adj e (n%l+d) ↔ adj e (n+d) := by
  simp only [adj,addMod,Nat.add_assoc]
theorem adjPeriod (e : Fin l → Fin l → Prop) (n : ℕ) : adj e (n+l) ↔ adj e n := by
  unfold adj
  rw [periodic, show n+l+1=n+1+l by omega, periodic]
theorem naturalCycle (e : Fin l → Fin l → Prop) (five : 5 ≤ l) (sym : ∀ x y,e x y → e y x)
    (uniq : ∀ x y z,e x y → e x z → y=z) :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    let near := univ.filter (fun i : Fin l => adj e i.val)
    let skip := univ.filter (fun i : Fin l => jump e i.val)
    let miss := univ.filter (fun i : Fin l => ¬(adj e i.val ∨ jump e i.val ∨ adj e (i.val+1)))
    let off := univ.filter (fun i : Fin l => ¬ adj e i.val ∧ ¬ adj e (i.val+(l-1)))
    miss.card + 2*near.card + skip.card = l ∧ miss.card + skip.card = off.card ∧
      (miss.card = 0 ↔ l%2 = 0 ∧ ∃ b : Fin 2, ∀ i : Fin l, adj e i.val ↔ i.val % 2=b.val) := by
  classical
  dsimp only
  let A := adj e
  let S := jump e
  let w := fun (P : Prop) => if P then 1 else 0
  let cov := fun n => A n ∨ S n ∨ A (n+1)
  have C := conflicts e five sym uniq
  have sumShift (d : ℕ) : (∑ i : Fin l, w (A (i.val+d))) = ∑ i : Fin l, w (A i.val) := by
    have h := shiftedSum (fun i : Fin l => w (A i.val)) d
    simpa only [idx,adjMod,A] using h
  have t1 (i : Fin l) : w (¬ cov i.val) + w (A i.val) + w (S i.val) + w (A (i.val+1)) = 1 := by
    obtain ⟨x,y⟩ := C i.val
    change (¬(A i.val ∧ A (i.val+1))) at x
    change (S i.val → ¬A i.val ∧ ¬A (i.val+1) ∧ _) at y
    by_cases h : A i.val <;> by_cases k : S i.val <;> by_cases z : A (i.val+1) <;> simp_all [w,cov]
  have t2 (i : Fin l) :
      w (¬A i.val ∧ ¬A (i.val+(l-1))) + w (A i.val) + w (A (i.val+(l-1))) = 1 := by
    have exc := (C (i.val+(l-1))).1
    rw [show i.val+(l-1)+1=i.val+l by omega, adjPeriod] at exc
    change ¬(A (i.val+(l-1)) ∧ A i.val) at exc
    by_cases h : A i.val <;> by_cases k : A (i.val+(l-1)) <;> simp_all [w]
  have v1 := sum_congr (rfl : (univ : Finset (Fin l)) = univ) (fun i _ => t1 i)
  have v2 := sum_congr (rfl : (univ : Finset (Fin l)) = univ) (fun i _ => t2 i)
  simp only [sum_add_distrib,sumShift,sum_const,card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at v1 v2
  have cnt (P : Fin l → Prop) : (univ.filter P).card = ∑ i, w (P i) := by
    simp only [card_filter,w]
  constructor
  · rw [cnt,cnt,cnt]
    change (∑ i : Fin l, w (¬ cov i.val)) + 2*(∑ i : Fin l,w (A i.val)) +
      (∑ i : Fin l,w (S i.val)) = l
    omega
  constructor
  · rw [cnt,cnt,cnt]
    change (∑ i : Fin l,w (¬ cov i.val)) + (∑ i : Fin l,w (S i.val)) =
      ∑ i : Fin l,w (¬A i.val ∧ ¬A (i.val+(l-1)))
    omega
  simp only [card_eq_zero,filter_eq_empty_iff,mem_univ,true_implies,not_not]
  have empty : (∀ {i : Fin l}, cov i.val) ↔ ∀ n, cov n := by
    constructor
    · intro all n
      have h := @all (idx l n)
      change cov (n%l) at h
      simpa only [cov,A,S,adjMod,jumpMod,adjModPlus] using h
    · intro all i; exact all i.val
  change (∀ {i : Fin l}, cov i.val) ↔ _
  rw [empty]
  constructor
  · intro full
    have per : A l ↔ A 0 := by simpa [A] using adjPeriod e 0
    obtain ⟨hl,b,hb⟩ := parityPhase A (alternating e five sym uniq full) per
    exact ⟨hl,b,fun i => hb i.val⟩
  · rintro ⟨even,b,phase⟩ n
    have ph (j : ℕ) : A j ↔ j%2=b.val := by
      have h := phase (idx l j)
      change adj e (j%l) ↔ (j%l)%2=b.val at h
      simpa only [adjMod,Nat.mod_mod_of_dvd _ (Nat.dvd_of_mod_eq_zero even),A] using h
    have hb := b.isLt
    exact (show A n ∨ A (n+1) from by rw [ph,ph]; omega).elim Or.inl (fun h => Or.inr (Or.inr h))
end PEqualNP.Outside.L_lib_867_aux

open PEqualNP.Outside.L_lib_867_aux Finset

namespace PEqualNP.Outside.L_lib_867_aux

noncomputable def cycleFilter {α : Type*} (P : α → Prop) (s : Finset α) : Finset α :=
  @Finset.filter α P (fun i => Classical.propDecidable _) s

theorem cycleFilter_eq {α : Type*} (P : α → Prop) [DecidablePred P] (s : Finset α) :
    s.filter P = cycleFilter P s := by
  ext i
  simp [cycleFilter]

end PEqualNP.Outside.L_lib_867_aux

theorem PEqualNP.Outside.L_lib_867 : (∀ (k l : Nat) (hl : 0 < l), 5 ≤ l →
  ∀ (name : Fin l → Fin k), Function.Injective name →
  ∀ p : Equiv.Perm (Fin k), Function.Involutive p →
  let shift := fun (i : Fin l) (d : Nat) => (⟨(i.val+d) % l, Nat.mod_lt _ hl⟩ : Fin l)
  let edge := fun i j : Fin l => p (name i) = name j
  let near := Finset.univ.filter (fun i : Fin l => edge i (shift i 1))
  let skip := Finset.univ.filter (fun i : Fin l => edge i (shift i 2))
  let miss := Finset.univ.filter (fun i : Fin l =>
    ¬ (edge i (shift i 1) ∨ edge i (shift i 2) ∨ edge (shift i 1) (shift i 2)))
  let off := Finset.univ.filter (fun i : Fin l =>
    ¬ edge i (shift i 1) ∧ ¬ edge (shift i (l-1)) i)
  miss.card + 2*near.card + skip.card = l ∧
    miss.card + skip.card = off.card ∧
    (miss.card = 0 ↔ l % 2 = 0 ∧
      ∃ b : Fin 2, ∀ i : Fin l, edge i (shift i 1) ↔ i.val % 2 = b.val)) := by
  classical
  intro k l hl five name injective p inv
  letI : NeZero l := ⟨Nat.ne_of_gt hl⟩
  let e := fun i j : Fin l => p (name i) = name j
  have sym : ∀ x y, e x y → e y x := by
    intro x y h
    change p (name x) = name y at h
    change p (name y) = name x
    rw [← h,inv]
  have uniq : ∀ x y z, e x y → e x z → y=z :=
    fun _ _ _ h g => injective (h.symm.trans g)
  have prev (n : ℕ) : idx l (n+(l-1)+1) = idx l n := by
    rw [show n+(l-1)+1=n+l by omega, periodic]
  have result := naturalCycle e five sym uniq
  dsimp only at result ⊢
  simp only [adj,jump,e,index_val,prev] at result
  simp only [cycleFilter_eq] at result ⊢
  exact result
