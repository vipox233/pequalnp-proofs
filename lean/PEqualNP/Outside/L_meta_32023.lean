import PEqualNP.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Fib.Basic

open scoped BigOperators Fin.NatCast

namespace PEqualNP.Outside.L_meta_32023

abbrev F := ZMod 2
abbrev Word (k : ℕ) := Fin k → F

section CyclicAlgebra

variable {k : ℕ} [NeZero k]

theorem fin_addNat_index (i : Fin k) (a : ℕ) :
    (i + (a : Fin k)).val = (i.val+a)%k := by
  rw [Fin.val_add]
  change (_ + a % k) % k = _
  exact Nat.add_mod_mod _ _ _

theorem fin_subNat_index (i : Fin k) (a : ℕ) :
    (i - (a : Fin k)).val = (i.val+k-a % k)%k := by
  rw [Fin.val_sub]
  change (k-a % k+i.val)%k = _
  have le : a % k ≤ k := (Nat.mod_lt _ (NeZero.pos k)).le
  congr 1
  omega

theorem finEquiv_natCast (n : ℕ) : ZMod.finEquiv k (n : Fin k) = (n : ZMod k) := by
  cases k with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ k => rfl

@[local simp] theorem finEquiv_two : ZMod.finEquiv k (2 : Fin k) = (2 : ZMod k) :=
  finEquiv_natCast 2

@[local simp] theorem finEquiv_three : ZMod.finEquiv k (3 : Fin k) = (3 : ZMod k) :=
  finEquiv_natCast 3

@[local simp] theorem finEquiv_four : ZMod.finEquiv k (4 : Fin k) = (4 : ZMod k) :=
  finEquiv_natCast 4

@[local simp] theorem finEquiv_five : ZMod.finEquiv k (5 : Fin k) = (5 : ZMod k) :=
  finEquiv_natCast 5

def point (i : Fin k) : Word k →ₗ[F] F := LinearMap.proj i

def shift (j : Fin k) : Word k →ₗ[F] Word k :=
  LinearMap.pi fun i => point (i-j)

def mixer (g : Fin k) : Word k →ₗ[F] Word k :=
  LinearMap.pi fun i => point i + point (i+g) + point (i-g)

def coord : Word k →ₗ[F] Word k := (mixer 1).comp (shift 1)

def column : Word k →ₗ[F] Word k := (mixer 2).comp (shift 3)

omit [NeZero k] in
theorem shift_apply (j : Fin k) (x : Word k) (i : Fin k) : shift j x i = x (i-j) := rfl

omit [NeZero k] in
theorem mixer_apply (g : Fin k) (x : Word k) (i : Fin k) :
    mixer g x i = x i + x (i+g) + x (i-g) := rfl

omit [NeZero k] in
theorem point_apply (i : Fin k) (x : Word k) : point i x = x i := rfl

theorem bit_two : (2 : F) = 0 := by decide +kernel

theorem bit_add_self (x : F) : x+x=0 := by linear_combination x * bit_two

theorem bit_square (x : F) : x*x=x := by
  fin_cases x <;> rfl

theorem bit_neg (x : F) : -x=x := neg_eq_of_add_eq_zero_left (bit_add_self x)

theorem column_of_coord (x : Word k) (j : Fin k) :
    column x j = coord x (j-3) + coord x (j-2) + coord x (j-1) := by
  unfold column coord
  simp only [LinearMap.comp_apply, mixer_apply, shift_apply]
  have i1 : j + 2 - 3 = j - 1 := by apply (ZMod.finEquiv k).injective; simp <;> ring
  have i2 : j - 2 - 3 = j - 5 := by apply (ZMod.finEquiv k).injective; simp <;> ring
  have i3 : j - 3 - 1 = j - 4 := by apply (ZMod.finEquiv k).injective; simp <;> ring
  have i4 : j - 3 + 1 - 1 = j - 3 := by apply (ZMod.finEquiv k).injective; simp <;> ring
  have i5 : j - 3 - 1 - 1 = j - 5 := by apply (ZMod.finEquiv k).injective; simp <;> ring
  have i6 : j - 2 - 1 = j - 3 := by apply (ZMod.finEquiv k).injective; simp <;> ring
  have i7 : j - 2 + 1 - 1 = j - 2 := by apply (ZMod.finEquiv k).injective; simp <;> ring
  have i8 : j - 2 - 1 - 1 = j - 4 := by apply (ZMod.finEquiv k).injective; simp <;> ring
  have i9 : j - 1 - 1 = j - 2 := by apply (ZMod.finEquiv k).injective; simp <;> ring
  have i10 : j - 1 + 1 - 1 = j - 1 := by apply (ZMod.finEquiv k).injective; simp <;> ring
  have i11 : j - 1 - 1 - 1 = j - 3 := by apply (ZMod.finEquiv k).injective; simp <;> ring
  rw [i1, i2, i4, i5, i7, i8, i10, i11, i3, i6, i9]
  linear_combination - bit_add_self (x (j-4)) - bit_add_self (x (j-3)) -
    bit_add_self (x (j-2))

def rowQ (z : Word k) : Word k := fun i => z (i+1) * z (i+2)

def parityQ (z : Word k) : F := ∑ i : Fin k, z i * z (i+3)

def residual (z : Word k) : Word k × F := (rowQ z,parityQ z)

def runAt (L : Word k →ₗ[F] Word k) (t c : Word k) (turn : Fin k) (x : Word k)
    (i : Fin k) : F :=
  let y := L x + t
  y i + (1 + y (i+1)) * y (i+2) + shift turn x i + c i

def affineAt (L : Word k →ₗ[F] Word k) (t : Word k) (turn i : Fin k) : Word k →ₗ[F] F :=
  (point i).comp L + (1+t (i+1)) • ((point (i+2)).comp L) +
    t (i+2) • ((point (i+1)).comp L) + (point i).comp (shift turn)

def constAt (t c : Word k) (i : Fin k) : F :=
  t i + (1+t (i+1))*t (i+2) + c i

theorem runAt_eq (L : Word k →ₗ[F] Word k) (t c : Word k) (turn : Fin k) (x : Word k)
    (i : Fin k) : runAt L t c turn x i =
      (affineAt L t turn i) x + constAt t c i + rowQ (L x) i := by
  simp only [runAt,affineAt,constAt,rowQ,Pi.add_apply,LinearMap.add_apply,
    LinearMap.smul_apply,LinearMap.comp_apply,point_apply,smul_eq_mul]
  ring

theorem sum_shift (f : Fin k → F) (c : Fin k) :
    (∑ i, f (i+c)) = ∑ i, f i := by
  simpa using Equiv.sum_comp (Equiv.addRight c) f

theorem sum_pair_shift (z : Word k) (a b : Fin k) :
    (∑ i : Fin k, z (i+a) * z (i+b)) = ∑ i : Fin k, z i * z (i+(b-a)) := by
  rw [← sum_shift (fun i => z i * z (i+(b-a))) a]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show i+a+(b-a) = i+b by apply (ZMod.finEquiv k).injective; simp <;> ring]

theorem column_product (z : Word k) (i : Fin k) :
    (z (i-2) + z (i-1) + z i) * (z (i-1) + z i + z (i+1)) =
      (z (i-1) + z i) + (z (i-2) * z (i-1) + z i * z (i+1)) +
      (z (i-2) * z i + z (i-1) * z (i+1)) + z (i-2) * z (i+1) := by
  linear_combination bit_square (z (i-1)) + bit_square (z i) +
    bit_add_self (z (i-1) * z i)

theorem column_rowQ (x : Word k) (i : Fin k) :
    rowQ (column x) i = (coord x (i-2) + coord x (i-1) + coord x i) *
      (coord x (i-1) + coord x i + coord x (i+1)) := by
  unfold rowQ
  rw [column_of_coord,column_of_coord]
  rw [show i+1-3=i-2 by apply (ZMod.finEquiv k).injective; simp <;> ring,show i+1-2=i-1 by apply (ZMod.finEquiv k).injective; simp <;> ring,show i+1-1=i by apply (ZMod.finEquiv k).injective; simp <;> ring,
    show i+2-3=i-1 by apply (ZMod.finEquiv k).injective; simp <;> ring,show i+2-2=i by apply (ZMod.finEquiv k).injective; simp <;> ring,show i+2-1=i+1 by apply (ZMod.finEquiv k).injective; simp <;> ring]

theorem column_sum (x : Word k) :
    (∑ i, rowQ (column x) i) = parityQ (coord x) := by
  let z := coord x
  simp_rw [column_rowQ,column_product,Finset.sum_add_distrib]
  change ((∑ i : Fin k,z (i-1)) + ∑ i : Fin k,z i) +
    ((∑ i : Fin k,z (i-2)*z (i-1)) + ∑ i : Fin k,z i*z (i+1)) +
    ((∑ i : Fin k,z (i-2)*z i) + ∑ i : Fin k,z (i-1)*z (i+1)) +
    (∑ i : Fin k,z (i-2)*z (i+1)) = _
  have pair (a b : Fin k) :
      (∑ i : Fin k,z (i+a)*z (i+b)) = ∑ i : Fin k,z i*z (i+(b-a)) := sum_pair_shift z a b
  have c1 : (-1 : Fin k) - (-2) = 1 := by apply (ZMod.finEquiv k).injective; simp <;> ring
  have c2 : (0 : Fin k) - (-2) = 2 := by apply (ZMod.finEquiv k).injective; simp <;> ring
  have c3 : (1 : Fin k) - (-1) = 2 := by apply (ZMod.finEquiv k).injective; simp <;> ring
  have c4 : (1 : Fin k) - (-2) = 3 := by apply (ZMod.finEquiv k).injective; simp <;> ring
  have h1 := pair (-2) (-1)
  have h2 := pair (-2) 0
  have h3 := pair (-1) 1
  have h4 := pair (-2) 1
  rw [c1] at h1
  rw [c2] at h2
  rw [c3] at h3
  rw [c4] at h4
  simp only [sub_eq_add_neg,add_zero] at h1 h2 h3 h4 ⊢
  have single : (∑ i : Fin k,z (i + -1)) = ∑ i : Fin k,z i := sum_shift z (-1)
  rw [single,h1,h2,h3,h4,bit_add_self,zero_add,bit_add_self,zero_add,bit_add_self,zero_add]
  rfl

end CyclicAlgebra

section Trace

variable {S : Type} [Fintype S] [DecidableEq S]

def walkWeight (A : Matrix S S ℤ) : (n : ℕ) → S → (Fin n → S) → S → ℤ
  | 0, a, _, b => A a b
  | n+1, a, p, b => A a (p 0) * walkWeight A n (p 0) (fun i => p i.succ) b

def sequence {n : ℕ} (a : S) (p : Fin n → S) (b : S) : Fin (n+2) → S :=
  Fin.snoc (α := fun _ => S) (Fin.cons (α := fun _ => S) a p) b

omit [Fintype S] [DecidableEq S] in
theorem sequence_first {n : ℕ} (a : S) (p : Fin n → S) (b : S) :
    sequence a p b 0 = a := by
  have eq : (0 : Fin (n+2)) = (0 : Fin (n+1)).castSucc := rfl
  rw [eq]
  simp [sequence]

omit [Fintype S] [DecidableEq S] in
theorem sequence_succ {n : ℕ} (a : S) (p : Fin (n+1) → S) (b : S) (i : Fin (n+2)) :
    sequence a p b i.succ = sequence (p 0) (fun j => p j.succ) b i := by
  induction i using Fin.lastCases with
  | last => simp [sequence]
  | cast j =>
    simp only [sequence,Fin.succ_castSucc,Fin.snoc_castSucc,Fin.cons_succ]
    induction j using Fin.cases with
    | zero => simp
    | succ q => simp

theorem walkWeight_product (A : Matrix S S ℤ) (n : ℕ) (a : S) (p : Fin n → S) (b : S) :
    walkWeight A n a p b =
      ∏ i : Fin (n+1), A (sequence a p b i.castSucc) (sequence a p b i.succ) := by
  induction n generalizing a b with
  | zero =>
    rw [walkWeight,Fin.prod_univ_one]
    rw [show (0 : Fin 1).castSucc = (0 : Fin 2) from rfl,sequence_first]
    rw [show (0 : Fin 1).succ = Fin.last 1 from rfl]
    simp only [sequence,Fin.snoc_last]
  | succ n ih =>
    rw [walkWeight,Fin.prod_univ_succ]
    have head : (0 : Fin (n+2)).castSucc = (0 : Fin (n+3)) := rfl
    rw [head,sequence_first,sequence_succ,sequence_first,ih]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Fin.succ_castSucc,sequence_succ,sequence_succ]

theorem matrix_entry_walk (A : Matrix S S ℤ) (n : ℕ) (a b : S) :
    (A^(n+1)) a b = ∑ p : Fin n → S, walkWeight A n a p b := by
  classical
  induction n generalizing a b with
  | zero => simp [walkWeight]
  | succ n ih =>
    rw [pow_succ',Matrix.mul_apply]
    conv => lhs; arg 2; intro u; rw [ih,Finset.mul_sum]
    calc
      _ = ∑ t : S × (Fin n → S), A a t.1 * walkWeight A n t.1 t.2 b :=
        (Fintype.sum_prod_type (fun t : S × (Fin n → S) => A a t.1 * walkWeight A n t.1 t.2 b)).symm
      _ = _ := by
        refine Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => S)) _ _ ?_
        rintro ⟨u,p⟩
        simp [walkWeight,Fin.consEquiv]

theorem castSucc_next {n : ℕ} (i : Fin n) : i.castSucc + (1 : Fin (n+1)) = i.succ := by
  apply Fin.ext
  rw [Fin.val_add]
  change (i.val+(1 % (n+1)))%(n+1) = i.val+1
  rw [Nat.add_mod_mod]
  exact Nat.mod_eq_of_lt (Nat.succ_lt_succ i.isLt)

omit [Fintype S] [DecidableEq S] in
theorem sequence_closed {n : ℕ} (a : S) (p : Fin n → S) (i : Fin (n+1)) :
    sequence a p a i.succ = Fin.cons (α := fun _ => S) a p (i+1) := by
  induction i using Fin.lastCases with
  | last => simp [sequence]
  | cast j =>
    rw [castSucc_next, ← Fin.castSucc_succ]
    simp only [sequence,Fin.snoc_castSucc]

theorem trace_cyclic (A : Matrix S S ℤ) (n : ℕ) :
    Matrix.trace (A^(n+1)) = ∑ p : Fin (n+1) → S, ∏ i : Fin (n+1), A (p i) (p (i+1)) := by
  classical
  calc
    _ = ∑ a : S, ∑ p : Fin n → S, walkWeight A n a p a :=
      Finset.sum_congr rfl (fun a _ => matrix_entry_walk A n a a)
    _ = ∑ t : S × (Fin n → S), walkWeight A n t.1 t.2 t.1 :=
      (Fintype.sum_prod_type (fun t : S × (Fin n → S) => walkWeight A n t.1 t.2 t.1)).symm
    _ = _ := by
      refine Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => S)) _ _ ?_
      rintro ⟨a,p⟩
      rw [walkWeight_product]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [sequence_closed]
      simp only [Fin.consEquiv,Equiv.coe_fn_mk,sequence,Fin.snoc_castSucc]

end Trace

section Kernel

variable {k : ℕ} [NeZero k]

def cyclicSeq (x : Word k) (n : ℕ) : F := x (n : Fin k)

theorem cyclicSeq_at (x : Word k) (i : Fin k) : cyclicSeq x i.val = x i := by
  unfold cyclicSeq
  congr 1
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

theorem seq_width_period (x : Word k) (n : ℕ) :
    cyclicSeq x (n+k) = cyclicSeq x n := by
  unfold cyclicSeq
  congr 1
  apply Fin.ext
  change (n+k)%k = n % k
  exact Nat.add_mod_right n k

theorem kernel_recurrence (x : Word k) (hk : coord x = 0) (n : ℕ) :
    cyclicSeq x (n+2) = cyclicSeq x n + cyclicSeq x (n+1) := by
  have zero := congrFun hk ((n+2 : ℕ) : Fin k)
  simp only [coord,LinearMap.comp_apply,mixer_apply,shift_apply] at zero
  have cast_add1 : ((n+2 : ℕ) : Fin k) - 1 = ((n+1 : ℕ) : Fin k) := by
    apply (ZMod.finEquiv k).injective
    simp [map_sub,finEquiv_natCast,Nat.cast_add,finEquiv_two] <;> ring
  have cast_eq : ((n+2 : ℕ) : Fin k)+1-1 = ((n+2 : ℕ) : Fin k) := add_sub_cancel_right _ _
  have cast_sub : ((n+2 : ℕ) : Fin k)-1-1 = (n : Fin k) := by
    apply (ZMod.finEquiv k).injective
    simp [map_sub,finEquiv_natCast,Nat.cast_add,finEquiv_two] <;> ring
  rw [cast_add1,cast_eq] at zero
  have cast_sub' : ((n+1 : ℕ) : Fin k)-1 = (n : Fin k) := by rw [← cast_add1,cast_sub]
  rw [cast_sub'] at zero
  change cyclicSeq x (n+1) + cyclicSeq x (n+2) + cyclicSeq x n = 0 at zero
  linear_combination zero - bit_add_self (cyclicSeq x n) - bit_add_self (cyclicSeq x (n+1))

theorem kernel_period (x : Word k) (hk : coord x = 0) (n : ℕ) :
    cyclicSeq x (n+3) = cyclicSeq x n := by
  have h0 := kernel_recurrence x hk n
  have h1 := kernel_recurrence x hk (n+1)
  change cyclicSeq x (n+3) = cyclicSeq x (n+1) + cyclicSeq x (n+2) at h1
  rw [h1,h0]
  linear_combination bit_add_self (cyclicSeq x (n+1))

theorem kernel_mod_three (x : Word k) (hk : coord x = 0) (n : ℕ) :
    cyclicSeq x n = cyclicSeq x (n % 3) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases h : n < 3
    · rw [Nat.mod_eq_of_lt h]
    · have hn : n = (n-3)+3 := by omega
      calc
        cyclicSeq x n = cyclicSeq x (n-3) := by rw [← kernel_period x hk (n-3),← hn]
        _ = cyclicSeq x ((n-3)%3) := ih _ (by omega)
        _ = cyclicSeq x (n % 3) := by congr 1; omega

theorem coord_kernel_injection :
    Function.Injective (fun x : LinearMap.ker (coord (k := k)) =>
      (cyclicSeq x.val 0,cyclicSeq x.val 1)) := by
  intro x y eq
  have hx : coord x.val = 0 := LinearMap.mem_ker.mp x.property
  have hy : coord y.val = 0 := LinearMap.mem_ker.mp y.property
  have h0 : cyclicSeq x.val 0 = cyclicSeq y.val 0 := congrArg Prod.fst eq
  have h1 : cyclicSeq x.val 1 = cyclicSeq y.val 1 := congrArg Prod.snd eq
  have h2 : cyclicSeq x.val 2 = cyclicSeq y.val 2 := by
    rw [kernel_recurrence x.val hx 0, kernel_recurrence y.val hy 0, h0,h1]
  apply Subtype.ext
  funext i
  rw [← cyclicSeq_at x.val i,← cyclicSeq_at y.val i,kernel_mod_three x.val hx,
    kernel_mod_three y.val hy]
  have bound : i.val % 3 < 3 := Nat.mod_lt _ (by decide)
  interval_cases i.val % 3 <;> assumption

theorem coord_kernel_card [Fintype (LinearMap.ker (coord (k := k)))] :
    Fintype.card (LinearMap.ker (coord (k := k))) ≤ 4 := by
  have h := Fintype.card_le_of_injective _ (coord_kernel_injection (k := k))
  simpa [F,Fintype.card_prod,ZMod.card] using h

theorem coord_kernel_regular (hreg : ¬ 3 ∣ k) (x : Word k) (hx : coord x = 0) : x = 0 := by
  let a := cyclicSeq x 0
  let b := cyclicSeq x 1
  let c := cyclicSeq x 2
  have z : c = a+b := kernel_recurrence x hx 0
  have ak : cyclicSeq x (k % 3) = a := by
    rw [← kernel_mod_three x hx]
    simpa only [a,zero_add] using seq_width_period x 0
  have bk : cyclicSeq x ((k+1)%3) = b := by
    rw [← kernel_mod_three x hx,Nat.add_comm k 1,seq_width_period]
  have nk : k % 3 ≠ 0 := fun e => hreg (Nat.dvd_of_mod_eq_zero e)
  have hk : k % 3 < 3 := Nat.mod_lt _ (by decide)
  have zero : a = 0 ∧ b = 0 := by
    by_cases h : k % 3 = 1
    · have h' : (k+1)%3 = 2 := by omega
      rw [h] at ak
      rw [h'] at bk
      change b = a at ak
      change c = b at bk
      have b0 : b = 0 := calc
        b = c := bk.symm
        _ = a+b := z
        _ = a+a := congrArg (fun t => a+t) ak
        _ = 0 := bit_add_self a
      exact ⟨ak.symm.trans b0,b0⟩
    · have h2 : k % 3 = 2 := by omega
      have h' : (k+1)%3 = 0 := by omega
      rw [h2] at ak
      rw [h'] at bk
      change c = a at ak
      change a = b at bk
      have a0 : a = 0 := calc
        a = c := ak.symm
        _ = a+b := z
        _ = a+a := congrArg (fun t => a+t) bk.symm
        _ = 0 := bit_add_self a
      exact ⟨a0,bk.symm.trans a0⟩
  have c0 : c = 0 := by rw [z,zero.1,zero.2,add_zero]
  funext i
  rw [← cyclicSeq_at x i,kernel_mod_three x hx]
  have bound : i.val % 3 < 3 := Nat.mod_lt _ (by decide)
  interval_cases i.val % 3
  · exact zero.1
  · exact zero.2
  · exact c0

theorem coord_injective (hreg : ¬ 3 ∣ k) : Function.Injective (coord (k := k)) := by
  intro x y h
  have diff : coord (x-y) = 0 := by rw [map_sub,h,sub_self]
  exact sub_eq_zero.mp (coord_kernel_regular hreg (x-y) diff)

theorem coord_surjective (hreg : ¬ 3 ∣ k) : Function.Surjective (coord (k := k)) :=
  Finite.surjective_of_injective (coord_injective hreg)

end Kernel

section Transfer

def stateBits : Fin 5 → Fin 3 → F :=
  ![![0,0,0], ![0,0,1], ![0,1,0], ![1,0,0], ![1,0,1]]

theorem stateBits_injective : Function.Injective stateBits := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | exact False.elim (by
    have he := congrFun h (0 : Fin 3)
    have hf := congrFun h (1 : Fin 3)
    have hg := congrFun h (2 : Fin 3)
    simp [stateBits] at he hf hg)

theorem state_valid (i : Fin 5) :
    stateBits i 0 * stateBits i 1 = 0 ∧ stateBits i 1 * stateBits i 2 = 0 := by
  fin_cases i <;> decide +kernel

theorem state_exists (x y z : F) (h0 : x*y=0) (h1 : y*z=0) :
    ∃ i, stateBits i 0 = x ∧ stateBits i 1 = y ∧ stateBits i 2 = z := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    first
    | exact ⟨0,rfl,rfl,rfl⟩
    | exact ⟨1,rfl,rfl,rfl⟩
    | exact ⟨2,rfl,rfl,rfl⟩
    | exact ⟨3,rfl,rfl,rfl⟩
    | exact ⟨4,rfl,rfl,rfl⟩
    | exact (by
        first
        | have h : (1:F) = 0 := h0; exact (one_ne_zero h).elim
        | have h : (1:F) = 0 := h1; exact (one_ne_zero h).elim)

def bitSign (b : F) : ℤ := if b = 0 then 1 else -1

theorem bit_cases (b : F) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem bitSign_add (a b : F) : bitSign (a+b) = bitSign a * bitSign b := by
  rcases bit_cases a with rfl|rfl <;> rcases bit_cases b with rfl|rfl <;> decide +kernel

theorem bitSign_sum {I : Type} (s : Finset I) (f : I → F) :
    bitSign (∑ i ∈ s, f i) = ∏ i ∈ s, bitSign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bitSign]
  | @insert i s hi ih => simp [hi,bitSign_add,ih]

abbrev overlaps (a b : Fin 5) : Prop :=
  stateBits a 1 = stateBits b 0 ∧ stateBits a 2 = stateBits b 1

def transfer (signed : Bool) : Matrix (Fin 5) (Fin 5) ℤ :=
  fun a b => if overlaps a b then
    if signed then bitSign (stateBits a 0 * stateBits b 2) else 1 else 0

variable {k : ℕ} [NeZero k]

def Independent (x : Word k) : Prop := ∀ i : Fin k, x i * x (i+1) = 0

def Closed (p : Fin k → Fin 5) : Prop := ∀ i : Fin k, overlaps (p i) (p (i+1))

def wordOf (p : Fin k → Fin 5) : Word k := fun i => stateBits (p i) 0

theorem add_two (i : Fin k) : i+1+1=i+2 := by
  apply (ZMod.finEquiv k).injective
  simp only [map_add,map_one,finEquiv_two]
  ring

theorem wordOf_second {p : Fin k → Fin 5} (h : Closed p) (i : Fin k) :
    stateBits (p i) 1 = wordOf p (i+1) := (h i).1

theorem wordOf_third {p : Fin k → Fin 5} (h : Closed p) (i : Fin k) :
    stateBits (p i) 2 = wordOf p (i+2) := by
  exact ((h i).2.trans (wordOf_second h (i+1))).trans (congrArg (wordOf p) (add_two i))

theorem wordOf_independent {p : Fin k → Fin 5} (h : Closed p) :
    Independent (wordOf p) := by
  intro i
  rw [← wordOf_second h i]
  exact (state_valid (p i)).1

noncomputable def stateOf (x : Word k) (h : Independent x) (i : Fin k) : Fin 5 :=
  Classical.choose (state_exists (x i) (x (i+1)) (x (i+2)) (h i)
    (by rw [← add_two]; exact h (i+1)))

theorem stateOf_spec (x : Word k) (h : Independent x) (i : Fin k) :
    stateBits (stateOf x h i) 0 = x i ∧
    stateBits (stateOf x h i) 1 = x (i+1) ∧
    stateBits (stateOf x h i) 2 = x (i+2) :=
  Classical.choose_spec (state_exists (x i) (x (i+1)) (x (i+2)) (h i)
    (by rw [← add_two]; exact h (i+1)))

theorem stateOf_closed (x : Word k) (h : Independent x) : Closed (stateOf x h) := by
  intro i
  have s := stateOf_spec x h i
  have t := stateOf_spec x h (i+1)
  exact ⟨s.2.1.trans t.1.symm,s.2.2.trans ((congrArg x (add_two i).symm).trans t.2.1.symm)⟩

noncomputable def closedEquiv : {p : Fin k → Fin 5 // Closed p} ≃
    {x : Word k // Independent x} where
  toFun p := ⟨wordOf p.val,wordOf_independent p.property⟩
  invFun x := ⟨stateOf x.val x.property,stateOf_closed x.val x.property⟩
  left_inv p := by
    apply Subtype.ext
    funext i
    apply stateBits_injective
    funext j
    have spec := stateOf_spec (wordOf p.val) (wordOf_independent p.property) i
    fin_cases j
    · exact spec.1
    · exact spec.2.1.trans (wordOf_second p.property i).symm
    · exact spec.2.2.trans (wordOf_third p.property i).symm
  right_inv x := by
    apply Subtype.ext
    funext i
    exact (stateOf_spec x.val x.property i).1

theorem weight_for_closed (signed : Bool) (p : Fin k → Fin 5) (hp : Closed p) :
    (∏ i : Fin k, transfer signed (p i) (p (i+1))) =
      if signed then bitSign (parityQ (wordOf p)) else 1 := by
  cases signed
  · change _ = (1:ℤ)
    calc
      _ = ∏ _ : Fin k, (1:ℤ) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        unfold transfer
        rw [ite_eq_left (hp i)]
        rfl
      _ = _ := by simp
  · change _ = bitSign (parityQ (wordOf p))
    rw [parityQ,bitSign_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    unfold transfer
    rw [ite_eq_left (hp i)]
    change bitSign (stateBits (p i) 0 * stateBits (p (i+1)) 2) = _
    rw [wordOf_third hp (i+1)]
    change bitSign (wordOf p i * wordOf p (i+1+2)) = _
    have ix : i+1+2=i+3 := by
      apply (ZMod.finEquiv k).injective
      simp only [map_add,map_one,finEquiv_two,finEquiv_three]
      ring
    rw [ix]

theorem weight_not_closed (signed : Bool) (p : Fin k → Fin 5) (hp : ¬ Closed p) :
    (∏ i : Fin k, transfer signed (p i) (p (i+1))) = 0 := by
  have h : ∃ i : Fin k, ¬ overlaps (p i) (p (i+1)) := not_forall.mp hp
  obtain ⟨i,hi⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [transfer,hi])

noncomputable def independentWords (k : ℕ) [NeZero k] : Finset (Word k) := by
  classical
  exact Finset.univ.filter Independent

theorem trace_count (signed : Bool) (n : ℕ) :
    Matrix.trace ((transfer signed)^(n+1)) =
      ∑ z ∈ independentWords (n+1), if signed then bitSign (parityQ z) else 1 := by
  classical
  rw [trace_cyclic]
  let D := Finset.univ.filter (Closed (k := n+1))
  let wt (z : Word (n+1)) := if signed then bitSign (parityQ z) else 1
  calc
    _ = ∑ p ∈ D, wt (wordOf p) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : Closed p
      · simpa [hp,wt] using weight_for_closed signed p hp
      · simpa [hp] using weight_not_closed signed p hp
    _ = ∑ p : {p : Fin (n+1) → Fin 5 // Closed p}, wt (wordOf p.val) := by
      have mem : ∀ p, p ∈ D ↔ Closed p := by simp [D]
      exact Finset.sum_subtype D mem (fun p => wt (wordOf p))
    _ = ∑ z : {z : Word (n+1) // Independent z}, wt z.val :=
      Fintype.sum_equiv closedEquiv _ _ (by intro p; rfl)
    _ = _ := by
      have mem : ∀ z, z ∈ independentWords (n+1) ↔ Independent z := by simp [independentWords]
      exact (Finset.sum_subtype (independentWords (n+1)) mem wt).symm

end Transfer

section TraceValues

theorem unsigned_power_relation :
    (transfer false)^4 = (transfer false)^3 + (transfer false)^2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem signed_power_relation :
    (transfer true)^5 = (transfer true)^4 + (transfer true)^3 -
      ((transfer true)^2 + (transfer true)^2) + (transfer true + transfer true) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem unsigned_trace_step (n : ℕ) :
    Matrix.trace ((transfer false)^(n+4)) =
      Matrix.trace ((transfer false)^(n+3)) + Matrix.trace ((transfer false)^(n+2)) := by
  have h := congrArg (fun A => Matrix.trace ((transfer false)^n * A)) unsigned_power_relation
  simpa only [mul_add,← pow_add,Matrix.trace_add] using h

theorem signed_trace_step (n : ℕ) :
    Matrix.trace ((transfer true)^(n+5)) =
      Matrix.trace ((transfer true)^(n+4)) + Matrix.trace ((transfer true)^(n+3)) -
      2 * Matrix.trace ((transfer true)^(n+2)) + 2 * Matrix.trace ((transfer true)^(n+1)) := by
  have h := congrArg (fun A => Matrix.trace ((transfer true)^n * A)) signed_power_relation
  simp only [mul_add,mul_sub,← pow_add,Matrix.trace_add,Matrix.trace_sub] at h
  have blend : (transfer true)^n * transfer true = (transfer true)^(n+1) := (pow_succ _ _).symm
  rw [blend] at h
  linarith

def lucas (n : ℕ) : ℕ := Nat.fib (n-1) + Nat.fib (n+1)

theorem lucas_step (n : ℕ) : lucas (n+4) = lucas (n+3) + lucas (n+2) := by
  unfold lucas
  rw [show n+4-1=n+3 by omega, show n+3-1=n+2 by omega, show n+2-1=n+1 by omega]
  change Nat.fib (n+3)+Nat.fib (n+5) =
    Nat.fib (n+2)+Nat.fib (n+4)+(Nat.fib (n+1)+Nat.fib (n+3))
  have h0 : Nat.fib (n+3) = Nat.fib (n+1)+Nat.fib (n+2) := Nat.fib_add_two
  have h1 : Nat.fib (n+5) = Nat.fib (n+3)+Nat.fib (n+4) := Nat.fib_add_two
  omega

theorem unsigned_trace (n : ℕ) (hn : 0 < n) :
    Matrix.trace ((transfer false)^n) = (lucas n : ℤ) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hs : n < 4
    · interval_cases n <;> decide +kernel
    · obtain ⟨t,rfl⟩ : ∃ t, n=t+4 := ⟨n-4,by omega⟩
      rw [unsigned_trace_step,lucas_step,Nat.cast_add,ih (t+3) (by omega) (by omega),
        ih (t+2) (by omega) (by omega)]

def grows (n : ℕ) : ℤ := if 2 ∣ n then 2^(1+n/2) else 0

def periodic (n : ℕ) : ℤ :=
  if 3 ∣ n then (if 2 ∣ n then 2 else -2) else (if 2 ∣ n then -1 else 1)

def signedValue (n : ℕ) : ℤ := grows n + periodic n

theorem grows_step (n : ℕ) : grows (n+2) = 2*grows n := by
  have even : (2 ∣ n+2) ↔ 2 ∣ n := by omega
  have half : (n+2)/2 = n/2+1 := by omega
  simp only [grows,even,half,← Nat.add_assoc,pow_succ]
  by_cases h : 2 ∣ n <;> simp [h,mul_comm]

theorem periodic_modsix (n : ℕ) : periodic n = periodic (n % 6) := by
  have two : 2 ∣ n ↔ 2 ∣ n % 6 := by omega
  have three : 3 ∣ n ↔ 3 ∣ n % 6 := by omega
  simp only [periodic,two,three]

theorem periodic_step (n : ℕ) : periodic (n+2) = periodic (n+1) - periodic n := by
  rw [periodic_modsix (n+2), periodic_modsix (n+1), periodic_modsix n]
  have r2 : (n+2)%6 = (n % 6+2)%6 := by omega
  have r1 : (n+1)%6 = (n % 6+1)%6 := by omega
  rw [r2,r1]
  have lt : n % 6 < 6 := Nat.mod_lt _ (by decide)
  interval_cases n % 6 <;> decide +kernel

theorem signed_step (n : ℕ) :
    signedValue (n+4) = signedValue (n+3) + signedValue (n+2) -
      2*signedValue (n+1) + 2*signedValue n := by
  unfold signedValue
  have a0 := grows_step n
  have a1 := grows_step (n+1)
  have a2 := grows_step (n+2)
  have b0 := periodic_step n
  have b2 := periodic_step (n+2)
  linear_combination a2-a1+a0+b2-2*b0

theorem signed_trace (n : ℕ) (hn : 0 < n) :
    Matrix.trace ((transfer true)^n) = signedValue n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hs : n < 5
    · interval_cases n <;> decide +kernel
    · obtain ⟨t,rfl⟩ : ∃ t, n=t+5 := ⟨n-5,by omega⟩
      rw [signed_trace_step,ih (t+4) (by omega) (by omega),ih (t+3) (by omega) (by omega),
        ih (t+2) (by omega) (by omega),ih (t+1) (by omega) (by omega)]
      exact (signed_step (t+1)).symm

variable {k : ℕ} [NeZero k]

noncomputable def zeroWords (k : ℕ) [NeZero k] : Finset (Word k) :=
  (independentWords k).filter (fun z => parityQ z = 0)

theorem zeroWords_solution (k : ℕ) [NeZero k] :
    zeroWords k = Finset.univ.filter (fun z : Word k => residual z = 0) := by
  classical
  ext x
  simp only [zeroWords,independentWords,Finset.mem_filter,Finset.mem_univ,true_and,
    residual,Prod.mk_eq_zero,Independent]
  constructor
  · rintro ⟨h,p⟩
    refine ⟨funext (fun i => ?_),p⟩
    change x (i+1) * x (i+2) = 0
    simpa only [add_two i] using h (i+1)
  · rintro ⟨hr,p⟩
    refine ⟨fun i => ?_,p⟩
    have h := congrFun hr (i-1)
    change x (i-1+1)*x (i-1+2)=0 at h
    have s : i-1+2=i+1 := by
      apply (ZMod.finEquiv k).injective
      simp only [map_add,map_sub,map_one,finEquiv_two]
      ring
    rwa [sub_add_cancel,s] at h

theorem twice_zeroWords {k : ℕ} [NeZero k] :
    (2 : ℤ) * (zeroWords k).card = (lucas k : ℤ) + signedValue k := by
  obtain ⟨n,rfl⟩ : ∃ n, k=n+1 := ⟨k-1,by have := NeZero.pos k; omega⟩
  have plus := trace_count false n
  have minus := trace_count true n
  rw [unsigned_trace _ (by omega)] at plus
  rw [signed_trace _ (by omega)] at minus
  simp at plus minus
  have h : (2 : ℤ) * (zeroWords (n+1)).card =
      ∑ z ∈ independentWords (n+1), (1 + bitSign (parityQ z)) := by
    unfold zeroWords
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hz : parityQ z = 0 <;> simp [bitSign,hz] <;> norm_num
  rw [h,Finset.sum_add_distrib,← minus]
  have posPlus : ((independentWords (n+1)).card : ℤ) = (lucas (n+1) : ℤ) := by
    exact_mod_cast plus.symm
  simp [nsmul_eq_mul,posPlus]

end TraceValues

open Classical

section Fourier

variable {U V : Type} [AddCommGroup U] [Module F U] [Fintype U]
  [AddCommGroup V] [Module F V] [Fintype V]

theorem bitSign_le (b : F) : bitSign b ≤ 1 := by
  rcases bit_cases b with rfl | rfl <;> decide +kernel

theorem char_sum (L : V →ₗ[F] F) :
    (∑ x : V, bitSign (L x)) = if L = 0 then (Fintype.card V : ℤ) else 0 := by
  classical
  by_cases hz : L = 0
  · simp [hz,bitSign]
  · rw [if_neg hz]
    have exists_on : ∃ a : V, L a = 1 := by
      by_contra! missing
      apply hz
      ext a
      rcases bit_cases (L a) with h | h
      · exact h
      · exact (missing a h).elim
    obtain ⟨a,ha⟩ := exists_on
    have sign_one : bitSign 1 = -1 := by decide +kernel
    have translate := Equiv.sum_comp (Equiv.addRight a) (fun x : V => bitSign (L x))
    change (∑ x : V, bitSign (L (x+a))) = ∑ x : V, bitSign (L x) at translate
    simp only [map_add,bitSign_add,ha,sign_one,← Finset.sum_mul] at translate
    linarith

noncomputable def level (L : U →ₗ[F] V) (b : V) : Finset U := by
  classical
  exact Finset.univ.filter (fun x => L x = b)

omit [Fintype V] in
theorem level_card_le (L : U →ₗ[F] V) (b : V) : (level L b).card ≤ (level L 0).card := by
  classical
  by_cases h : ∃ a, L a = b
  · obtain ⟨a,ha⟩ := h
    let f (x : U) := x-a
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro x hx
      have hx' : L x = b := (Finset.mem_filter.mp hx).2
      simp [level,f,map_sub,hx',ha]
    · intro x _ y _ eq
      exact sub_left_injective eq
  · have empty : level L b = ∅ := by
      ext x
      simp [level,show L x ≠ b from fun equal => h ⟨x,equal⟩]
    simp [empty]

theorem bilinear_shift_bound (B : U →ₗ[F] (V →ₗ[F] F))
    (A : U →ₗ[F] F) (D : V →ₗ[F] F) (b : F) :
    (∑ u : U, ∑ v : V, bitSign (B u v + (A u + D v + b))) ≤
      ∑ u : U, ∑ v : V, bitSign (B u v) := by
  classical
  let N : ℤ := Fintype.card V
  have nonneg : 0 ≤ N := by positivity
  have inner (u : U) :
      (∑ v : V, bitSign (B u v + (A u + D v + b))) =
        if B u = -D then bitSign (A u+b) * N else 0 := by
    have split (v : V) :
        bitSign (B u v + (A u + D v + b)) =
          bitSign (A u+b) * bitSign ((B u + D) v) := by
      rw [← bitSign_add]
      congr 1
      simp only [LinearMap.add_apply]
      ring
    simp only [split,← Finset.mul_sum,char_sum]
    by_cases h : B u = -D
    · simp [h, N]
    · have no : B u + D ≠ 0 := fun equal => h (eq_neg_of_add_eq_zero_left equal)
      simp [h,no]
  have raw (u : U) : (∑ v : V, bitSign (B u v)) = if B u = 0 then N else 0 := char_sum (B u)
  have counted (c : V →ₗ[F] F) :
      (∑ u : U, if B u = c then N else 0) = ((level B c).card : ℤ)*N := by
    rw [← Finset.sum_filter]
    have same : (Finset.univ.filter fun u => B u=c) = level B c := by
      ext u
      simp [level]
    rw [same]
    simp [nsmul_eq_mul]
  calc
    _ = ∑ u : U, if B u = -D then bitSign (A u+b) * N else 0 := Finset.sum_congr rfl fun u _ => inner u
    _ ≤ ∑ u : U, if B u = -D then N else 0 := by
      refine Finset.sum_le_sum fun u _ => ?_
      split
      · simpa only [one_mul] using mul_le_mul_of_nonneg_right (bitSign_le (A u+b)) nonneg
      · rfl
    _ = ((level B (-D)).card : ℤ) * N := counted (-D)
    _ ≤ ((level B 0).card : ℤ) * N :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast level_card_le B (-D)) nonneg
    _ = _ := by rw [counted 0 |>.symm]; simp_rw [raw]

end Fourier

open Classical

section WordFourier

variable {k : ℕ} [NeZero k]

abbrev Out (k : ℕ) := Word k × F

def probe (w : Out k) : Out k →ₗ[F] F :=
  (∑ i : Fin k, w.1 i • point i).comp (LinearMap.fst _ _ _) +
    w.2 • (LinearMap.snd _ _ _)

theorem probe_apply (x y : Out k) :
    probe x y = (∑ i : Fin k, x.1 i * y.1 i) + x.2 * y.2 := by
  simp [probe,point_apply,smul_eq_mul]

theorem probe_comm (x y : Out k) : probe x y = probe y x := by
  simp only [probe_apply]
  simp only [mul_comm]

theorem probe_zero_iff (y : Out k) : probe y = 0 ↔ y = 0 := by
  constructor
  · intro hy
    have atLast := LinearMap.congr_fun hy (0,1)
    simp [probe_apply] at atLast
    have atEach (i : Fin k) : y.1 i = 0 := by
      let delta : Word k := fun j => if i = j then 1 else 0
      have h := LinearMap.congr_fun hy (delta,0)
      rw [probe_apply] at h
      change (∑ j : Fin k, y.1 j * delta j) + y.2*0 = 0 at h
      simpa [delta,mul_ite,Finset.sum_ite_eq] using h
    exact Prod.ext (funext atEach) atLast
  · rintro rfl
    apply LinearMap.ext
    intro x
    simp [probe_apply]

noncomputable def countZero (f : Word k → Out k) : ℕ :=
  (Finset.univ.filter (fun x => f x = 0)).card

theorem probe_count (f : Word k → Out k) :
    (Fintype.card (Out k) : ℤ) * (countZero f : ℤ) =
      ∑ u : Out k, ∑ x : Word k, bitSign (probe u (f x)) := by
  rw [Finset.sum_comm]
  simp_rw [probe_comm _ (f _),char_sum,probe_zero_iff]
  simp [countZero,← Finset.sum_filter,nsmul_eq_mul,mul_comm]

def evenPart : Word k →ₗ[F] Word k :=
  LinearMap.pi fun i => if i.val % 2 = 0 then point i else 0

def oddPart : Word k →ₗ[F] Word k :=
  LinearMap.pi fun i => if i.val % 2 = 0 then 0 else point i

def joined (u v : Word k) : Word k := evenPart u + oddPart v

theorem joined_apply (u v : Word k) (i : Fin k) :
    joined u v i = if i.val % 2 = 0 then u i else v i := by
  simp only [joined,Pi.add_apply,evenPart,oddPart,LinearMap.pi_apply]
  split <;> simp_all [point_apply]

theorem joined_roundtrip (u v : Word k) :
    joined (joined u v) (joined v u) = u := by
  funext i
  by_cases h : i.val % 2 = 0 <;> simp [joined_apply,h]

def joinedEquiv : (Word k × Word k) ≃ (Word k × Word k) where
  toFun p := (joined p.1 p.2,joined p.2 p.1)
  invFun p := (joined p.1 p.2,joined p.2 p.1)
  left_inv p := Prod.ext (joined_roundtrip p.1 p.2) (joined_roundtrip p.2 p.1)
  right_inv p := Prod.ext (joined_roundtrip p.1 p.2) (joined_roundtrip p.2 p.1)

theorem duplicate_sum (g : Word k → ℤ) :
    (∑ u : Word k, ∑ v : Word k, g (joined u v)) =
      (Fintype.card (Word k) : ℤ) * ∑ x : Word k, g x := by
  calc
    _ = ∑ p : Word k × Word k, g ((joinedEquiv p).1) :=
      (Fintype.sum_prod_type (fun p : Word k × Word k => g ((joinedEquiv p).1))).symm
    _ = ∑ p : Word k × Word k, g p.1 :=
      Equiv.sum_comp joinedEquiv (fun p : Word k × Word k => g p.1)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp [nsmul_eq_mul,← Finset.mul_sum]

theorem parity_offset (he : 2 ∣ k) (i : Fin k) (a : ℕ) :
    (i+(a : Fin k)).val % 2 = (i.val+a)%2 := by
  rw [fin_addNat_index]
  exact Nat.mod_mod_of_dvd _ he

theorem adjacent_opp (he : 2 ∣ k) (i : Fin k) :
    (i+1).val % 2 ≠ (i+2).val % 2 := by
  have h1 : (i+1).val % 2 = (i.val+1)%2 := parity_offset he i 1
  have h2 : (i+2).val % 2 = (i.val+2)%2 := parity_offset he i 2
  omega

theorem distant_opp (he : 2 ∣ k) (i : Fin k) :
    i.val % 2 ≠ (i+3).val % 2 := by
  have h3 : (i+3).val % 2 = (i.val+3)%2 := parity_offset he i 3
  omega

def orderedEdge (i j : Fin k) : Word k →ₗ[F] (Word k →ₗ[F] F) where
  toFun u := u i • point j
  map_add' u v := by simp [add_smul]
  map_smul' a u := by simp [mul_smul,smul_eq_mul]

def crossEdge (i j : Fin k) : Word k →ₗ[F] (Word k →ₗ[F] F) :=
  if i.val % 2 = 0 then orderedEdge i j else orderedEdge j i

theorem crossEdge_apply (u v : Word k) (i j : Fin k) (h : i.val % 2 ≠ j.val % 2) :
    crossEdge i j u v = joined u v i * joined u v j := by
  by_cases hi : i.val % 2 = 0
  · have hj : j.val % 2 ≠ 0 := by omega
    simp [crossEdge,orderedEdge,joined_apply,hi,hj,point_apply,smul_eq_mul]
  · have hj : j.val % 2 = 0 := by omega
    simp [crossEdge,orderedEdge,joined_apply,hi,hj,point_apply,smul_eq_mul,mul_comm]

def residualBilinear (probeWord : Out k) : Word k →ₗ[F] (Word k →ₗ[F] F) :=
  (∑ i : Fin k, probeWord.1 i • crossEdge (i+1) (i+2)) +
    probeWord.2 • ∑ i : Fin k, crossEdge i (i+3)

theorem residualBilinear_eq (he : 2 ∣ k) (w : Out k) (u v : Word k) :
    residualBilinear w u v = probe w (residual (joined u v)) := by
  simp only [residualBilinear,probe_apply,LinearMap.add_apply,LinearMap.sum_apply,
    LinearMap.smul_apply,smul_eq_mul,residual,rowQ,parityQ]
  simp_rw [crossEdge_apply _ _ _ _ (adjacent_opp he _),
    crossEdge_apply _ _ _ _ (distant_opp he _)]

theorem probe_shift_bound (he : 2 ∣ k) (D : Word k →ₗ[F] Out k) (b w : Out k) :
    (∑ x : Word k, bitSign (probe w (residual x + (D x + b)))) ≤
      ∑ x : Word k, bitSign (probe w (residual x)) := by
  let AL := ((probe w).comp D).comp evenPart
  let AR := ((probe w).comp D).comp oddPart
  have h := bilinear_shift_bound (residualBilinear w) AL AR (probe w b)
  have eq (u v : Word k) :
      residualBilinear w u v + (AL u + AR v + probe w b) =
        probe w (residual (joined u v) + (D (joined u v) + b)) := by
    rw [residualBilinear_eq he]
    simp [AL,AR,joined,map_add,add_assoc]
  simp_rw [eq,residualBilinear_eq he] at h
  let f (x : Word k) := bitSign (probe w (residual x + (D x+b)))
  let g (x : Word k) := bitSign (probe w (residual x))
  change (∑ u : Word k, ∑ v : Word k, f (joined u v)) ≤
    ∑ u : Word k, ∑ v : Word k, g (joined u v) at h
  rw [duplicate_sum f,duplicate_sum g] at h
  apply le_of_mul_le_mul_left h
  exact_mod_cast (Fintype.card_pos (α := Word k))

theorem full_affine_bound (he : 2 ∣ k) (D : Word k →ₗ[F] Out k) (b : Out k) :
    countZero (fun x => residual x - (D x + b)) ≤ (zeroWords k).card := by
  have h := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset (Out k))) =>
    probe_shift_bound he (-D) (-b) w)
  have diff (x : Word k) :
      residual x + ((-D) x + (-b)) = residual x - (D x+b) := by
    simp only [LinearMap.neg_apply, neg_add, sub_eq_add_neg]
  simp_rw [diff] at h
  rw [← probe_count,← probe_count] at h
  have hpos : (0 : ℤ) < (Fintype.card (Out k) : ℤ) := by
    exact_mod_cast (Fintype.card_pos (α := Out k))
  have h' := le_of_mul_le_mul_left h hpos
  rw [zeroWords_solution]
  change _ ≤ countZero residual
  exact_mod_cast h'

end WordFourier

open Classical

section AffineReduction

variable {k : ℕ} [NeZero k]

def rowName (name : Bool → Word k) : Word k := mixer 1 (name false)

def colName (name : Bool → Word k) : Word k := mixer 2 (name true)

def linearPart (name : Bool → Word k) : Word k →ₗ[F] Out k :=
  (LinearMap.pi fun i => affineAt coord (rowName name) 0 i).prod
    (∑ i : Fin k, affineAt column (colName name) 4 i)

def constantPart (name c : Bool → Word k) : Out k :=
  (fun i => constAt (rowName name) (c false) i,
    ∑ i : Fin k, constAt (colName name) (c true) i)

def output (name c : Bool → Word k) (x : Word k) : Out k :=
  (runAt coord (rowName name) (c false) 0 x,
    ∑ i : Fin k, runAt column (colName name) (c true) 4 x i)

theorem output_decomposition (name c : Bool → Word k) (x : Word k) :
    output name c x = (linearPart name x + constantPart name c) + residual (coord x) := by
  apply Prod.ext
  · funext i
    exact runAt_eq coord (rowName name) (c false) 0 x i
  · change (∑ i : Fin k, runAt column (colName name) (c true) 4 x i) =
      ((∑ i : Fin k, affineAt column (colName name) 4 i) x +
        ∑ i : Fin k, constAt (colName name) (c true) i) + parityQ (coord x)
    simp only [LinearMap.sum_apply,runAt_eq,Finset.sum_add_distrib,column_sum]

def rowAdjustment (u : Word k) : Word k →ₗ[F] Word k :=
  LinearMap.pi fun i => u (i+1) • point (i+2) + u (i+2) • point (i+1)

def scalarAdjustment (u : Word k) : Word k →ₗ[F] F :=
  ∑ i : Fin k, (u i • point (i+3) + u (i+3) • point i)

def adjustment (u : Word k) : Word k →ₗ[F] Out k :=
  (rowAdjustment u).prod (scalarAdjustment u)

theorem residual_translate (z u : Word k) :
    residual (z+u) = (residual z + adjustment u z) + residual u := by
  apply Prod.ext
  · funext i
    simp [residual,rowQ,adjustment,rowAdjustment,point_apply,smul_eq_mul]
    ring
  · change parityQ (z+u) = (parityQ z + scalarAdjustment u z) + parityQ u
    simp only [parityQ,scalarAdjustment,LinearMap.sum_apply,LinearMap.add_apply,
      LinearMap.smul_apply,point_apply,Pi.add_apply,smul_eq_mul,← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

noncomputable def hits (f : Word k → Out k) (D : Word k →ₗ[F] Out k) (b : Out k) : ℕ :=
  (Finset.univ.filter (fun x => f x = D x+b)).card

theorem hits_count (f : Word k → Out k) (D : Word k →ₗ[F] Out k) (b : Out k) :
    hits f D b = countZero (fun x => f x-(D x+b)) := by
  unfold hits countZero
  congr 1
  ext x
  simp [sub_eq_zero]

theorem shift_average (L : Word k →ₗ[F] Word k) :
    ∃ u : Word k, (zeroWords k).card ≤ countZero (fun x => residual (L x+u)) := by
  let N := (zeroWords k).card
  have totals :
      (∑ u : Word k, countZero (fun x => residual (L x + u))) = ∑ _ : Word k, N := by
    simp only [countZero,Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    have eq := Equiv.sum_comp (Equiv.addLeft (L x))
      (fun z : Word k => if residual z=0 then (1:ℕ) else 0)
    change (∑ u : Word k, if residual (L x+u)=0 then (1:ℕ) else 0) =
      (∑ z : Word k, if residual z=0 then (1:ℕ) else 0) at eq
    rw [eq]
    dsimp [N]
    rw [zeroWords_solution,Finset.card_filter]
  by_contra! h
  have lt : (∑ u : Word k, countZero (fun x => residual (L x+u))) < ∑ _ : Word k, N :=
    Finset.sum_lt_sum (fun x _ => (h x).le) ⟨0,Finset.mem_univ _,h 0⟩
  exact (lt_irrefl _) (totals ▸ lt)

theorem coordinate_section (L : Word k →ₗ[F] Word k) :
    ∃ P : Word k →ₗ[F] Word k, ∀ x, L (P (L x)) = L x := by
  obtain ⟨s,hs⟩ := L.rangeRestrict.exists_rightInverse_of_surjective L.range_rangeRestrict
  obtain ⟨t,ht⟩ := L.range.subtype.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  refine ⟨s.comp t,?_⟩
  intro x
  have h1 := LinearMap.congr_fun ht (L.rangeRestrict x)
  have h2 := LinearMap.congr_fun hs (L.rangeRestrict x)
  change t (L x) = L.rangeRestrict x at h1
  change L.rangeRestrict (s (L.rangeRestrict x)) = L.rangeRestrict x at h2
  change L (s (t (L x))) = L x
  rw [h1]
  exact congrArg Subtype.val h2

theorem restricted_affine_bound (even : 2 ∣ k) (L : Word k →ₗ[F] Word k)
    [Fintype L.ker] (D : Word k →ₗ[F] Out k) (b : Out k) :
    countZero (fun x => residual (L x)-(D x+b)) ≤
      Fintype.card L.ker * (zeroWords k).card := by
  obtain ⟨P,hP⟩ := coordinate_section L
  let key : Word k → L.ker := fun x => ⟨x-P (L x), LinearMap.mem_ker.mpr (by rw [map_sub,hP,sub_self])⟩
  have split (x : Word k) : x = P (L x) + (key x).val := by
    change x = P (L x)+(x-P (L x))
    abel
  let S := Finset.univ.filter (fun x : Word k => residual (L x) - (D x+b) = 0)
  change S.card ≤ _
  have partition : (∑ u : L.ker, (S.filter (fun x => key x = u)).card) = S.card := by
    simpa using Finset.sum_card_fiberwise_eq_card_filter S (Finset.univ : Finset L.ker) key
  rw [← partition]
  have each (u : L.ker) : (S.filter (fun x => key x = u)).card ≤ (zeroWords k).card := by
    let T := countZero (fun y => residual y - ((D.comp P) y + (D u.val+b)))
    refine le_trans ?_ (full_affine_bound even (D.comp P) (D u.val+b))
    change _ ≤ T
    unfold T countZero
    refine Finset.card_le_card_of_injOn L ?_ ?_
    · intro x hx
      obtain ⟨hS,hK⟩ := Finset.mem_filter.mp hx
      have hS' : residual (L x) - (D x+b) = 0 := (Finset.mem_filter.mp hS).2
      have expand : D x+b = D (P (L x)) + (D u.val+b) := by
        conv_lhs => arg 1; rw [split x, map_add, hK]
        abel
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [expand] using hS'⟩
    · intro x hx y hy h
      have hx' : key x = u := (Finset.mem_filter.mp hx).2
      have hy' : key y = u := (Finset.mem_filter.mp hy).2
      calc
        x = P (L x)+(key x).val := split x
        _ = P (L y)+(key y).val := by rw [h,hx',hy']
        _ = y := (split y).symm
  calc
    _ ≤ ∑ _ : L.ker, (zeroWords k).card := Finset.sum_le_sum fun u _ => each u
    _ = _ := by simp

theorem regular_count (hreg : ¬ 3 ∣ k) :
    countZero (fun x : Word k => residual (coord x)) = (zeroWords k).card := by
  let e : Word k ≃ Word k := Equiv.ofBijective coord ⟨coord_injective hreg,coord_surjective hreg⟩
  simp only [countZero,zeroWords_solution,Finset.card_filter]
  exact Equiv.sum_comp e (fun z => if residual z = 0 then (1:ℕ) else 0)

end AffineReduction

section Mask

variable {k : ℕ} [NeZero k]

def oneSide (p : Fin 2) (x : Word k) : Prop :=
  ∀ i : Fin k, i.val % 2 ≠ p.val → coord x i = 0

def weighted (name c : Bool → Word k) (mask x : Word k) : F :=
  ∑ i : Fin k, mask i * runAt column (colName name) (c true) 4 x i

def polar (f : Word k → F) (u v : Word k) : F :=
  f 0 + f u + f v + f (u+v)

theorem run_polar (L : Word k →ₗ[F] Word k) (t c : Word k) (turn : Fin k)
    (u v : Word k) (i : Fin k) :
    polar (fun x => runAt L t c turn x i) u v =
      L u (i+1)*L v (i+2) + L v (i+1)*L u (i+2) := by
  simp only [polar,runAt_eq,rowQ,map_zero,map_add,Pi.add_apply,Pi.zero_apply,zero_mul,add_zero,
    zero_add]
  linear_combination bit_add_self (affineAt L t turn i u) +
    bit_add_self (affineAt L t turn i v) + 2*bit_add_self (constAt t c i) +
    bit_add_self (L u (i+1)*L u (i+2)) + bit_add_self (L v (i+1)*L v (i+2))

theorem weighted_polar (name c : Bool → Word k) (mask u v : Word k) :
    polar (weighted name c mask) u v = ∑ i : Fin k,
      mask i * (column u (i+1)*column v (i+2) + column v (i+1)*column u (i+2)) := by
  simp only [polar,weighted,← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_add,← mul_add,← mul_add]
  exact congrArg (fun q : F => mask i*q) (run_polar column (colName name) (c true) 4 u v i)

def colA (z : Word k) (i : Fin k) : F := z (i-2)+z (i-1)+z i

def colB (z : Word k) (i : Fin k) : F := z (i-1)+z i+z (i+1)

theorem colA_coord (x : Word k) (i : Fin k) : column x (i+1) = colA (coord x) i := by
  rw [column_of_coord,colA]
  have a : i+1-3=i-2 := by apply (ZMod.finEquiv k).injective; simp [finEquiv_two,finEquiv_three] <;> ring
  have b : i+1-2=i-1 := by apply (ZMod.finEquiv k).injective; simp [finEquiv_two] <;> ring
  rw [a,b,add_sub_cancel_right]

theorem colB_coord (x : Word k) (i : Fin k) : column x (i+2) = colB (coord x) i := by
  rw [column_of_coord,colB]
  have a : i+2-3=i-1 := by apply (ZMod.finEquiv k).injective; simp [finEquiv_two,finEquiv_three] <;> ring
  have b : i+2-1=i+1 := by apply (ZMod.finEquiv k).injective; simp [finEquiv_two] <;> ring
  rw [a,b,add_sub_cancel_right]

def delta (j : Fin k) : Word k := fun i => if i = j then 1 else 0

def relative (t : Fin k) (a : Fin 6) : Word k := delta (t+(a.val : Fin k))

theorem delta_sub (t i b : Fin k) : delta t (i-b) = delta (t+b) i := by
  simp [delta,sub_eq_iff_eq_add]

theorem delta_add (t i b : Fin k) : delta (t+b) (i+b) = delta t i := by
  simp [delta]

theorem cast_shift_add (t : Fin k) (a b : ℕ) :
    t+(a:Fin k)+(b:Fin k) = t+((a+b:ℕ):Fin k) := by
  rw [Nat.cast_add,add_assoc]

theorem relative_trans (t : Fin k) (i : Fin k) :
    colA (relative t 1) i = relative t 3 i + relative t 2 i + relative t 1 i ∧
    colB (relative t 1) i = relative t 2 i + relative t 1 i + relative t 0 i ∧
    colA (relative t 3) i = relative t 5 i + relative t 4 i + relative t 3 i ∧
    colB (relative t 3) i = relative t 4 i + relative t 3 i + relative t 2 i := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change delta (t+1) (i-2)+delta (t+1) (i-1)+delta (t+1) i =
      delta (t+3) i+delta (t+2) i+delta (t+1) i
    rw [delta_sub,delta_sub,show t+1+2=t+3 from cast_shift_add t 1 2,
      show t+1+1=t+2 from cast_shift_add t 1 1]
  · change delta (t+1) (i-1)+delta (t+1) i+delta (t+1) (i+1) =
      delta (t+2) i+delta (t+1) i+delta (t+(0:Fin k)) i
    rw [add_zero,delta_sub,show t+1+1=t+2 from cast_shift_add t 1 1,delta_add]
  · change delta (t+3) (i-2)+delta (t+3) (i-1)+delta (t+3) i =
      delta (t+5) i+delta (t+4) i+delta (t+3) i
    rw [delta_sub,delta_sub,show t+3+2=t+5 from cast_shift_add t 3 2,
      show t+3+1=t+4 from cast_shift_add t 3 1]
  · change delta (t+3) (i-1)+delta (t+3) i+delta (t+3) (i+1) =
      delta (t+4) i+delta (t+3) i+delta (t+2) i
    have h : delta (t+3) (i+1) = delta (t+2) i := by
      rw [show t+3=t+2+1 from (cast_shift_add t 2 1).symm,delta_add]
    rw [delta_sub,show t+3+1=t+4 from cast_shift_add t 3 1,h]

theorem relative_injective (wide : 8 ≤ k) (t : Fin k) :
    Function.Injective (fun a : Fin 6 => t+(a.val : Fin k)) := by
  intro a b h
  have eq := congrArg (fun i : Fin k => i.val) (add_left_cancel h)
  change a.val % k = b.val % k at eq
  rw [Nat.mod_eq_of_lt (by omega : a.val < k),Nat.mod_eq_of_lt (by omega : b.val < k)] at eq
  exact Fin.ext eq

theorem relative_mul (wide : 8 ≤ k) (t i : Fin k) (a b : Fin 6) :
    relative t a i * relative t b i = if a=b then relative t a i else 0 := by
  by_cases eq : a=b
  · subst b
    simp [bit_square]
  · have neq := fun h => eq (relative_injective wide t h)
    by_cases ha : i = t+(a.val : Fin k)
    · have hb : i ≠ t+(b.val : Fin k) := fun hb => neq (ha.symm.trans hb)
      unfold relative delta
      rw [ite_eq_left ha,ite_eq_right hb,ite_eq_right eq,mul_zero]
    · simp [eq,relative,delta,ha]

theorem distance_two_coefficient (wide : 8 ≤ k) (t i : Fin k) :
    colA (relative t 1) i * colB (relative t 3) i +
      colA (relative t 3) i * colB (relative t 1) i = relative t 2 i + relative t 3 i := by
  obtain ⟨A1,B1,A3,B3⟩ := relative_trans t i
  rw [A1,B1,A3,B3]
  simp only [add_mul,mul_add,relative_mul wide]
  norm_num
  ring

theorem sum_delta (mask : Word k) (i : Fin k) :
    (∑ j : Fin k, mask j * delta i j) = mask i := by
  simp [delta,mul_ite]

theorem extract_mask (wide : 8 ≤ k) (even : 2 ∣ k) (regular : ¬ 3 ∣ k)
    (name c : Bool → Word k) (mask : Word k)
    (flat : ∀ (p : Fin 2) (u v : Word k), oneSide p u → oneSide p v →
      polar (weighted name c mask) u v = 0) : ∀ i j, mask i = mask j := by
  have offsets (t : Fin k) : mask (t+2) = mask (t+3) := by
    obtain ⟨u,hu⟩ := coord_surjective regular (relative t 1)
    obtain ⟨v,hv⟩ := coord_surjective regular (relative t 3)
    let p : Fin 2 := ⟨(t+1).val % 2,Nat.mod_lt _ (by decide)⟩
    have same : (t+3).val % 2 = p.val := by
      change (t+3).val % 2 = (t+1).val % 2
      rw [show (t+3).val % 2=(t.val+3)%2 from parity_offset even t 3,
        show (t+1).val % 2=(t.val+1)%2 from parity_offset even t 1]
      omega
    have hup : oneSide p u := by
      intro j h
      rw [hu]
      have ne : j ≠ t+1 := fun eqq => h (by rw [eqq])
      exact if_neg ne
    have hvp : oneSide p v := by
      intro j h
      rw [hv]
      have ne : j ≠ t+3 := fun eqq => h (eqq ▸ same)
      exact if_neg ne
    have zero := flat p u v hup hvp
    rw [weighted_polar] at zero
    simp_rw [colA_coord,colB_coord,hu,hv,distance_two_coefficient wide,mul_add,Finset.sum_add_distrib] at zero
    change (∑ i : Fin k, mask i * delta (t+2) i) +
      (∑ i : Fin k, mask i * delta (t+3) i) = 0 at zero
    rw [sum_delta,sum_delta] at zero
    exact (eq_neg_of_add_eq_zero_left zero).trans (bit_neg _)
  have adjacent (i : Fin k) : mask i = mask (i+1) := by
    have h := offsets (i-2)
    rw [sub_add_cancel] at h
    have ix : i-2+3=i+1 := by
      apply (ZMod.finEquiv k).injective
      simp [finEquiv_two,finEquiv_three] <;> ring
    rwa [ix] at h
  have all (n : ℕ) : mask (n : Fin k) = mask 0 := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Nat.cast_succ,← adjacent]
      exact ih
  intro i j
  have castId (x : Fin k) : (x.val : Fin k) = x := Fin.ext (Nat.mod_eq_of_lt x.isLt)
  simpa only [castId] using (all i.val).trans (all j.val).symm

theorem parityQ_oneSide (even : 2 ∣ k) (p : Fin 2) (x : Word k)
    (h : oneSide p x) : parityQ (coord x) = 0 := by
  unfold parityQ
  refine Finset.sum_eq_zero fun i _ => ?_
  have opp := distant_opp even i
  by_cases same : i.val % 2 = p.val
  · have other : (i+3).val % 2 ≠ p.val := fun e => opp (same.trans e.symm)
    rw [h (i+3) other,mul_zero]
  · rw [h i same,zero_mul]

theorem constant_mask_flat (even : 2 ∣ k) (name c : Bool → Word k) (mask : Word k)
    (constant : ∀ i j, mask i = mask j)
    (p : Fin 2) (u v : Word k) (hu : oneSide p u) (hv : oneSide p v) :
    polar (weighted name c mask) u v = 0 := by
  have h0 : oneSide p (0 : Word k) := by intro i _; rw [map_zero]; rfl
  have huv : oneSide p (u+v) := by
    intro i hi
    rw [map_add]
    change coord u i+coord v i=0
    rw [hu i hi,hv i hi,add_zero]
  let L := (LinearMap.snd F (Word k) F).comp (linearPart name)
  let b := (constantPart name c).2
  have onlyAffine (x : Word k) (hx : oneSide p x) :
      weighted name c mask x = mask 0 * (L x+b) := by
    have eq : weighted name c mask x = mask 0 * (output name c x).2 := by
      change _ = mask 0 * (∑ i : Fin k, runAt column (colName name) (c true) 4 x i)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [constant i 0]
    rw [eq,output_decomposition]
    change mask 0 * (L x+b+parityQ (coord x)) = _
    rw [parityQ_oneSide even p x hx,add_zero]
  unfold polar
  rw [onlyAffine 0 h0,onlyAffine u hu,onlyAffine v hv,onlyAffine (u+v) huv]
  rw [map_zero,map_add,zero_add]
  linear_combination mask 0 * (2*bit_add_self b + bit_add_self (L u) + bit_add_self (L v))

end Mask

section Result

variable {k : ℕ} [NeZero k]

def twiceFormula (k : ℕ) : ℕ :=
  if 3 ∣ k then (if 2 ∣ k then lucas k+2^(1+k/2)+2 else lucas k-2)
  else lucas k+(if 2 ∣ k then 2^(1+k/2)-1 else 1)

theorem zeroWords_formula : 2 * (zeroWords k).card = twiceFormula k := by
  let J : ℕ := 2^(1+k/2)
  have hp : 0 < J := by dsimp [J]; positivity
  have Jint : (2:ℤ)^(1+k/2) = (J:ℤ) := by
    dsimp [J]
  have h := twice_zeroWords (k := k)
  by_cases h3 : 3 ∣ k <;> by_cases h2 : 2 ∣ k
  all_goals
    simp only [twiceFormula,h3,h2,ite_true,ite_false]
    simp only [signedValue,grows,periodic,h3,h2,ite_true,ite_false,zero_add,Jint] at h
  · change 2*(zeroWords k).card = lucas k+J+2
    omega
  · omega
  · change 2*(zeroWords k).card = lucas k+(J-1)
    omega
  · omega

theorem subtraction_residual (name c : Bool → Word k) (x : Word k) :
    output name c x - (linearPart name x + constantPart name c) = residual (coord x) := by
  rw [output_decomposition]
  abel

theorem exact_and_lower (name c : Bool → Word k) :
    (∃ (A : Word k →ₗ[F] Out k) (b : Out k),
      (∀ x, output name c x - (A x+b) = residual (coord x)) ∧
      (¬ 3 ∣ k → 2*hits (output name c) A b = twiceFormula k)) ∧
    (∃ (C : Word k →ₗ[F] Out k) (d : Out k), twiceFormula k ≤ 2*hits (output name c) C d) := by
  constructor
  · refine ⟨linearPart name,constantPart name c,subtraction_residual name c,?_⟩
    intro regular
    rw [hits_count]
    simp_rw [subtraction_residual,regular_count regular,zeroWords_formula]
  · obtain ⟨u,hu⟩ := shift_average (coord (k := k))
    refine ⟨linearPart name - (adjustment u).comp coord,
      constantPart name c - residual u, ?_⟩
    have shifted (x : Word k) : output name c x -
        ((linearPart name - (adjustment u).comp coord) x + (constantPart name c-residual u)) =
          residual (coord x+u) := by
      rw [output_decomposition,residual_translate]
      simp only [LinearMap.sub_apply,LinearMap.comp_apply]
      abel
    rw [hits_count]
    simp_rw [shifted]
    rw [← zeroWords_formula]
    exact Nat.mul_le_mul_left 2 hu

theorem upper_count (he : 2 ∣ k) (name c : Bool → Word k)
    (D : Word k →ₗ[F] Out k) (b : Out k) :
    2*hits (output name c) D b ≤ (if 3 ∣ k then 4 else 1)*twiceFormula k := by
  classical
  let K := LinearMap.ker (coord (k := k))
  let : Fintype K := Fintype.ofFinite _
  have expanded (x : Word k) : output name c x-(D x+b) =
      residual (coord x)-((D-linearPart name) x+(b-constantPart name c)) := by
    rw [output_decomposition]
    simp only [LinearMap.sub_apply]
    abel
  rw [hits_count]
  simp_rw [expanded]
  have upper := restricted_affine_bound he coord (D-linearPart name) (b-constantPart name c)
  have card : Fintype.card K ≤ if 3 ∣ k then 4 else 1 := by
    by_cases h : 3 ∣ k
    · rw [ite_eq_left h]
      exact coord_kernel_card (k := k)
    · rw [ite_eq_right h]
      apply Fintype.card_le_one_iff_subsingleton.mpr
      constructor
      intro x y
      apply Subtype.ext
      have hx := coord_kernel_regular h x.val (LinearMap.mem_ker.mp x.property)
      have hy := coord_kernel_regular h y.val (LinearMap.mem_ker.mp y.property)
      exact hx.trans hy.symm
  calc
    _ ≤ 2*(Fintype.card K*(zeroWords k).card) := Nat.mul_le_mul_left 2 upper
    _ = Fintype.card K * (2*(zeroWords k).card) := by ring
    _ ≤ _ := by rw [zeroWords_formula]; exact Nat.mul_le_mul_right _ card

end Result

section PostedDefinitions

variable {k : ℕ}

def idx (hk : 0 < k) (n : ℕ) : Fin k := ⟨n % k,Nat.mod_lt _ hk⟩

def givenRot (hk : 0 < k) (a : ℕ) (v : Word k) (i : Fin k) : F :=
  v (idx hk (i.val+k-a % k))

def givenMix (hk : 0 < k) (col : Bool) (v : Word k) (i : Fin k) : F :=
  let g := if col then 2 else 1
  v i + v (idx hk (i.val+g)) + v (idx hk (i.val+k-g % k))

def givenCoord (hk : 0 < k) (x : Word k) : Word k := givenMix hk false (givenRot hk 1 x)

def givenRun (hk : 0 < k) (name c : Bool → Word k) (col : Bool) (x : Word k) (i : Fin k) : F :=
  let y := givenMix hk col (givenRot hk (if col then 3 else 1) x + name col)
  y i + (1+y (idx hk (i.val+1)))*y (idx hk (i.val+2)) +
    givenRot hk (if col then 4 else 0) x i + c col i

def givenOutput (hk : 0 < k) (name c : Bool → Word k) (x : Word k) : Out k :=
  (givenRun hk name c false x,∑ i : Fin k, givenRun hk name c true x i)

def givenResidual (hk : 0 < k) (x : Word k) : Out k :=
  let z := givenCoord hk x
  ((fun i => z (idx hk (i.val+1))*z (idx hk (i.val+2))),
    ∑ i : Fin k, z i * z (idx hk (i.val+3)))

variable [NeZero k]

theorem idx_add (hk : 0 < k) (i : Fin k) (a : ℕ) :
    idx hk (i.val+a) = i+(a:Fin k) := Fin.ext (fin_addNat_index i a).symm

theorem idx_sub (hk : 0 < k) (i : Fin k) (a : ℕ) :
    idx hk (i.val+k-a % k) = i-(a:Fin k) := Fin.ext (fin_subNat_index i a).symm

theorem givenRot_eq (hk : 0 < k) (a : ℕ) (x : Word k) :
    givenRot hk a x = shift (a : Fin k) x := by
  funext i
  rw [givenRot,idx_sub,shift_apply]

theorem givenMix_eq (hk : 0 < k) (col : Bool) (x : Word k) :
    givenMix hk col x = mixer ((if col then 2 else 1 : ℕ) : Fin k) x := by
  funext i
  simp only [givenMix,idx_add,idx_sub,mixer_apply]

theorem givenCoord_eq (hk : 0 < k) (x : Word k) :
    givenCoord hk x = coord x := by
  rw [givenCoord,givenMix_eq,givenRot_eq]
  rfl

theorem givenRun_row (hk : 0 < k) (name c : Bool → Word k) (x : Word k) :
    givenRun hk name c false x = runAt coord (rowName name) (c false) 0 x := by
  funext i
  simp only [givenRun,idx_add,givenMix_eq,givenRot_eq]
  rw [map_add]
  rfl

theorem givenRun_col (hk : 0 < k) (name c : Bool → Word k) (x : Word k) :
    givenRun hk name c true x = runAt column (colName name) (c true) 4 x := by
  funext i
  simp only [givenRun,idx_add,givenMix_eq,givenRot_eq]
  rw [map_add]
  rfl

theorem givenOutput_eq (hk : 0 < k) (name c : Bool → Word k) :
    givenOutput hk name c = output name c := by
  funext x
  simp only [givenOutput,givenRun_row,givenRun_col,output]

theorem givenResidual_eq (hk : 0 < k) (x : Word k) :
    givenResidual hk x = residual (coord x) := by
  simp only [givenResidual,givenCoord_eq,idx_add]
  rfl


end PostedDefinitions

theorem clean_statement {k : ℕ} (hk : 0 < k) (name c : Bool → Word k) :
    let f := givenOutput hk name c
    (∃ (A : Word k →ₗ[F] Out k) (b : Out k),
      (∀ x, f x - (A x+b) = givenResidual hk x) ∧
      (¬ 3 ∣ k → 2*hits f A b = twiceFormula k)) ∧
    (∃ (C : Word k →ₗ[F] Out k) (d : Out k), twiceFormula k ≤ 2*hits f C d) ∧
    (2 ∣ k → ∀ (D : Word k →ₗ[F] Out k) (e : Out k),
      2*hits f D e ≤ (if 3 ∣ k then 4 else 1)*twiceFormula k) ∧
    (¬ 3 ∣ k → 8 ≤ k → 2 ∣ k → ∀ mask : Word k,
      let g := fun x => dotProduct mask (givenRun hk name c true x)
      let side := fun (p : Fin 2) (v : Word k) =>
        ∀ j : Fin k, j.val % 2 ≠ p.val → givenCoord hk v j = 0
      ((∀ (p : Fin 2) (u v : Word k), side p u → side p v →
        g 0 + g u + g v + g (u+v) = 0) ↔ ∀ i j : Fin k, mask i = mask j)) := by
  let : NeZero k := ⟨Nat.ne_of_gt hk⟩
  dsimp only
  simp only [givenOutput_eq, givenResidual_eq, givenCoord_eq]
  obtain ⟨exactProof,lowerProof⟩ := exact_and_lower name c
  refine ⟨exactProof,lowerProof,fun even => upper_count even name c,?_⟩
  intro regular wide even mask
  simp only [givenRun_col]
  change ((∀ (p : Fin 2) (u v : Word k), oneSide p u → oneSide p v →
    polar (weighted name c mask) u v = 0) ↔ ∀ i j, mask i = mask j)
  exact ⟨extract_mask wide even regular name c mask,constant_mask_flat even name c mask⟩

end PEqualNP.Outside.L_meta_32023

theorem PEqualNP.Outside.L_meta_32023 :
  ∀ (k : Nat) (hk : 0 < k),
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun n : Nat => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (n : Nat) (v : W) (j : Fin k) => v (ix (j.val+k-n % k))
  let mix := fun (col : Bool) (v : W) (j : Fin k) =>
    let g := if col then 2 else 1
    v j + v (ix (j.val+g)) + v (ix (j.val+k-g % k))
  let coord := fun x : W => mix false (rot 1 x)
  ∀ name c : Bool → W,
    let run := fun (col : Bool) (raw : W) (site : Fin k) =>
      let y := mix col (rot (if col then 3 else 1) raw + name col)
      y site + (1+y (ix (site.val+1)))*y (ix (site.val+2)) +
        rot (if col then 4 else 0) raw site + c col site
    let output := fun w : W => (run false w, ∑ i : Fin k, run true w i)
    let residual := fun word : W =>
      let z := coord word
      ((fun a : Fin k => z (ix (a.val+1))*z (ix (a.val+2))),
        ∑ u : Fin k, z u * z (ix (u.val+3)))
    let hits := fun (A : W →ₗ[F] (W × F)) (b : W × F) =>
      ((Finset.univ : Finset W).filter (fun key => output key = A key + b)).card
    let luc := Nat.fib (k-1) + Nat.fib (k+1)
    let twice := if 3 ∣ k then (if 2 ∣ k then luc + 2^(1+k/2) + 2 else luc-2)
      else luc + (if 2 ∣ k then 2^(1+k/2)-1 else 1)
    (∃ (A : W →ₗ[F] (W × F)) (b : W × F),
      (∀ x : W, output x - (A x+b) = residual x) ∧
      (¬ 3 ∣ k → 2 * hits A b = twice)) ∧
    (∃ (C : W →ₗ[F] (W × F)) (d : W × F), twice ≤ 2 * hits C d) ∧
    (2 ∣ k → ∀ (D : W →ₗ[F] (W × F)) (e : W × F),
      2 * hits D e ≤ (if 3 ∣ k then 4 else 1) * twice) ∧
    (¬ 3 ∣ k → 8 ≤ k → 2 ∣ k → ∀ mask : W,
      let readout := fun input : W => dotProduct mask (run true input)
      let oneSide := fun (p : Fin 2) (v : W) =>
        ∀ j : Fin k, j.val % 2 ≠ p.val → coord v j = 0
      ((∀ (par : Fin 2) (u v : W), oneSide par u → oneSide par v →
        readout 0 + readout u + readout v + readout (u+v) = 0) ↔
        ∀ i j : Fin k, mask i = mask j)) := by
  intro k hk
  dsimp only
  intro name c
  exact PEqualNP.Outside.L_meta_32023.clean_statement hk name c
