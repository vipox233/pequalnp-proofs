import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Lattice

namespace PEqualNP.Outside.L_pcx_424_aux

theorem splitSum {α : Type*} (s : Finset α) (e : α → ℕ) (b : ℕ) :
    (∑ x ∈ s, b ^ e x) = (s.filter (fun x => e x = 0)).card +
      b * ∑ x ∈ s.filter (fun x => 0 < e x), b ^ (e x - 1) := by
  classical
  rw [Finset.card_eq_sum_ones, Finset.mul_sum, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  cases h : e x with
  | zero => simp [h]
  | succ t => simp [h, pow_succ, Nat.mul_comm]

theorem histogramDigit {α : Type*} (s : Finset α) (e : α → ℕ) (b k : ℕ)
    (h : s.card < b) :
    ((∑ x ∈ s, b ^ e x) / b ^ k) % b = (s.filter (fun x => e x = k)).card := by
  classical
  induction k generalizing s e with
  | zero =>
    rw [pow_zero, Nat.div_one, splitSum, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (lt_of_le_of_lt (Finset.card_filter_le _ _) h)]
  | succ k ih =>
    have hb : 0 < b := by omega
    have small : (s.filter (fun x => e x = 0)).card < b :=
      lt_of_le_of_lt (Finset.card_filter_le _ _) h
    have shrink : (∑ x ∈ s, b ^ e x) / b =
        ∑ x ∈ s.filter (fun x => 0 < e x), b ^ (e x - 1) := by
      rw [splitSum, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt small, Nat.zero_add]
    rw [pow_succ', ← Nat.div_div_eq_div_mul, shrink,
      ih _ _ (lt_of_le_of_lt (Finset.card_filter_le _ _) h)]
    apply congrArg Finset.card
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hx,hp⟩, hk⟩
      exact ⟨hx,by omega⟩
    · rintro ⟨hx,hk⟩
      exact ⟨⟨hx,by omega⟩,by omega⟩

theorem code_eq {d a b c A B C : ℕ}
    (ha : a < d) (hb : b < d) (hA : A < d) (hB : B < d) :
    a + d*b + d^2*c = A + d*B + d^2*C ↔ a = A ∧ b = B ∧ c = C := by
  constructor
  · intro he
    have hd : 0 < d := by omega
    have h : a+d*(b+d*c) = A+d*(B+d*C) := by
      simpa only [pow_two, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc] using he
    have lo := congrArg (fun z : ℕ => z % d) h
    have hi := congrArg (fun z : ℕ => z / d) h
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hA] at lo
    simp only [Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hA, Nat.zero_add] at hi
    have mid := congrArg (fun z : ℕ => z % d) hi
    have top := congrArg (fun z : ℕ => z / d) hi
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hB] at mid
    simp only [Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hb, Nat.div_eq_of_lt hB, Nat.zero_add] at top
    exact ⟨lo, mid, top⟩
  · rintro ⟨rfl,rfl,rfl⟩
    rfl

theorem postedHistogram : ∀ (n : ℕ) (σ τ : Equiv.Perm (Fin n)),
  let V := Bool × Fin n
  let X := V → Bool
  let Mask := Fin n → Bool × Bool
  let base := 2^(2*n)+1
  let idx := fun (a b c : ℕ) => a + (n+1)*b + (n+1)^2*c
  let red := fun (y : X) =>
    (Finset.univ.filter (fun i : Fin n => y (false,i) ≠ y (true,i))).card
  let blue := fun (y : X) =>
    (Finset.univ.filter (fun i : Fin n => y (false,i) ≠ y (true,σ i))).card
  let third := fun (y : X) =>
    (Finset.univ.filter (fun i : Fin n => y (false,i) = y (true,τ i))).card
  let good := fun (p : Mask) => (Finset.univ : Finset X).filter (fun y =>
    ∀ i, ((p i).1 = true → y (false,i) = false) ∧ ((p i).2 = true → y (true,i) = false))
  let Z := fun (p : Mask) => ∑ y ∈ good p, base^(idx (red y) (blue y) (third y))
  (∀ (p : Mask) (a b c : Fin (n+1)),
    (Z p / base^(idx a.val b.val c.val)) % base =
      ((good p).filter (fun y => red y = a.val ∧ blue y = b.val ∧ third y = c.val)).card) := by

  intro n σ τ V X Mask base idx red blue third good Z p a b c
  have pop : Fintype.card X = 2 ^ (2*n) := by
    change Fintype.card ((Bool × Fin n) → Bool) = _
    simp
  have small : (good p).card < base := by
    have h := (good p).card_le_univ
    rw [pop] at h
    exact Nat.lt_succ_of_le h
  let e := fun y : X => idx (red y) (blue y) (third y)
  change ((∑ y ∈ good p, base ^ e y) / base ^ idx a.val b.val c.val) % base = _
  rw [histogramDigit _ _ _ _ small]
  congr 1
  ext y
  simp only [Finset.mem_filter]
  apply and_congr_right
  intro hy
  apply code_eq
  · exact Nat.lt_succ_of_le (by simpa [red] using (Finset.card_filter_le Finset.univ (fun i : Fin n => y (false,i) ≠ y (true,i))))
  · exact Nat.lt_succ_of_le (by simpa [blue] using (Finset.card_filter_le Finset.univ (fun i : Fin n => y (false,i) ≠ y (true,σ i))))
  · exact a.isLt
  · exact b.isLt


abbrev Letter := Bool × Bool
abbrev Word (n : ℕ) := Fin n → Letter

def splice {n : ℕ} (q : Fin (n+1)) (p b : Word n) : Word n :=
  fun j => if j.val < q.val then p j else b j

def response {n : ℕ} (f : Word n → ℤ) (q : Fin (n+1)) (p : Word n) : Word n → ℤ :=
  fun b => f (splice q p b)

def lattice {n : ℕ} (f : Word n → ℤ) (q : Fin (n+1)) : Submodule ℤ (Word n → ℤ) :=
  Submodule.span ℤ (Set.range (response f q))

def rowVector {n : ℕ} (f : Word n → ℤ) (q : Fin (n+1)) (p : Word n) : lattice f q :=
  ⟨response f q p, Submodule.subset_span ⟨p,rfl⟩⟩

def symbolShift {n : ℕ} (i : Fin n) (a : Letter) : (Word n → ℤ) →ₗ[ℤ] (Word n → ℤ) where
  toFun v := fun b => v (Function.update b i a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem shift_response {n : ℕ} (f : Word n → ℤ) (i : Fin n) (a : Letter) (p : Word n) :
    symbolShift i a (response f i.castSucc p) = response f i.succ (Function.update p i a) := by
  funext b
  apply congrArg f
  funext j
  by_cases h : j = i
  · subst j
    simp [splice, Function.update]
  · have ne : j.val ≠ i.val := fun e => h (Fin.ext e)
    have eqv : j.val < i.val + 1 ↔ j.val < i.val := by omega
    simp [splice, Fin.val_succ, eqv, h]

def latticeShift {n : ℕ} (f : Word n → ℤ) (i : Fin n) (a : Letter) :
    lattice f i.castSucc →ₗ[ℤ] lattice f i.succ :=
  (symbolShift i a).restrict (by
    suffices h : lattice f i.castSucc ≤ (lattice f i.succ).comap (symbolShift i a) from fun _ hx => h hx
    apply Submodule.span_le.mpr
    rintro _ ⟨p,rfl⟩
    change symbolShift i a (response f i.castSucc p) ∈ lattice f i.succ
    rw [shift_response]
    exact (rowVector f i.succ _).property)

theorem shift_row {n : ℕ} (f : Word n → ℤ) (i : Fin n) (p : Word n) :
    latticeShift f i (p i) (rowVector f i.castSucc p) = rowVector f i.succ p := by
  apply Subtype.ext
  change symbolShift i (p i) (response f i.castSucc p) = response f i.succ p
  rw [shift_response, Function.update_eq_self]

def padVector {k w : ℕ} : (Fin k → ℤ) →ₗ[ℤ] (Fin w → ℤ) where
  toFun x j := if h : j.val < k then x ⟨_,h⟩ else 0
  map_add' x y := by ext j; by_cases h : j.val < k <;> simp [h]
  map_smul' a x := by ext j; by_cases h : j.val < k <;> simp [h]

theorem coordinates {V : Type*} [AddCommGroup V] [Module ℤ V] [Module.Free ℤ V] [Module.Finite ℤ V]
    {w : ℕ} (h : Module.finrank ℤ V ≤ w) :
    ∃ (E : V →ₗ[ℤ] (Fin w → ℤ)) (D : (Fin w → ℤ) →ₗ[ℤ] V), ∀ v, D (E v) = v := by
  let e := (Module.finBasis ℤ V).equivFun
  refine ⟨padVector.comp e.toLinearMap,
    e.symm.toLinearMap.comp (LinearMap.funLeft ℤ ℤ (Fin.castLE h)), ?_⟩
  intro v
  change e.symm (fun j => if hp : j.val < Module.finrank ℤ V then e v ⟨_,hp⟩ else 0) = v
  simp

theorem linear_sum {k : ℕ} (F : (Fin k → ℤ) →ₗ[ℤ] ℤ) (x : Fin k → ℤ) :
    F x = ∑ j, x j * F (Pi.single j 1) := by
  classical
  have decom : (∑ j, x j • (Pi.single j (1:ℤ) : Fin k → ℤ)) = x := by
    ext t
    simp [Finset.sum_apply, Pi.single_apply, mul_ite]
  calc
    F x = F (∑ j, x j • (Pi.single j (1:ℤ) : Fin k → ℤ)) := congrArg F decom.symm
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]

def HasReader {n : ℕ} (f : Word n → ℤ) (w : Fin (n+1) → ℕ) : Prop :=
  ∃ (initial : Fin (w 0) → ℤ) (out : Fin (w (Fin.last n)) → ℤ)
    (T : (i : Fin n) → Letter → Fin (w i.castSucc) → Fin (w i.succ) → ℤ),
    ∀ p : Word n, ∃ run : (q : Fin (n+1)) → Fin (w q) → ℤ,
      run 0 = initial ∧
      (∀ (i : Fin n) (j : Fin (w i.succ)),
        run i.succ j = ∑ u : Fin (w i.castSucc), run i.castSucc u * T i (p i) u j) ∧
      f p = ∑ j : Fin (w (Fin.last n)), run (Fin.last n) j * out j

theorem reader_of_rank {n : ℕ} (f : Word n → ℤ) (w : Fin (n+1) → ℕ)
    (hw : ∀ q, Module.finrank ℤ (lattice f q) ≤ w q) : HasReader f w := by
  classical
  choose E D undo using fun q => coordinates (V := lattice f q) (hw q)
  let step := fun (i : Fin n) (a : Letter) =>
    (E i.succ).comp ((latticeShift f i a).comp (D i.castSucc))
  let zeroWord : Word n := fun _ => (false,false)
  let final : (Fin (w (Fin.last n)) → ℤ) →ₗ[ℤ] ℤ :=
    (LinearMap.proj zeroWord).comp ((lattice f (Fin.last n)).subtype.comp (D (Fin.last n)))
  refine ⟨E 0 (rowVector f 0 zeroWord), fun j => final (Pi.single j 1),
    fun i a u j => step i a (Pi.single u 1) j, ?_⟩
  intro p
  refine ⟨fun q => E q (rowVector f q p), ?_, ?_, ?_⟩
  · apply congrArg (E 0)
    apply Subtype.ext
    funext b
    change f (splice 0 p b) = f (splice 0 zeroWord b)
    apply congrArg f
    funext j
    simp [splice]
  · intro i j
    let v := E i.castSucc (rowVector f i.castSucc p)
    have forward : step i (p i) v = E i.succ (rowVector f i.succ p) := by
      simp [step, v, undo, shift_row]
    change E i.succ (rowVector f i.succ p) j = ∑ u, v u * step i (p i) (Pi.single u 1) j
    rw [← forward]
    exact linear_sum ((LinearMap.proj j).comp (step i (p i))) v
  · let v := E (Fin.last n) (rowVector f (Fin.last n) p)
    have output : final v = f p := by
      change ((D (Fin.last n) v : lattice f (Fin.last n)) : Word n → ℤ) zeroWord = f p
      dsimp only [v]
      rw [undo]
      change f (splice (Fin.last n) p zeroWord) = f p
      apply congrArg f
      funext i
      simp [splice,i.isLt]
    rw [← output]
    exact linear_sum final v

abbrev Transfers {n : ℕ} (w : Fin (n+1) → ℕ) :=
  (i : Fin n) → Letter → Fin (w i.castSucc) → Fin (w i.succ) → ℤ

def forward {n : ℕ} {w : Fin (n+1) → ℕ} (s : Fin (w 0) → ℤ) (T : Transfers w)
    (p : Word n) : (q : Fin (n+1)) → Fin (w q) → ℤ :=
  Fin.induction s (fun i x j => ∑ u, x u * T i (p i) u j)

def backward {n : ℕ} {w : Fin (n+1) → ℕ} (t : Fin (w (Fin.last n)) → ℤ) (T : Transfers w)
    (p : Word n) : (q : Fin (n+1)) → Fin (w q) → ℤ :=
  Fin.reverseInduction t (fun i x u => ∑ j, T i (p i) u j * x j)

theorem forward_agree {n : ℕ} {w : Fin (n+1) → ℕ} (s : Fin (w 0) → ℤ) (T : Transfers w)
    (p b : Word n) (q : Fin (n+1)) (h : ∀ j : Fin n, j.val < q.val → p j = b j) :
    forward s T p q = forward s T b q := by
  induction q using Fin.induction with
  | zero => rfl
  | succ i ih =>
    have same : forward s T p i.castSucc = forward s T b i.castSucc := by
      apply ih
      intro j hj
      exact h j (by simp only [Fin.val_castSucc] at hj; simp only [Fin.val_succ]; omega)
    have atI := h i (by simp)
    simp only [forward, Fin.induction_succ] at same ⊢
    rw [same, atI]

theorem backward_agree {n : ℕ} {w : Fin (n+1) → ℕ} (t : Fin (w (Fin.last n)) → ℤ)
    (T : Transfers w) (p b : Word n) (q : Fin (n+1))
    (h : ∀ j : Fin n, q.val ≤ j.val → p j = b j) :
    backward t T p q = backward t T b q := by
  induction q using Fin.reverseInduction with
  | last => simp [backward]
  | cast i ih =>
    have same : backward t T p i.succ = backward t T b i.succ := by
      apply ih
      intro j hj
      exact h j (by simp only [Fin.val_succ] at hj; simp only [Fin.val_castSucc]; omega)
    have atI := h i (by simp)
    simp only [backward, Fin.reverseInduction_castSucc] at same ⊢
    rw [same, atI]

theorem reader_factor {n : ℕ} {w : Fin (n+1) → ℕ} {f : Word n → ℤ}
    (s : Fin (w 0) → ℤ) (t : Fin (w (Fin.last n)) → ℤ) (T : Transfers w)
    (good : ∀ p : Word n, ∃ run : (q : Fin (n+1)) → Fin (w q) → ℤ,
      run 0 = s ∧
      (∀ i j, run i.succ j = ∑ u, run i.castSucc u * T i (p i) u j) ∧
      f p = ∑ j, run (Fin.last n) j * t j)
    (p b : Word n) (q : Fin (n+1)) :
    response f q p b = ∑ j, forward s T p q j * backward t T b q j := by
  let z := splice q p b
  obtain ⟨run, at0, next, finish⟩ := good z
  have runs : ∀ i, run i = forward s T z i := by
    intro i
    induction i using Fin.induction with
    | zero => exact at0
    | succ i ih =>
      funext j
      simp only [forward, Fin.induction_succ]
      rw [next, ih]
      rfl
  have value : ∀ i, f z = ∑ j, run i j * backward t T z i j := by
    intro i
    induction i using Fin.reverseInduction with
    | last => simpa [backward] using finish
    | cast i ih =>
      rw [ih]
      simp only [next, Finset.sum_mul, backward, Fin.reverseInduction_castSucc,
        Finset.mul_sum, mul_assoc]
      exact Finset.sum_comm
  have pre : forward s T z q = forward s T p q := by
    apply forward_agree
    intro j hj
    simp [z, splice, hj]
  have post : backward t T z q = backward t T b q := by
    apply backward_agree
    intro j hj
    simp [z, splice, Nat.not_lt.mpr hj]
  change f z = _
  simpa only [runs, pre, post] using value q

theorem rank_of_reader {n : ℕ} (f : Word n → ℤ) (w : Fin (n+1) → ℕ)
    (reader : HasReader f w) (q : Fin (n+1)) :
    Module.finrank ℤ (lattice f q) ≤ w q := by
  classical
  obtain ⟨s,t,T,good⟩ := reader
  let obs : (Fin (w q) → ℤ) →ₗ[ℤ] (Word n → ℤ) :=
    { toFun := fun x b => ∑ u, x u * backward t T b q u
      map_add' := by intro x y; ext b; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro c x; ext b; simp [smul_eq_mul, Finset.mul_sum, mul_assoc] }
  have sub : lattice f q ≤ LinearMap.range obs := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p,rfl⟩
    refine ⟨forward s T p q, ?_⟩
    funext b
    exact (reader_factor s t T good p b q).symm
  exact (Submodule.finrank_mono sub).trans (by simpa using obs.finrank_range_le)

theorem reader_iff_rank {n : ℕ} (f : Word n → ℤ) (w : Fin (n+1) → ℕ) :
    HasReader f w ↔ ∀ q, Module.finrank ℤ (lattice f q) ≤ w q :=
  ⟨rank_of_reader f w, reader_of_rank f w⟩


def CrossingMatching {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (q : Fin (n+1))
    (M : Finset (Fin n × Fin n)) : Prop :=
  (∀ e ∈ M, (decide (e.1.val < q.val) ≠ decide (e.2.val < q.val)) ∧
    (e.2 = σ e.1 ∨ e.2 = τ e.1)) ∧
  Set.InjOn Prod.fst (↑M : Set (Fin n × Fin n)) ∧
  Set.InjOn Prod.snd (↑M : Set (Fin n × Fin n))

noncomputable def matchingWidth {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (q : Fin (n+1)) : ℕ := by
  classical
  exact (Finset.univ.filter (CrossingMatching σ τ q)).sup (fun M => 2 ^ M.card)

theorem matchingWidth_le {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (q : Fin (n+1)) (d : ℕ) :
    matchingWidth σ τ q ≤ d ↔ ∀ M, CrossingMatching σ τ q M → 2 ^ M.card ≤ d := by
  classical
  simp [matchingWidth, Finset.sup_le_iff]

theorem posted_of_cut_rank : ∀ (n : ℕ) (σ τ : Equiv.Perm (Fin n)),
  let V := Bool × Fin n
  let X := V → Bool
  let Mask := Fin n → Bool × Bool
  let base : ℕ := 2^(2*n)+1
  let idx := fun (a b c : ℕ) => a + (n+1)*b + (n+1)^2*c
  let red := fun (y : X) =>
    (Finset.univ.filter (fun i : Fin n => y (false,i) ≠ y (true,i))).card
  let blue := fun (y : X) =>
    (Finset.univ.filter (fun i : Fin n => y (false,i) ≠ y (true,σ i))).card
  let third := fun (y : X) =>
    (Finset.univ.filter (fun i : Fin n => y (false,i) = y (true,τ i))).card
  let good := fun (p : Mask) => (Finset.univ : Finset X).filter (fun y =>
    ∀ i, ((p i).1 = true → y (false,i) = false) ∧ ((p i).2 = true → y (true,i) = false))
  let Z := fun (p : Mask) => ∑ y ∈ good p, base^(idx (red y) (blue y) (third y))
  (∀ q : Fin (n+1), Module.finrank ℤ (lattice (fun p : Mask => (Z p : ℤ)) q) =
    matchingWidth σ τ q) →
  (∀ (p : Mask) (a b c : Fin (n+1)),
    (Z p / base^(idx a.val b.val c.val)) % base =
      ((good p).filter (fun y => red y = a.val ∧ blue y = b.val ∧ third y = c.val)).card) ∧
  ∀ w : Fin (n+1) → ℕ,
    (∃ (initial : Fin (w 0) → ℤ) (out : Fin (w (Fin.last n)) → ℤ)
      (T : (i : Fin n) → Bool × Bool → Fin (w i.castSucc) → Fin (w i.succ) → ℤ),
      ∀ p : Mask, ∃ run : (q : Fin (n+1)) → Fin (w q) → ℤ,
        run 0 = initial ∧
        (∀ (i : Fin n) (j : Fin (w i.succ)),
          run i.succ j = ∑ u : Fin (w i.castSucc), run i.castSucc u * T i (p i) u j) ∧
        (Z p : ℤ) = ∑ j : Fin (w (Fin.last n)), run (Fin.last n) j * out j) ↔
      ∀ (q : Fin (n+1)) (M : Finset (Fin n × Fin n)),
        (∀ e ∈ M, (decide (e.1.val < q.val) ≠ decide (e.2.val < q.val)) ∧
          (e.2 = σ e.1 ∨ e.2 = τ e.1)) →
        Set.InjOn Prod.fst (↑M : Set (Fin n × Fin n)) →
        Set.InjOn Prod.snd (↑M : Set (Fin n × Fin n)) → 2^M.card ≤ w q := by

  intro n σ τ V X Mask base idx red blue third good Z ranks
  constructor
  · exact postedHistogram n σ τ
  · intro w
    change HasReader (fun p : Mask => (Z p : ℤ)) w ↔ _
    rw [reader_iff_rank]
    constructor
    · intro hw q M edges left right
      exact (matchingWidth_le σ τ q (w q)).mp ((ranks q) ▸ hw q) M ⟨edges,left,right⟩
    · intro hw q
      rw [ranks q, matchingWidth_le]
      intro M hM
      exact hw q M hM.1 hM.2.1 hM.2.2

def PostedCutRanks : Prop := ∀ (n : ℕ) (σ τ : Equiv.Perm (Fin n)),
  let V := Bool × Fin n
  let X := V → Bool
  let Mask := Fin n → Bool × Bool
  let base : ℕ := 2^(2*n)+1
  let idx := fun (a b c : ℕ) => a + (n+1)*b + (n+1)^2*c
  let red := fun (y : X) =>
    (Finset.univ.filter (fun i : Fin n => y (false,i) ≠ y (true,i))).card
  let blue := fun (y : X) =>
    (Finset.univ.filter (fun i : Fin n => y (false,i) ≠ y (true,σ i))).card
  let third := fun (y : X) =>
    (Finset.univ.filter (fun i : Fin n => y (false,i) = y (true,τ i))).card
  let good := fun (p : Mask) => (Finset.univ : Finset X).filter (fun y =>
    ∀ i, ((p i).1 = true → y (false,i) = false) ∧ ((p i).2 = true → y (true,i) = false))
  let Z := fun (p : Mask) => ∑ y ∈ good p, base^(idx (red y) (blue y) (third y))
  ∀ q : Fin (n+1), Module.finrank ℤ (lattice (fun p : Mask => (Z p : ℤ)) q) = matchingWidth σ τ q

def subsetSum {ι V : Type*} [AddCommMonoid V] (v : Finset ι → V) (S : Finset ι) : V :=
  ∑ t ∈ S.powerset, v t

theorem subsetSum_span {ι V : Type*} [AddCommGroup V] [Module ℤ V] (v : Finset ι → V) :
    Submodule.span ℤ (Set.range (subsetSum v)) = Submodule.span ℤ (Set.range v) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨S,rfl⟩
    exact Submodule.sum_mem _ fun t _ => Submodule.subset_span ⟨t,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨S,rfl⟩
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      let P := Submodule.span ℤ (Set.range (subsetSum v))
      have allmem : subsetSum v S ∈ P := Submodule.subset_span ⟨S,rfl⟩
      have small : ∑ t ∈ S.powerset.erase S, v t ∈ P := by
        apply Submodule.sum_mem
        intro t ht
        obtain ⟨hne, hsub⟩ := Finset.mem_erase.mp ht
        exact ih t (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp hsub,hne⟩)
      have entire : (∑ t ∈ S.powerset.erase S, v t) + v S = subsetSum v S :=
        Finset.sum_erase_add _ _ (Finset.mem_powerset.mpr (by rfl))
      rw [← entire] at allmem
      simpa using P.sub_mem allmem small

def subsetMap {ι : Type*} : (Finset ι → ℤ) →ₗ[ℤ] (Finset ι → ℤ) where
  toFun := subsetSum
  map_add' f g := by ext S; simp [subsetSum, Finset.sum_add_distrib]
  map_smul' c f := by ext S; simp [subsetSum, smul_eq_mul, Finset.mul_sum]

theorem subsetMap_injective {ι : Type*} : Function.Injective (subsetMap (ι := ι)) := by
  classical
  intro f g eqv
  funext S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    have h := congrFun eqv S
    change (∑ t ∈ S.powerset, f t) = ∑ t ∈ S.powerset, g t at h
    have mem : S ∈ S.powerset := Finset.mem_powerset.mpr (by rfl)
    rw [← Finset.sum_erase_add _ _ mem, ← Finset.sum_erase_add _ _ mem] at h
    have same : ∑ t ∈ S.powerset.erase S, f t = ∑ t ∈ S.powerset.erase S, g t := by
      apply Finset.sum_congr rfl
      intro t ht
      obtain ⟨hne,hsub⟩ := Finset.mem_erase.mp ht
      exact ih t (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp hsub,hne⟩)
    omega

theorem pinRank {ι κ : Type*} (M : Finset ι → Finset κ → ℤ) :
    Module.finrank ℤ (Submodule.span ℤ (Set.range (fun S => subsetSum (fun t => subsetMap (M t)) S))) =
      Module.finrank ℤ (Submodule.span ℤ (Set.range M)) := by
  rw [subsetSum_span]
  let P := Submodule.span ℤ (Set.range M)
  have mapped : Submodule.span ℤ (Set.range (fun t => subsetMap (M t))) = P.map subsetMap := by
    rw [show P = Submodule.span ℤ (Set.range M) from rfl, Submodule.map_span]
    congr 1
    exact Set.range_comp' subsetMap M
  rw [mapped]
  exact (Submodule.equivMapOfInjective subsetMap subsetMap_injective P).finrank_eq.symm

theorem dominantPowers {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ℕ) (E : ι → ι → ℕ) (hb : Fintype.card ι < b)
    (higher : ∀ i j, j ≠ i → E i j < E i i) :
    (Matrix.of fun i j => (b : ℝ) ^ E i j).det ≠ 0 := by
  apply det_ne_zero_of_sum_row_lt_diag
  intro i
  have hb0 : 0 < b := by omega
  have hnat : (∑ j ∈ Finset.univ.erase i, b ^ E i j) < b ^ E i i := by
    have prodBound : b * (∑ j ∈ Finset.univ.erase i, b ^ E i j) < b * b ^ E i i := by
      rw [Finset.mul_sum]
      calc
        (∑ j ∈ Finset.univ.erase i, b * b ^ E i j) ≤ ∑ _j ∈ Finset.univ.erase i, b ^ E i i := by
          apply Finset.sum_le_sum
          intro j hj
          rw [← pow_succ']
          exact Nat.pow_le_pow_right hb0 (higher i j (Finset.mem_erase.mp hj).1)
        _ = (Finset.univ.erase i).card * b ^ E i i := by simp
        _ < b * b ^ E i i := by
          apply Nat.mul_lt_mul_of_pos_right _ (pow_pos hb0 _)
          exact lt_of_le_of_lt ((Finset.univ.erase i).card_le_univ) hb
    exact (Nat.mul_lt_mul_left hb0).mp prodBound
  simp only [Matrix.of_apply, Real.norm_eq_abs, abs_pow, abs_of_nonneg (show (0:ℝ) ≤ b by positivity)]
  exact_mod_cast hnat

theorem rankPairDiagonal {ι κ : Type*} [Fintype ι] [Fintype κ] (A B : Matrix ι κ ℝ) :
    (Matrix.fromBlocks A (0 : Matrix ι κ ℝ) 0 B).rank = A.rank + B.rank := by
  let e1 := LinearEquiv.sumArrowLequivProdArrow ι ι ℝ ℝ
  let e2 := LinearEquiv.sumArrowLequivProdArrow κ κ ℝ ℝ
  have key : (Matrix.fromBlocks A (0 : Matrix ι κ ℝ) 0 B).mulVecLin =
      (e1.symm.toLinearMap.comp (LinearMap.prodMap A.mulVecLin B.mulVecLin)).comp e2.toLinearMap := by
    apply LinearMap.ext
    intro x
    funext i
    rcases i with i | i <;> simp [e1, e2, Matrix.fromBlocks_mulVec, LinearEquiv.sumArrowLequivProdArrow] <;> rfl
  unfold Matrix.rank
  rw [key, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range e2), LinearMap.range_comp,
    LinearEquiv.finrank_map_eq, LinearMap.range_prodMap, (Submodule.prodEquiv _ _).finrank_eq,
    Module.finrank_prod]

theorem leafRank {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (M : Matrix ι κ ℝ) (a b c d : ℝ) (hd : a*d-b*c ≠ 0)
    (D₀ D₁ : Matrix ι ι ℝ) (h₀ : IsUnit D₀.det) (h₁ : IsUnit D₁.det) :
    (Matrix.fromBlocks (a • (D₀*M)) (b • (D₁*M)) (c • (D₀*M)) (d • (D₁*M))).rank =
      2 * M.rank := by
  classical
  let I : Matrix ι ι ℝ := 1
  let A := Matrix.fromBlocks (a • I) (b • I) (c • I) (d • I)
  let B := Matrix.fromBlocks ((d / (a*d-b*c)) • I) ((-b / (a*d-b*c)) • I)
    ((-c / (a*d-b*c)) • I) ((a / (a*d-b*c)) • I)
  have hBA : B*A = 1 := by
    have h00 : a*(d/(a*d-b*c)) + c*((-b)/(a*d-b*c)) = 1 := by field_simp [hd] <;> ring
    have h01 : b*(d/(a*d-b*c)) + d*((-b)/(a*d-b*c)) = 0 := by ring
    have h10 : a*((-c)/(a*d-b*c))+c*(a/(a*d-b*c)) = 0 := by ring
    have h11 : b*((-c)/(a*d-b*c))+d*(a/(a*d-b*c)) = 1 := by field_simp [hd] <;> ring
    simp only [B,A,I,Matrix.fromBlocks_multiply, Matrix.smul_mul, Matrix.mul_smul,
      one_mul, smul_smul, ← add_smul, h00, h01, h10, h11, zero_smul, one_smul, Matrix.fromBlocks_one]
  let block := Matrix.fromBlocks (D₀*M) (0 : Matrix ι κ ℝ) 0 (D₁*M)
  have hfactor : A*block = Matrix.fromBlocks (a • (D₀*M)) (b • (D₁*M)) (c • (D₀*M)) (d • (D₁*M)) := by
    simp [A,I,block,Matrix.fromBlocks_multiply,Matrix.smul_mul]
  rw [← hfactor]
  have eqrk : (A*block).rank = block.rank := by
    apply le_antisymm (Matrix.rank_mul_le_right _ _)
    calc block.rank = (B*(A*block)).rank := by rw [← Matrix.mul_assoc,hBA,Matrix.one_mul]
         _ ≤ _ := Matrix.rank_mul_le_right _ _
  rw [eqrk,rankPairDiagonal,Matrix.rank_mul_eq_right_of_isUnit_det _ _ h₀,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ h₁, two_mul]



abbrev Vertex (n : ℕ) := Bool × Fin n
abbrev Before {n : ℕ} (q : Fin (n+1)) := {v : Vertex n // v.2.val < q.val}
abbrev After {n : ℕ} (q : Fin (n+1)) := {v : Vertex n // ¬ v.2.val < q.val}

def asSpins {n : ℕ} (p : Word n) : Vertex n → Bool :=
  fun v => if v.1 then (p v.2).2 else (p v.2).1

def asWord {n : ℕ} (y : Vertex n → Bool) : Word n :=
  fun i => (y (false,i),y (true,i))

theorem spins_word {n : ℕ} (y : Vertex n → Bool) : asSpins (asWord y) = y := by
  funext v
  rcases v with ⟨b,i⟩
  cases b <;> rfl

def joinSpins {n : ℕ} (q : Fin (n+1)) (x : Finset (Before q) × Finset (After q)) :
    Vertex n → Bool :=
  fun v => if h : v.2.val < q.val then decide (⟨v,h⟩ ∈ x.1) else decide (⟨v,h⟩ ∈ x.2)

def splitSpins {n : ℕ} (q : Fin (n+1)) :
    (Vertex n → Bool) ≃ Finset (Before q) × Finset (After q) where
  toFun y := (Finset.univ.filter (fun v : Before q => y v), Finset.univ.filter (fun v : After q => y v))
  invFun := joinSpins q
  left_inv y := by
    funext v
    by_cases h : v.2.val < q.val <;> simp [joinSpins, h]
  right_inv x := by
    apply Prod.ext
    · ext v
      simp [joinSpins, v.property]
    · ext v
      simp [joinSpins, v.property]

theorem pin_iff_subsets {n : ℕ} (q : Fin (n+1)) (p : Word n) (y : Vertex n → Bool) :
    (∀ i, ((p i).1 = true → y (false,i) = false) ∧ ((p i).2 = true → y (true,i) = false)) ↔
    ((splitSpins q y).1 ⊆ ((splitSpins q (asSpins p)).1)ᶜ ∧
     (splitSpins q y).2 ⊆ ((splitSpins q (asSpins p)).2)ᶜ) := by
  change _ ↔ (Finset.univ.filter (fun v : Before q => y v) ⊆
    (Finset.univ.filter (fun v : Before q => asSpins p v))ᶜ ∧
    Finset.univ.filter (fun v : After q => y v) ⊆
    (Finset.univ.filter (fun v : After q => asSpins p v))ᶜ)
  simp only [Finset.subset_iff, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
  constructor
  · intro h
    have separated : ∀ v : Vertex n, y v = true → ¬ asSpins p v = true := by
      rintro ⟨b,i⟩ hy hp
      cases b with
      | false => simpa [hy] using (h i).1 hp
      | true => simpa [hy] using (h i).2 hp
    exact ⟨fun v => separated v, fun v => separated v⟩
  · rintro ⟨hl,hr⟩ i
    have separated (v : Vertex n) (hp : asSpins p v = true) : y v = false := by
      by_cases side : v.2.val < q.val
      · cases hy : y v with
        | false => rfl
        | true => exact False.elim (hl (x := ⟨v,side⟩) hy hp)
      · cases hy : y v with
        | false => rfl
        | true => exact False.elim (hr (x := ⟨v,side⟩) hy hp)
    exact ⟨separated (false,i), separated (true,i)⟩

theorem restricted_sum {α : Type*} [Fintype α] [DecidableEq α] (s : Finset α)
    (F : Finset α → ℤ) :
    (∑ t : Finset α, if t ⊆ s then F t else 0) = subsetSum F s := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext t
  simp

theorem rectangle_sum {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (F : Finset ι → Finset κ → ℤ) (s : Finset ι) (t : Finset κ) :
    (∑ z : Finset ι × Finset κ, if z.1 ⊆ s ∧ z.2 ⊆ t then F z.1 z.2 else 0) =
      subsetSum (fun u => subsetMap (F u)) s t := by
  classical
  rw [Fintype.sum_prod_type]
  change _ = (∑ u ∈ s.powerset, subsetMap (F u)) t
  rw [Finset.sum_apply]
  change _ = subsetSum (fun u => subsetSum (F u) t) s
  rw [← restricted_sum]
  apply Finset.sum_congr rfl
  intro u _
  by_cases h : u ⊆ s
  · simp only [h, true_and, ite_true, restricted_sum]
  · simp [h]

def pinned {n : ℕ} (F : (Vertex n → Bool) → ℤ) (p : Word n) : ℤ :=
  ∑ y : Vertex n → Bool, if ∀ i, ((p i).1 = true → y (false,i) = false) ∧
    ((p i).2 = true → y (true,i) = false) then F y else 0

def spinMatrix {n : ℕ} (F : (Vertex n → Bool) → ℤ) (q : Fin (n+1)) :
    Finset (Before q) → Finset (After q) → ℤ :=
  fun s t => F (joinSpins q (s,t))

theorem pinned_split {n : ℕ} (F : (Vertex n → Bool) → ℤ) (q : Fin (n+1)) (p : Word n) :
    pinned F p = subsetSum (fun u => subsetMap (spinMatrix F q u))
      ((splitSpins q (asSpins p)).1)ᶜ ((splitSpins q (asSpins p)).2)ᶜ := by
  let left := ((splitSpins q (asSpins p)).1)ᶜ
  let right := ((splitSpins q (asSpins p)).2)ᶜ
  let H := fun z : Finset (Before q) × Finset (After q) =>
    if z.1 ⊆ left ∧ z.2 ⊆ right then spinMatrix F q z.1 z.2 else 0
  calc
    pinned F p = ∑ y, H (splitSpins q y) := by
      apply Finset.sum_congr rfl
      intro y _
      simp only [H, pin_iff_subsets q p y]
      have hv : spinMatrix F q (splitSpins q y).1 (splitSpins q y).2 = F y :=
        congrArg F ((splitSpins q).symm_apply_apply y)
      rw [hv]
    _ = ∑ z, H z := (splitSpins q).sum_comp H
    _ = _ := rectangle_sum (spinMatrix F q) left right

theorem splice_sides {n : ℕ} (q : Fin (n+1)) (a b : Word n) :
    splitSpins q (asSpins (splice q a b)) =
      ((splitSpins q (asSpins a)).1, (splitSpins q (asSpins b)).2) := by
  apply Prod.ext
  · ext v
    change v ∈ Finset.univ.filter _ ↔ v ∈ Finset.univ.filter _
    simp [asSpins, splice, v.property]
  · ext v
    change v ∈ Finset.univ.filter _ ↔ v ∈ Finset.univ.filter _
    simp [asSpins, splice, v.property]

theorem pull_rank {I J U V : Type*} (F : I → J → ℤ) (l : U → I) (r : V → J)
    (hl : Function.Surjective l) (hr : Function.Surjective r) :
    Module.finrank ℤ (Submodule.span ℤ (Set.range (fun a b => F (l a) (r b)))) =
      Module.finrank ℤ (Submodule.span ℤ (Set.range F)) := by
  let A := LinearMap.funLeft ℤ ℤ r
  have hA : Function.Injective A := by
    intro x y h
    funext j
    obtain ⟨b,rfl⟩ := hr j
    exact congrFun h b
  let P := Submodule.span ℤ (Set.range F)
  have ht : Set.range (fun a b => F (l a) (r b)) = A '' Set.range F := by
    ext t
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨F (l a), ⟨l a,rfl⟩,rfl⟩
    · rintro ⟨v,⟨i,rfl⟩,rfl⟩
      obtain ⟨x,rfl⟩ := hl i
      exact ⟨x,rfl⟩
  rw [ht, ← Submodule.map_span]
  exact (Submodule.equivMapOfInjective A hA P).finrank_eq.symm

theorem physical_cut_rank {n : ℕ} (F : (Vertex n → Bool) → ℤ) (q : Fin (n+1)) :
    Module.finrank ℤ (lattice (pinned F) q) =
      Module.finrank ℤ (Submodule.span ℤ (Set.range (spinMatrix F q))) := by
  classical
  let E := splitSpins q
  let l := fun p : Word n => (E (asSpins p)).1ᶜ
  let r := fun p : Word n => (E (asSpins p)).2ᶜ
  have hl : Function.Surjective l := by
    intro s
    refine ⟨asWord (E.symm (sᶜ,∅)), ?_⟩
    simp [l, spins_word]
  have hr : Function.Surjective r := by
    intro s
    refine ⟨asWord (E.symm (∅,sᶜ)), ?_⟩
    simp [r, spins_word]
  let grid := fun u => subsetSum (fun t => subsetMap (spinMatrix F q t)) u
  have he : response (pinned F) q = fun a b => grid (l a) (r b) := by
    funext a b
    rw [response, pinned_split, splice_sides]
  unfold lattice
  rw [he, pull_rank grid l r hl hr]
  exact pinRank (spinMatrix F q)

def spinWeight {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (y : Vertex n → Bool) : ℤ :=
  let red := (Finset.univ.filter (fun i : Fin n => y (false,i) ≠ y (true,i))).card
  let blue := (Finset.univ.filter (fun i : Fin n => y (false,i) ≠ y (true,σ i))).card
  let third := (Finset.univ.filter (fun i : Fin n => y (false,i) = y (true,τ i))).card
  ((2^(2*n)+1 : ℕ) : ℤ) ^ (red + (n+1)*blue + (n+1)^2*third)

def PhysicalCutRanks : Prop := ∀ (n : ℕ) (σ τ : Equiv.Perm (Fin n)) (q : Fin (n+1)),
  Module.finrank ℤ (Submodule.span ℤ (Set.range (spinMatrix (spinWeight σ τ) q))) = matchingWidth σ τ q

theorem physical_reduction (h : PhysicalCutRanks) : PostedCutRanks := by
  intro n σ τ V X Mask base idx red blue third good Z q
  have ident : (fun p : Mask => (Z p : ℤ)) = pinned (spinWeight σ τ) := by
    funext p
    simp [Z, good, pinned, Finset.sum_filter, spinWeight, red, blue, third, idx, base]
    rfl
  rw [ident, physical_cut_rank]
  exact h n σ τ q

theorem bipartite_cover_match {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (t : A → Finset B) :
    ∃ (P : Finset A) (Q : Finset B) (M : Finset (A × B)),
      (∀ a b, b ∈ t a → a ∈ P ∨ b ∈ Q) ∧
      (∀ e ∈ M, e.2 ∈ t e.1) ∧
      Set.InjOn Prod.fst (↑M : Set (A × B)) ∧ Set.InjOn Prod.snd (↑M : Set (A × B)) ∧
      P.card + Q.card ≤ M.card := by
  classical
  let cost := fun S : Finset A => Sᶜ.card + (S.biUnion t).card
  obtain ⟨S,_,hmin⟩ := Finset.exists_min_image Finset.univ cost Finset.univ_nonempty
  have hcost : cost S ≤ Fintype.card A := by simpa [cost] using hmin ∅ (Finset.mem_univ _)
  let d := Fintype.card A - cost S
  let aug := fun a => (t a).disjSum (Finset.univ : Finset (Fin d))
  obtain ⟨f, hf, hmem⟩ : ∃ f : A → B ⊕ Fin d, Function.Injective f ∧ ∀ a, f a ∈ aug a := by
    apply (Finset.all_card_le_biUnion_card_iff_existsInjective' aug).mp
    intro U
    rcases U.eq_empty_or_nonempty with rfl | hU
    · simp
    have eqv : U.biUnion aug = (U.biUnion t).disjSum (Finset.univ : Finset (Fin d)) := by
      ext z
      rcases z with b | i
      · simp [aug]
      · simpa [aug] using (show ∃ a, a ∈ U from hU)
    rw [eqv, Finset.card_disjSum, Finset.card_univ, Fintype.card_fin]
    have hUmin := hmin U (Finset.mem_univ _)
    have hcounts := Finset.card_compl_add_card U
    change cost S ≤ Uᶜ.card + (U.biUnion t).card at hUmin
    dsimp [d]
    omega
  let R := Finset.univ.image f
  have get (b : R.toLeft) : ∃ a, f a = Sum.inl b.val :=
    by simpa [R] using Finset.mem_toLeft.mp b.property
  let edge := fun b : R.toLeft => ((get b).choose,b.val)
  have unique : Function.Injective edge := fun x y eqv => Subtype.ext (congrArg Prod.snd eqv)
  let M := Finset.univ.image edge
  refine ⟨Sᶜ, S.biUnion t, M, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hb
    by_cases ha : a ∈ S
    · exact Or.inr (Finset.mem_biUnion.mpr ⟨a,ha,hb⟩)
    · exact Or.inl (Finset.mem_compl.mpr ha)
  · intro e he
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp he
    have prop := hmem (get b).choose
    rw [(get b).choose_spec] at prop
    simpa [aug,edge] using prop
  · intro x hx y hy heq
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hy
    change (get b).choose = (get c).choose at heq
    have eqv : (Sum.inl b.val : B ⊕ Fin d) = Sum.inl c.val :=
      (get b).choose_spec.symm.trans ((congrArg f heq).trans (get c).choose_spec)
    exact congrArg edge (Subtype.ext (Sum.inl.inj eqv))
  · intro x hx y hy heq
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hy
    exact congrArg edge (Subtype.ext heq)
  · have hcard : R.card = Fintype.card A := by simp [R, Finset.card_image_of_injective _ hf]
    have hsplit : R.toLeft.card + R.toRight.card = R.card := Finset.card_toLeft_add_card_toRight
    have hright : R.toRight.card ≤ d := by simpa using R.toRight.card_le_univ
    have hm : M.card = R.toLeft.card := by simp [M, Finset.card_image_of_injective _ unique]
    change cost S ≤ M.card
    dsimp [d] at hright
    omega

theorem separated_rank {I J K : Type*} [Fintype J] [Fintype K]
    (F : I → J → ℤ) (L : I → K → ℤ) (R : K → J → ℤ)
    (fac : ∀ i j, F i j = ∑ k, L i k * R k j) :
    Module.finrank ℤ (Submodule.span ℤ (Set.range F)) ≤ Fintype.card K := by
  classical
  let P := Submodule.span ℤ (Set.range R)
  have inc : Submodule.span ℤ (Set.range F) ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    have eqv : F i = ∑ k, L i k • R k := by ext j; simpa [Finset.sum_apply] using fac i j
    rw [eqv]
    exact P.sum_mem fun k _ => P.smul_mem _ (Submodule.subset_span ⟨k,rfl⟩)
  exact (Submodule.finrank_mono inc).trans ((finrank_span_le_card (R := ℤ) (Set.range R)).trans
    (by rw [Set.toFinset_range]; exact Finset.card_image_le.trans_eq Finset.card_univ))

theorem rank_cover {n : ℕ} {E : Type*} [Fintype E] (q : Fin (n+1)) (C : Finset (Vertex n))
    (u v : E → Vertex n) (H : E → Bool → Bool → ℤ)
    (covers : ∀ e, (decide ((u e).2.val < q.val) ≠ decide ((v e).2.val < q.val)) →
      u e ∈ C ∨ v e ∈ C) :
    Module.finrank ℤ (Submodule.span ℤ (Set.range
      (spinMatrix (fun y => ∏ e, H e (y (u e)) (y (v e))) q))) ≤ 2^C.card := by
  classical
  let front := fun w : Vertex n => w.2.val < q.val
  let pre := fun (s : Finset (Before q)) => joinSpins q (s,∅)
  let post := fun (t : Finset (After q)) => joinSpins q (∅,t)
  let label := fun (c : C → Bool) (w : Vertex n) => if h : w ∈ C then c ⟨w,h⟩ else false
  let left := fun s c w => if front w then pre s w else label c w
  let right := fun t c w => if front w then label c w else post t w
  let useL := fun e => (front (u e) ∨ u e ∈ C) ∧ (front (v e) ∨ v e ∈ C)
  have useR : ∀ e, ¬useL e → (¬front (u e) ∨ u e ∈ C) ∧ (¬front (v e) ∨ v e ∈ C) := by
    intro e h
    have hc := covers e
    change (decide (front (u e)) ≠ decide (front (v e))) → _ at hc
    dsimp [useL] at h
    by_cases a : front (u e) <;> by_cases b : front (v e) <;> simp_all
  let okL := fun s (c : C → Bool) => ∀ w : C, front w.val → c w = pre s w.val
  let okR := fun t (c : C → Bool) => ∀ w : C, ¬front w.val → c w = post t w.val
  let L := fun s c => if okL s c then ∏ e, if useL e then H e (left s c (u e)) (left s c (v e)) else 1 else 0
  let R := fun c t => if okR t c then ∏ e, if useL e then 1 else H e (right t c (u e)) (right t c (v e)) else 0
  have decmp : ∀ s t, spinMatrix (fun y => ∏ e, H e (y (u e)) (y (v e))) q s t = ∑ c, L s c * R c t := by
    intro s t
    let y := joinSpins q (s,t)
    let c₀ : C → Bool := fun w => y w.val
    have hp (w : Vertex n) (h : front w) : pre s w = y w := by
      change w.2.val < q.val at h
      simp [pre,y,joinSpins,h]
    have hs (w : Vertex n) (h : ¬front w) : post t w = y w := by
      change ¬w.2.val < q.val at h
      simp [post,y,joinSpins,h]
    have hcL : okL s c₀ := fun w hw => (hp w.val hw).symm
    have hcR : okR t c₀ := fun w hw => (hs w.val hw).symm
    have lgood (w : Vertex n) (h : front w ∨ w ∈ C) : left s c₀ w = y w := by
      by_cases hf : front w
      · simpa [left,hf] using hp w hf
      · simp [left,hf,label,h.resolve_left hf,c₀]
    have rgood (w : Vertex n) (h : ¬front w ∨ w ∈ C) : right t c₀ w = y w := by
      by_cases hf : front w
      · simp [right,hf,label,h.resolve_left (not_not_intro hf),c₀]
      · simpa [right,hf] using hs w hf
    rw [Finset.sum_eq_single c₀]
    · simp only [L,R, hcL,hcR, ite_true, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro e _
      by_cases h : useL e
      · simp [h,lgood _ h.1,lgood _ h.2,y]
      · simp [h,rgood _ (useR e h).1,rgood _ (useR e h).2,y]
    · intro c _ hn
      by_cases hl : okL s c
      · have hr : ¬okR t c := by
          intro hr
          apply hn
          funext w
          by_cases hw : front w.val
          · exact (hl w hw).trans (hp w.val hw)
          · exact (hr w hw).trans (hs w.val hw)
        simp [R,hr]
      · simp [L,hl]
    · simp
  simpa using separated_rank _ L R decmp

abbrev EdgeSet (n : ℕ) := Fin n ⊕ (Fin n ⊕ Fin n)
def source {n : ℕ} : EdgeSet n → Vertex n :=
  Sum.elim (fun i => (false,i)) (Sum.elim (fun i => (false,i)) (fun i => (false,i)))
def target {n : ℕ} (σ τ : Equiv.Perm (Fin n)) : EdgeSet n → Vertex n :=
  Sum.elim (fun i => (true,i)) (Sum.elim (fun i => (true,σ i)) (fun i => (true,τ i)))
def coupling {n : ℕ} : EdgeSet n → Bool → Bool → ℤ :=
  let b : ℤ := (2^(2*n)+1 : ℕ)
  Sum.elim (fun _ a c => if a ≠ c then b^1 else 1)
    (Sum.elim (fun _ a c => if a ≠ c then b^(n+1) else 1)
      (fun _ a c => if a = c then b^((n+1)^2) else 1))

theorem counted_weight {A : Type*} [Fintype A] (b : ℤ) (k : ℕ) (p : A → Prop) [DecidablePred p] :
    (∏ i, if p i then b^k else 1) = b^(k*(Finset.univ.filter p).card) := by
  rw [← Finset.prod_filter, Finset.prod_const, ← pow_mul]

theorem spinWeight_product {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    spinWeight σ τ = fun y => ∏ e : EdgeSet n, coupling e (y (source e)) (y (target σ τ e)) := by
  funext y
  simp only [Fintype.prod_sum_type, source,target,coupling,Sum.elim_inl,Sum.elim_inr,
    counted_weight, spinWeight, one_mul]
  rw [pow_add, pow_add, mul_assoc]

theorem cut_rank_upper {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (q : Fin (n+1)) :
    Module.finrank ℤ (Submodule.span ℤ (Set.range (spinMatrix (spinWeight σ τ) q))) ≤ matchingWidth σ τ q := by
  classical
  let N := fun i : Fin n => Finset.univ.filter fun j : Fin n =>
    (decide (i.val < q.val) ≠ decide (j.val < q.val)) ∧ (j = σ i ∨ j = τ i)
  obtain ⟨P,Q,M,hcover,hedge,hfst,hsnd,hsize⟩ := bipartite_cover_match N
  let C := P.image (Prod.mk false) ∪ Q.image (Prod.mk true)
  have cp (i : Fin n) (hi : i ∈ P) : (false,i) ∈ C := Finset.mem_union_left _ (Finset.mem_image_of_mem _ hi)
  have cq (i : Fin n) (hi : i ∈ Q) : (true,i) ∈ C := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi)
  have cover : ∀ e : EdgeSet n, (decide ((source e).2.val < q.val) ≠ decide ((target σ τ e).2.val < q.val)) →
      source e ∈ C ∨ target σ τ e ∈ C := by
    rintro (i | i | i) h
    · exact False.elim (h rfl)
    · exact (hcover i (σ i) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h,Or.inl rfl⟩)).imp (cp i) (cq (σ i))
    · exact (hcover i (τ i) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h,Or.inr rfl⟩)).imp (cp i) (cq (τ i))
  have card : C.card ≤ M.card :=
    (Finset.card_union_le _ _).trans ((Nat.add_le_add Finset.card_image_le Finset.card_image_le).trans hsize)
  have hm : CrossingMatching σ τ q M :=
    ⟨fun e he => (Finset.mem_filter.mp (hedge e he)).2,hfst,hsnd⟩
  rw [spinWeight_product]
  exact (rank_cover q C source (target σ τ) coupling cover).trans
    ((Nat.pow_le_pow_right (by decide : 0 < 2) card).trans ((matchingWidth_le σ τ q _).mp le_rfl M hm))

abbrev Spins (I : Type*) := I → Bool

def interactions {I : Type*} [Fintype I] (W : I → I → Bool → Bool → ℝ) :
    Matrix (Spins I) (Spins I) ℝ := Matrix.of fun x y => ∏ i, ∏ j, W i j (x i) (y j)

theorem peel {I : Type*} [Fintype I] [DecidableEq I] (W : I → I → Bool → Bool → ℝ) (r : I)
    (hn : ∀ i j a b, W i j a b ≠ 0)
    (leaf : ∀ j, j ≠ r → ∀ a b, W r j a b = 1)
    (det : W r r false false * W r r true true - W r r false true * W r r true false ≠ 0) :
    (interactions W).rank =
      2 * (interactions (fun i j : {i : I // i ≠ r} => W i.val j.val)).rank := by
  classical
  let J := {i : I // i ≠ r}
  let A := interactions (fun i j : J => W i.val j.val)
  let d := fun b (x : Spins J) => ∏ i : J, W i.val r (x i) b
  let D := fun b => Matrix.diagonal (d b)
  have nd (b) : IsUnit (D b).det := by
    simp only [D,Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun x _ => Finset.prod_ne_zero_iff.mpr fun i _ => hn _ _ _ _
  let T : Spins I ≃ Spins J ⊕ Spins J := (Equiv.funSplitAt r Bool).trans (Equiv.boolProdEquivSum _)
  have calcEntry (x y : Spins I) :
      interactions W x y = W r r (x r) (y r) * (d (y r) (fun i => x i.val) * A (fun i => x i.val) (fun j => y j.val)) := by
    change (∏ i, ∏ j, W i j (x i) (y j)) = _
    rw [Fintype.prod_eq_mul_prod_subtype_ne (fun i => ∏ j, W i j (x i) (y j)) r]
    have diag : (∏ j, W r j (x r) (y j)) = W r r (x r) (y r) := by
      rw [Fintype.prod_eq_mul_prod_subtype_ne _ r]
      have ones : ∀ i : {j : I // j ≠ r}, W r i.val (x r) (y i.val) = 1 := fun i => leaf i i.property _ _
      simp [ones]
    rw [diag]
    apply congrArg
    change (∏ i : J, ∏ j : I, W i.val j (x i.val) (y j)) =
      (∏ i : J, W i.val r (x i.val) (y r)) * ∏ i : J, ∏ j : J, W i.val j.val (x i.val) (y j.val)
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => Fintype.prod_eq_mul_prod_subtype_ne _ r
  let B := Matrix.fromBlocks (W r r false false • (D false*A)) (W r r false true • (D true*A))
    (W r r true false • (D false*A)) (W r r true true • (D true*A))
  have chart : interactions W = B.submatrix T T := by
    ext x y
    rw [calcEntry]
    by_cases hx : x r = true <;> by_cases hy : y r = true <;>
      simp [B,D,T,Equiv.funSplitAt,Equiv.piSplitAt,Equiv.boolProdEquivSum, Matrix.submatrix,
        Matrix.fromBlocks,Matrix.diagonal_mul, Bool.eq_false_of_not_eq_true, hx,hy] <;> exact Or.inl rfl
  rw [chart, Matrix.rank_submatrix, leafRank _ _ _ _ _ det _ _ (nd false) (nd true)]

def bond {I : Type*} (n : ℕ) (B T : I → I → Prop) [DecidableRel B] [DecidableRel T]
    (i j : I) (a b : Bool) : ℝ :=
  ((2^(2*n)+1 : ℕ) : ℝ) ^ ((if B i j ∧ a ≠ b then n+1 else 0) + (if T i j ∧ a = b then (n+1)^2 else 0))

def PartialPerm {I : Type*} (R : I → I → Prop) : Prop :=
  (∀ ⦃i j k⦄, R i j → R i k → j = k) ∧ (∀ ⦃i j k⦄, R i k → R j k → i = j)

theorem completed_rank {I : Type*} [Fintype I] [DecidableEq I] (n : ℕ)
    (B T : I → I → Prop) [DecidableRel B] [DecidableRel T] (hcard : Fintype.card I ≤ n)
    (bperm : PartialPerm B) (tperm : PartialPerm T) (full : ∀ i, ∃ j, T i j) :
    (interactions (bond n B T)).rank = Fintype.card (Spins I) := by
  classical
  let f i := (full i).choose
  have hf (i) : T i (f i) := (full i).choose_spec
  have hinj : Function.Injective f := by
    intro i j h
    exact tperm.2 (h ▸ hf i) (hf j)
  let π := Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩
  let p : Spins I ≃ Spins I :=
    ⟨fun y i => y (π.symm i), fun y i => y (π i), fun _ => by ext; simp, fun _ => by ext; simp⟩
  let eB := fun (x y : Spins I) (i j : I) => if B i j ∧ x i ≠ p y j then n+1 else 0
  let eT := fun (x y : Spins I) (i j : I) => if T i j ∧ x i = p y j then (n+1)^2 else 0
  let noise := fun x y => ∑ i, ∑ j, eB x y i j
  let E := fun (x y : Spins I) => noise x y + (n+1)^2 * (Finset.univ.filter (fun i => x i = y i)).card
  have reindex : (interactions (bond n B T)).submatrix (Equiv.refl _) p =
      Matrix.of (fun x y => ((2^(2*n)+1 : ℕ) : ℝ)^E x y) := by
    ext x y
    change (∏ i, ∏ j, ((2^(2*n)+1 : ℕ) : ℝ) ^ (eB x y i j + eT x y i j)) = _ ^ E x y
    simp only [Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib, E, noise]
    congr 2
    have row i : ∑ j, eT x y i j = if x i = y i then (n+1)^2 else 0 := by
      rw [Finset.sum_eq_single (π i)]
      · have eqv : p y (π i) = y i := by simp [p]
        simp [eT, show T i (π i) from hf i, eqv]
      · intro j _ h
        have hno : ¬T i j := fun hT => h (tperm.1 hT (hf i))
        simp [eT,hno]
      · simp
    simp_rw [row]
    rw [← Finset.sum_filter]
    simp [Nat.mul_comm]
  have noisecap (x y) : noise x y < (n+1)^2 := by
    have row i : ∑ j, eB x y i j ≤ n+1 := by
      by_cases h : ∃ j, B i j
      · obtain ⟨j,hj⟩ := h
        rw [Finset.sum_eq_single j]
        · dsimp [eB]; split <;> omega
        · intro k _ hne
          have hno : ¬B i k := fun hk => hne (bperm.1 hk hj)
          simp [eB,hno]
        · simp
      · simp [eB,not_exists.mp h]
    have bound := Finset.sum_le_sum (s := Finset.univ) (fun i _ => row i)
    change (∑ i, ∑ j, eB x y i j) < _
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      (lt_of_le_of_lt bound (by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        nlinarith [Nat.mul_le_mul_right (n+1) hcard] : (∑ _i : I, (n+1)) < (n+1)^2))
  have dh : (Matrix.of (fun x y => ((2^(2*n)+1 : ℕ) : ℝ)^E x y)).det ≠ 0 := by
    apply dominantPowers
    · simpa only [Spins,Fintype.card_fun,Fintype.card_bool] using
        Nat.lt_succ_of_le (Nat.pow_le_pow_right (by decide : 0 < 2) (show Fintype.card I ≤ 2*n by omega))
    · intro x y hne
      have diff : (Finset.univ.filter (fun i => x i = y i)).card < Fintype.card I := by
        apply lt_of_lt_of_eq _ Finset.card_univ
        apply Finset.card_lt_card
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _,?_⟩
        intro he
        apply hne
        funext i
        have hi : i ∈ Finset.univ.filter (fun i => x i = y i) := by rw [he]; exact Finset.mem_univ _
        exact (Finset.mem_filter.mp hi).2.symm
      have more := Nat.mul_le_mul_left ((n+1)^2) diff
      rw [Nat.mul_succ] at more
      have small := noisecap x y
      have di : (Finset.univ.filter (fun i => x i = x i)).card = Fintype.card I := by simp
      change noise x y + _ * _ < noise x x + _ * _
      rw [di]
      omega
  rw [← Matrix.rank_submatrix (interactions (bond n B T)) (Equiv.refl _) p, reindex, Matrix.rank_of_det_ne_zero dh]

theorem matched_rank {I : Type*} [Fintype I] [DecidableEq I] (n : ℕ)
    (B T : I → I → Prop) [DecidableRel B] [DecidableRel T] (hcard : Fintype.card I ≤ n)
    (bperm : PartialPerm B) (tperm : PartialPerm T) (matched : ∀ i, B i i ∨ T i i) :
    (interactions (bond n B T)).rank = Fintype.card (Spins I) := by
  classical
  by_cases full : ∀ i, ∃ j, T i j
  · exact completed_rank n B T hcard bperm tperm full
  push Not at full
  obtain ⟨r,hr⟩ := full
  have br : B r r := (matched r).resolve_right (hr r)
  let J := {i : I // i ≠ r}
  let B' := fun i j : J => B i.val j.val
  let T' := fun i j : J => T i.val j.val
  have less : Fintype.card J < Fintype.card I := Fintype.card_subtype_lt (x := r) (by simp)
  have bper' : PartialPerm B' :=
    ⟨fun _ _ _ h k => Subtype.ext (bperm.1 h k), fun _ _ _ h k => Subtype.ext (bperm.2 h k)⟩
  have tper' : PartialPerm T' :=
    ⟨fun _ _ _ h k => Subtype.ext (tperm.1 h k), fun _ _ _ h k => Subtype.ext (tperm.2 h k)⟩
  have ih := matched_rank (I := J) n B' T' (le_trans less.le hcard) bper' tper' (fun i => matched i)
  have hn : ∀ i j x y, bond n B T i j x y ≠ 0 := by intros; unfold bond; positivity
  have leaf : ∀ j, j ≠ r → ∀ a b, bond n B T r j a b = 1 := by
    intro j h a b
    have nb : ¬B r j := fun hb => h (bperm.1 hb br)
    simp [bond,nb,hr]
  have hB : (1:ℝ) < ((2^(2*n)+1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < 2^(2*n)+1 by have := Nat.two_pow_pos (2*n); omega)
  have pb : (1:ℝ) < ((2^(2*n)+1 : ℕ) : ℝ)^(n+1) := one_lt_pow₀ hB (by omega)
  have det : bond n B T r r false false * bond n B T r r true true -
      bond n B T r r false true * bond n B T r r true false ≠ 0 := by
    simp only [bond, br, hr r, false_and, true_and, Bool.false_eq_true, Bool.true_eq_false,
      ne_self_iff_false, not_true_eq_false, not_false_eq_true, ite_true, ite_false, add_zero, pow_zero, one_mul]
    simp only [if_pos (by decide : false ≠ true), if_pos (by decide : true ≠ false)]
    nlinarith [mul_self_lt_mul_self (by norm_num : (0:ℝ) ≤ 1) pb]
  rw [peel _ r hn leaf det]
  change 2 * (interactions (bond n B' T')).rank = _
  rw [ih]
  have he := Fintype.card_congr (Equiv.funSplitAt r Bool)
  simpa [Spins,J,Fintype.card_prod] using he.symm
termination_by Fintype.card I
decreasing_by exact less

abbrev Site (I : Type*) := Option (I ⊕ I)

def siteVal {I : Type*} (x y : Spins I) : Site I → Bool
  | none => false
  | some (.inl i) => x i
  | some (.inr j) => y j

def sitePair {I : Type*} : Site I → Site I → Option (I × I)
  | some (.inl i), some (.inr j) => some (i,j)
  | some (.inr j), some (.inl i) => some (i,j)
  | _,_ => none

def rightSite {I : Type*} : Site I → Bool
  | some (.inr _) => true
  | _ => false

def sideL {I : Type*} (s t : Site I) (h : Bool → Bool → ℝ) (x : Spins I) : ℝ :=
  if (sitePair s t).isNone && !(rightSite s || rightSite t) then
    h (siteVal x (fun _ => false) s) (siteVal x (fun _ => false) t) else 1

def sideR {I : Type*} (s t : Site I) (h : Bool → Bool → ℝ) (y : Spins I) : ℝ :=
  if (sitePair s t).isNone && (rightSite s || rightSite t) then
    h (siteVal (fun _ => false) y s) (siteVal (fun _ => false) y t) else 1

theorem single_coupling {I : Type*} [Fintype I] [DecidableEq I] (s t : Site I)
    (h : Bool → Bool → ℝ) (hs : ∀ a b, h a b = h b a) (x y : Spins I) :
    h (siteVal x y s) (siteVal x y t) = sideL s t h x * sideR s t h y *
      ∏ z : I × I, if sitePair s t = some z then h (x z.1) (y z.2) else 1 := by
  rcases s with _ | (s|s) <;> rcases t with _ | (t|t) <;>
    simp [sideL,sideR,siteVal,sitePair,rightSite,hs]

theorem all_couplings {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E] (a b : E → Site I)
    (h : E → Bool → Bool → ℝ) (hs : ∀ e x y, h e x y = h e y x)
    (hn : ∀ e x y, h e x y ≠ 0) :
    ∃ (L R : Spins I → ℝ), (∀ x, L x ≠ 0) ∧ (∀ y, R y ≠ 0) ∧
      ∀ x y, (∏ e, h e (siteVal x y (a e)) (siteVal x y (b e))) =
      L x * R y * interactions
        (fun i j x y => ∏ e, if sitePair (a e) (b e) = some (i,j) then h e x y else 1) x y := by
  classical
  refine ⟨fun x => ∏ e, sideL (a e) (b e) (h e) x,fun y => ∏ e, sideR (a e) (b e) (h e) y,?_,?_,?_⟩
  · intro x; apply Finset.prod_ne_zero_iff.mpr; intro e _; unfold sideL; split
    · exact hn _ _ _
    · exact one_ne_zero
  · intro y; apply Finset.prod_ne_zero_iff.mpr; intro e _; unfold sideR; split
    · exact hn _ _ _
    · exact one_ne_zero
  · intro x y
    simp_rw [single_coupling (a _) (b _) (h _) (hs _) x y, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_comm]
    exact (Fintype.prod_prod_type _)

theorem restricted_spin_rank {I U V : Type*} [Fintype I] [DecidableEq I] [Fintype U] [Fintype V]
    (F : U → V → ℤ) (l : I → U) (r : I → V) (M : Matrix I I ℝ)
    (hM : M.rank = Fintype.card I) (L R : I → ℝ)
    (hL : ∀ i, L i ≠ 0) (hR : ∀ i, R i ≠ 0)
    (fac : ∀ i j, (F (l i) (r j) : ℝ) = L i * R j * M i j) :
    Fintype.card I ≤ Module.finrank ℤ (Submodule.span ℤ (Set.range F)) := by
  classical
  let A := Matrix.of F
  let Z := A.submatrix l r
  let H := Z.map (Int.castRingHom ℝ)
  have hH : H = Matrix.diagonal L * M * Matrix.diagonal R := by
    ext i j
    simpa [Matrix.diagonal_mul,Matrix.mul_diagonal, mul_right_comm,H,Z,A] using fac i j
  have rk : H.rank = Fintype.card I := by
    rw [hH,Matrix.rank_mul_eq_left_of_isUnit_det,Matrix.rank_mul_eq_right_of_isUnit_det,hM]
    · simp [Matrix.det_diagonal,Finset.prod_ne_zero_iff,hL,isUnit_iff_ne_zero]
    · simp [Matrix.det_diagonal,Finset.prod_ne_zero_iff,hR,isUnit_iff_ne_zero]
  have dH := H.isUnit_iff_isUnit_det.mp (Matrix.mulVec_surjective_iff_isUnit.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr rk))
  have nz : Z.det ≠ 0 := by
    intro dz
    have zero : H.det = 0 := by
      change ((Int.castRingHom ℝ).mapMatrix Z).det = 0
      rw [← RingHom.map_det, dz, map_zero]
    exact (isUnit_iff_ne_zero.mp dH) zero
  have dn : (A.transpose.submatrix r l).det ≠ 0 := by simpa [Z, Matrix.transpose_submatrix] using
    (show Z.transpose.det ≠ 0 from by simpa using nz)
  have inequality := A.transpose.rank_submatrix_le r l
  rw [Matrix.rank_of_det_ne_zero dn,Matrix.rank_eq_finrank_span_cols] at inequality
  exact inequality

def mate {n : ℕ} (κ : Equiv.Perm (Fin n)) : Vertex n → Vertex n
  | (false,i) => (true,κ i)
  | (true,j) => (false,κ.symm j)

theorem mate_injective {n : ℕ} (κ : Equiv.Perm (Fin n)) : Function.Injective (mate κ) := by
  have hi : Function.Involutive (mate κ) := by rintro ⟨(_|_),i⟩ <;> simp [mate]
  exact hi.injective

theorem site_pair_iff {I : Type*} (s t : Site I) (i j : I) :
    sitePair s t = some (i,j) ↔
    (s = some (.inl i) ∧ t = some (.inr j)) ∨ (s = some (.inr j) ∧ t = some (.inl i)) := by
  rcases s with _ | (s|s) <;> rcases t with _ | (t|t) <;> simp [sitePair,and_comm]

theorem physical_pair_iff {n : ℕ} (κ : Equiv.Perm (Fin n)) (k : Fin n) (v w : Vertex n) :
    (((false,k) = v ∧ (true,κ k) = w) ∨ ((false,k) = w ∧ (true,κ k) = v)) ↔
      k = (if v.1 then w.2 else v.2) ∧ mate κ v = w := by
  rcases v with ⟨(_|_),i⟩ <;> rcases w with ⟨(_|_),j⟩ <;> simp [mate,Equiv.symm_apply_eq] <;> grind

theorem family_product {n : ℕ} {I : Type*} [DecidableEq I] (κ : Equiv.Perm (Fin n))
    (a b : I → Vertex n) (loc : Vertex n → Site I)
    (hl : ∀ v i, loc v = some (.inl i) ↔ v = a i)
    (hr : ∀ v i, loc v = some (.inr i) ↔ v = b i) (i j : I) (z : ℝ) :
    (∏ k, if sitePair (loc (false,k)) (loc (true,κ k)) = some (i,j) then z else 1) =
    if mate κ (a i) = b j then z else 1 := by
  have each k : sitePair (loc (false,k)) (loc (true,κ k)) = some (i,j) ↔
      k = (if (a i).1 then (b j).2 else (a i).2) ∧ mate κ (a i) = b j := by
    rw [site_pair_iff,hl,hr,hr,hl,physical_pair_iff]
  simp_rw [each]
  by_cases h : mate κ (a i) = b j <;> simp [h]

def firstEnd {n : ℕ} (q : Fin (n+1)) (e : Fin n × Fin n) : Vertex n :=
  if e.1.val < q.val then (false,e.1) else (true,e.2)
def secondEnd {n : ℕ} (q : Fin (n+1)) (e : Fin n × Fin n) : Vertex n :=
  if e.1.val < q.val then (true,e.2) else (false,e.1)

theorem matching_ends {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (q : Fin (n+1))
    (M : Finset (Fin n × Fin n)) (hm : CrossingMatching σ τ q M) :
    let a := fun e : M => firstEnd q e.val
    let b := fun e : M => secondEnd q e.val
    Function.Injective a ∧ Function.Injective b ∧
    (∀ e, (a e).2.val < q.val) ∧ (∀ e, ¬(b e).2.val < q.val) ∧
    (∀ e, mate σ (a e) = b e ∨ mate τ (a e) = b e) := by
  intro a b
  have sides (e : M) := (hm.1 e.val e.property).1
  have leftInj {i j : M} (h : i.val.1 = j.val.1) : i = j := Subtype.ext (hm.2.1 i.property j.property h)
  have rightInj {i j : M} (h : i.val.2 = j.val.2) : i = j := Subtype.ext (hm.2.2 i.property j.property h)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i j h
    by_cases hi : i.val.1.val < q.val <;> by_cases hj : j.val.1.val < q.val <;>
      simp [a,firstEnd,hi,hj] at h
    · exact leftInj h
    · exact rightInj h
  · intro i j h
    by_cases hi : i.val.1.val < q.val <;> by_cases hj : j.val.1.val < q.val <;>
      simp [b,secondEnd,hi,hj] at h
    · exact rightInj h
    · exact leftInj h
  · intro e
    by_cases h : e.val.1.val < q.val <;> simpa [a,firstEnd,h] using (show _ from sides e)
  · intro e
    by_cases h : e.val.1.val < q.val <;> simpa [b,secondEnd,h] using (show _ from sides e)
  · intro e
    rcases (hm.1 e.val e.property).2 with h|h
    · left; by_cases hh : e.val.1.val < q.val <;> simp [a,b,firstEnd,secondEnd,hh,mate,h]
    · right; by_cases hh : e.val.1.val < q.val <;> simp [a,b,firstEnd,secondEnd,hh,mate,h]

noncomputable def locate {I V : Type*} (a b : I → V) (v : V) : Site I := by
  classical
  exact if h : ∃ i, a i = v then some (.inl h.choose) else
    if h : ∃ j, b j = v then some (.inr h.choose) else none

theorem locate_correct {I V : Type*} (a b : I → V) (ha : Function.Injective a) (hb : Function.Injective b)
    (disj : ∀ i j, a i ≠ b j) :
    (∀ v i, locate a b v = some (.inl i) ↔ v = a i) ∧
    (∀ v i, locate a b v = some (.inr i) ↔ v = b i) := by
  classical
  have la i : locate a b (a i) = some (.inl i) := by
    let h : ∃ j, a j = a i := ⟨i,rfl⟩
    simp [locate,h,ha h.choose_spec]
  have lb i : locate a b (b i) = some (.inr i) := by
    let h : ∃ j, b j = b i := ⟨i,rfl⟩
    have hno : ¬ ∃ j, a j = b i := fun ⟨j,hj⟩ => disj j i hj
    simp [locate,h,hno,hb h.choose_spec]
  constructor
  · intro v i
    refine ⟨?_,fun he => he ▸ la i⟩
    intro he
    unfold locate at he
    split at he
    · rename_i h
      simpa [← Option.some.inj he |> Sum.inl.inj] using h.choose_spec.symm
    · split at he <;> simp at he
  · intro v i
    refine ⟨?_,fun he => he ▸ lb i⟩
    intro he
    unfold locate at he
    split at he
    · simp at he
    · split at he
      · rename_i h
        simpa [← Option.some.inj he |> Sum.inr.inj] using h.choose_spec.symm
      · simp at he

theorem filter_bit {A : Type*} [Fintype A] [DecidableEq A] (f : A → Bool) (v : A) :
    decide (v ∈ Finset.univ.filter (fun u => f u)) = f v := by simp

theorem matching_minor {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (q : Fin (n+1)) (M : Finset (Fin n × Fin n))
    (hm : CrossingMatching σ τ q M) :
    2^M.card ≤ Module.finrank ℤ (Submodule.span ℤ (Set.range (spinMatrix (spinWeight σ τ) q))) := by
  classical
  let I := ↥M
  let a := fun e : I => firstEnd q e.val
  let b := fun e : I => secondEnd q e.val
  obtain ⟨ha,hb,front,back,edge⟩ := matching_ends σ τ q M hm
  have fa : ∀ i, (a i).2.val < q.val := front
  have fb : ∀ i, ¬(b i).2.val < q.val := back
  have disj : ∀ i j, a i ≠ b j := fun i j eqv => fb j (eqv ▸ fa i)
  let loc := locate a b
  obtain ⟨hl,hr⟩ := locate_correct a b ha hb disj
  let l := fun x : Spins I => Finset.univ.filter (fun w : Before q => siteVal x (fun _ => false) (loc w.val))
  let r := fun y : Spins I => Finset.univ.filter (fun w : After q => siteVal (fun _ => false) y (loc w.val))
  have hjoin (x y : Spins I) : joinSpins q (l x,r y) = fun w => siteVal x y (loc w) := by
    funext w
    have lp (hw : w.2.val < q.val) : joinSpins q (l x,r y) w = siteVal x (fun _ => false) (loc w) := by
      rw [joinSpins,dif_pos hw]
      exact filter_bit (fun z : Before q => siteVal x (fun _ => false) (loc z.val)) ⟨w,hw⟩
    have rp (hw : ¬ w.2.val < q.val) : joinSpins q (l x,r y) w = siteVal (fun _ => false) y (loc w) := by
      rw [joinSpins,dif_neg hw]
      exact filter_bit (fun z : After q => siteVal (fun _ => false) y (loc z.val)) ⟨w,hw⟩
    cases hs : loc w with
    | none => by_cases h : w.2.val < q.val
              · simp [lp h,hs,siteVal]
              · simp [rp h,hs,siteVal]
    | some tag =>
      rcases tag with i|j
      · have he : w = a i := (hl w i).mp hs
        have hw : w.2.val < q.val := he ▸ fa i
        simp [lp hw,hs,siteVal]
      · have he : w = b j := (hr w j).mp hs
        have hw : ¬w.2.val < q.val := he ▸ fb j
        simp [rp hw,hs,siteVal]
  let B := fun i j : I => mate σ (a i) = b j
  let T := fun i j : I => mate τ (a i) = b j
  have pp (κ : Equiv.Perm (Fin n)) : PartialPerm (fun i j : I => mate κ (a i) = b j) :=
    ⟨fun _ _ _ h k => hb (h.symm.trans k), fun _ _ _ h k => ha (mate_injective κ (h.trans k.symm))⟩
  have cardI : Fintype.card I ≤ n := by
    have inject : Function.Injective (fun i : I => i.val.1) := fun i j eqv => Subtype.ext (hm.2.1 i.property j.property eqv)
    simpa using Fintype.card_le_of_injective _ inject
  have full := matched_rank n B T cardI (pp σ) (pp τ) edge
  let H := fun (e : EdgeSet n) x y => (coupling e x y : ℝ)
  have symmH : ∀ e x y, H e x y = H e y x := by
    rintro (i | i | i) x y <;> simp [H,coupling, eq_comm,ne_comm]
  have posH : ∀ e x y, H e x y ≠ 0 := by
    rintro (i | i | i) x y <;> dsimp [H,coupling] <;> split <;> push_cast <;> positivity
  obtain ⟨L,R,hL,hR,fac⟩ := all_couplings (fun e : EdgeSet n => loc (source e))
    (fun e => loc (target σ τ e)) H symmH posH
  have noRed i j : mate (Equiv.refl _) (a i) ≠ b j := by
    have ix : ∀ w : Vertex n, (mate (Equiv.refl _) w).2 = w.2 := by rintro ⟨(_|_),v⟩ <;> rfl
    intro he
    have eqv := congrArg (fun w : Vertex n => w.2) he
    rw [ix] at eqv
    exact fb j (eqv ▸ fa i)
  let W := fun (i j : I) (x y : Bool) => ∏ e : EdgeSet n,
    if sitePair (loc (source e)) (loc (target σ τ e)) = some (i,j) then H e x y else 1
  have Wbond : W = bond n B T := by
    funext i j x y
    dsimp only [W]
    rw [Fintype.prod_sum_type]
    rw [Fintype.prod_sum_type]
    let z₀ : ℝ := ((if x ≠ y then ((2^(2*n)+1 : ℕ) : ℤ)^1 else 1 : ℤ) : ℝ)
    let z₁ : ℝ := ((if x ≠ y then ((2^(2*n)+1 : ℕ) : ℤ)^(n+1) else 1 : ℤ) : ℝ)
    let z₂ : ℝ := ((if x = y then ((2^(2*n)+1 : ℕ) : ℤ)^((n+1)^2) else 1 : ℤ) : ℝ)
    let family := fun (κ : Equiv.Perm (Fin n)) (z : ℝ) => ∏ k,
      if sitePair (loc (false,k)) (loc (true,κ k)) = some (i,j) then z else 1
    change family (Equiv.refl _) z₀ * (family σ z₁ * family τ z₂) = _
    have oneFamily (κ z) : family κ z = if mate κ (a i) = b j then z else 1 :=
      family_product κ a b loc hl hr i j z
    rw [oneFamily,oneFamily,oneFamily]
    simp only [noRed,ite_false,one_mul]
    change (if B i j then z₁ else 1) * (if T i j then z₂ else 1) = _
    by_cases hB : B i j <;> by_cases hT : T i j <;> by_cases heq : x = y <;>
      simp [bond,hB,hT,heq,z₁,z₂]
  have hf : ∀ x y, (spinMatrix (spinWeight σ τ) q (l x) (r y) : ℝ) =
      L x * R y * interactions (bond n B T) x y := by
    intro x y
    have f := fac x y
    change _ = L x * R y * interactions W x y at f
    rw [Wbond] at f
    simpa only [spinMatrix,spinWeight_product,hjoin,Int.cast_prod,H] using f
  have rank := restricted_spin_rank _ l r _ full L R hL hR hf
  simpa [Spins,I] using rank

theorem all_cut_ranks : PhysicalCutRanks := by
  intro n σ τ q
  apply le_antisymm (cut_rank_upper σ τ q)
  exact (matchingWidth_le σ τ q _).mpr (fun M h => matching_minor σ τ q M h)

end PEqualNP.Outside.L_pcx_424_aux

theorem PEqualNP.Outside.L_pcx_424 : (∀ (n : ℕ) (σ τ : Equiv.Perm (Fin n)),
  let V := Bool × Fin n
  let X := V → Bool
  let Mask := Fin n → Bool × Bool
  let base := 2^(2*n)+1
  let idx := fun (a b c : ℕ) => a + (n+1)*b + (n+1)^2*c
  let red := fun (y : X) =>
    (Finset.univ.filter (fun i : Fin n => y (false,i) ≠ y (true,i))).card
  let blue := fun (y : X) =>
    (Finset.univ.filter (fun i : Fin n => y (false,i) ≠ y (true,σ i))).card
  let third := fun (y : X) =>
    (Finset.univ.filter (fun i : Fin n => y (false,i) = y (true,τ i))).card
  let good := fun (p : Mask) => (Finset.univ : Finset X).filter (fun y =>
    ∀ i, ((p i).1 = true → y (false,i) = false) ∧ ((p i).2 = true → y (true,i) = false))
  let Z := fun (p : Mask) => ∑ y ∈ good p, base^(idx (red y) (blue y) (third y))
  (∀ (p : Mask) (a b c : Fin (n+1)),
    (Z p / base^(idx a.val b.val c.val)) % base =
      ((good p).filter (fun y => red y = a.val ∧ blue y = b.val ∧ third y = c.val)).card) ∧
  ∀ w : Fin (n+1) → ℕ,
    (∃ (initial : Fin (w 0) → ℤ) (out : Fin (w (Fin.last n)) → ℤ)
      (T : (i : Fin n) → Bool × Bool → Fin (w i.castSucc) → Fin (w i.succ) → ℤ),
      ∀ p : Mask, ∃ run : (q : Fin (n+1)) → Fin (w q) → ℤ,
        run 0 = initial ∧
        (∀ (i : Fin n) (j : Fin (w i.succ)),
          run i.succ j = ∑ u : Fin (w i.castSucc), run i.castSucc u * T i (p i) u j) ∧
        (Z p : ℤ) = ∑ j : Fin (w (Fin.last n)), run (Fin.last n) j * out j) ↔
      ∀ (q : Fin (n+1)) (M : Finset (Fin n × Fin n)),
        (∀ e ∈ M, (decide (e.1.val < q.val) ≠ decide (e.2.val < q.val)) ∧
          (e.2 = σ e.1 ∨ e.2 = τ e.1)) →
        Set.InjOn Prod.fst (↑M : Set (Fin n × Fin n)) →
        Set.InjOn Prod.snd (↑M : Set (Fin n × Fin n)) → 2^M.card ≤ w q) := by
  intro n σ τ
  exact PEqualNP.Outside.L_pcx_424_aux.posted_of_cut_rank n σ τ
    (PEqualNP.Outside.L_pcx_424_aux.physical_reduction PEqualNP.Outside.L_pcx_424_aux.all_cut_ranks n σ τ)
