import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1154_aux

-- ============================================================
-- Section 1: Shift, Walsh characters, and Spectrum
-- ============================================================

def shiftB {n : Nat} (x z : Finset (Fin n)) : Finset (Fin n) := (x \ z) ∪ (z \ x)

lemma shiftB_eq_symmDiff {n : Nat} (x z : Finset (Fin n)) :
    shiftB x z = symmDiff x z := rfl

lemma shiftB_comm {n : Nat} (x z : Finset (Fin n)) : shiftB x z = shiftB z x := by
  simp [shiftB, Finset.union_comm]

lemma shiftB_self {n : Nat} (x : Finset (Fin n)) : shiftB x x = ∅ := by
  simp [shiftB]

lemma shiftB_invol {n : Nat} (x z : Finset (Fin n)) : shiftB x (shiftB x z) = z := by
  ext j
  simp only [shiftB, Finset.mem_union, Finset.mem_sdiff]
  by_cases hx : j ∈ x <;> by_cases hz : j ∈ z <;> simp [hx, hz]

lemma shiftB_invol_right {n : Nat} (x z : Finset (Fin n)) : shiftB (shiftB x z) z = x := by
  rw [shiftB_comm, shiftB_comm x z, shiftB_invol]

def chi {n : Nat} (T x : Finset (Fin n)) : Int := (-1 : Int) ^ (x ∩ T).card

lemma card_inter_add_mod_two {n : Nat} (s a b : Finset (Fin n)) :
    ((a ∩ s).card + (b ∩ s).card) % 2 = (s ∩ shiftB a b).card % 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert u s hu ih =>
    have h1 : a ∩ insert u s = if u ∈ a then insert u (a ∩ s) else a ∩ s := by
      ext j; by_cases h : u ∈ a <;> by_cases hj : j = u <;> simp [h, hj]
    have h2 : b ∩ insert u s = if u ∈ b then insert u (b ∩ s) else b ∩ s := by
      ext j; by_cases h : u ∈ b <;> by_cases hj : j = u <;> simp [h, hj]
    have h3 : insert u s ∩ shiftB a b =
        if u ∈ shiftB a b then insert u (s ∩ shiftB a b) else s ∩ shiftB a b := by
      ext j; by_cases h : u ∈ shiftB a b <;> by_cases hj : j = u <;> simp [h, hj]
    have hua : u ∉ a ∩ s := fun h => hu (Finset.mem_inter.mp h).2
    have hub : u ∉ b ∩ s := fun h => hu (Finset.mem_inter.mp h).2
    have husd : u ∉ s ∩ shiftB a b := fun h => hu (Finset.mem_inter.mp h).1
    have hsd_mem : u ∈ shiftB a b ↔ (u ∈ a ∧ u ∉ b) ∨ (u ∈ b ∧ u ∉ a) := by
      simp [shiftB, Finset.mem_union, Finset.mem_sdiff]
    rw [h1, h2, h3]
    by_cases ha : u ∈ a <;> by_cases hb : u ∈ b
    · have hnot : u ∉ shiftB a b := by simp [hsd_mem, ha, hb]
      simp only [ha, hb, hnot, ite_true, ite_false]
      have ca : (insert u (a ∩ s)).card = (a ∩ s).card + 1 := by simp [hua]
      have cb : (insert u (b ∩ s)).card = (b ∩ s).card + 1 := by simp [hub]
      rw [ca, cb]; omega
    · have hyes : u ∈ shiftB a b := by simp [hsd_mem, ha, hb]
      simp only [ha, hb, hyes, ite_true, ite_false]
      have ca : (insert u (a ∩ s)).card = (a ∩ s).card + 1 := by simp [hua]
      have cs : (insert u (s ∩ shiftB a b)).card = (s ∩ shiftB a b).card + 1 := by simp [husd]
      rw [ca, cs]; omega
    · have hyes : u ∈ shiftB a b := by simp [hsd_mem, ha, hb]
      simp only [ha, hb, hyes, ite_true, ite_false]
      have cb : (insert u (b ∩ s)).card = (b ∩ s).card + 1 := by simp [hub]
      have cs : (insert u (s ∩ shiftB a b)).card = (s ∩ shiftB a b).card + 1 := by simp [husd]
      rw [cb, cs]; omega
    · have hnot : u ∉ shiftB a b := by simp [hsd_mem, ha, hb]
      simp only [ha, hb, hnot, ite_true, ite_false]
      exact ih

lemma chi_shift {n : Nat} (T x z : Finset (Fin n)) :
    chi T (shiftB x z) = chi T x * chi T z := by
  simp only [chi, ← pow_add]
  have hmod : ((x ∩ T).card + (z ∩ T).card) % 2 = (shiftB x z ∩ T).card % 2 := by
    rw [Finset.inter_comm (shiftB x z) T]
    exact card_inter_add_mod_two T x z
  rw [← Nat.div_add_mod ((x ∩ T).card + (z ∩ T).card) 2,
      ← Nat.div_add_mod (shiftB x z ∩ T).card 2, hmod]
  simp only [pow_add, pow_mul, show (-1 : Int) ^ 2 = 1 by decide, one_pow, one_mul]

lemma sum_powerset_chi {n : Nat} (B S : Finset (Fin n)) (hSB : S ⊆ B) :
    B.powerset.sum (fun q => (-1 : Int) ^ (q ∩ S).card) =
      if S = ∅ then (2 : Int) ^ B.card else 0 := by
  induction B using Finset.induction_on generalizing S with
  | empty =>
    have hS : S = ∅ := Finset.subset_empty.mp hSB
    subst hS; simp
  | insert u B hu ih =>
    have hdisj : Disjoint B.powerset (B.powerset.image (insert u)) := by
      rw [Finset.disjoint_left]
      intro q hq1 hq2
      rcases Finset.mem_image.mp hq2 with ⟨r, _, rfl⟩
      exact hu (Finset.mem_powerset.mp hq1 (Finset.mem_insert_self u r))
    have hinj : Set.InjOn (insert u) (B.powerset : Set (Finset (Fin n))) := by
      intro q1 hq1 q2 hq2 heq
      have hu1 : u ∉ q1 := fun h => hu (Finset.mem_powerset.mp hq1 h)
      have hu2 : u ∉ q2 := fun h => hu (Finset.mem_powerset.mp hq2 h)
      ext v
      by_cases hvu : v = u
      · subst hvu; simp [hu1, hu2]
      · have := Finset.ext_iff.mp heq v; simp [hvu] at this; exact this
    rw [Finset.powerset_insert, Finset.sum_union hdisj, Finset.sum_image hinj]
    by_cases huS : u ∈ S
    · have hS_ne : S ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨u, huS⟩
      simp only [hS_ne, ite_false]
      have hneg : B.powerset.sum (fun q => (-1 : Int) ^ (insert u q ∩ S).card) =
          -(B.powerset.sum (fun q => (-1 : Int) ^ (q ∩ S).card)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun q hq => ?_
        have huq : u ∉ q := fun h => hu (Finset.mem_powerset.mp hq h)
        have hinter : insert u q ∩ S = insert u (q ∩ S) := by
          ext v; by_cases hvu : v = u <;> simp [hvu, huS]
        have huqS : u ∉ q ∩ S := fun h => huq (Finset.mem_inter.mp h).1
        have hcard : (insert u (q ∩ S)).card = (q ∩ S).card + 1 := by simp [huqS]
        rw [hinter, hcard, pow_succ]; ring
      rw [hneg]; ring
    · have hSB' : S ⊆ B := by
        intro v hv
        rcases Finset.mem_insert.mp (hSB hv) with rfl | hvB
        · exact False.elim (huS hv)
        · exact hvB
      have hsame : B.powerset.sum (fun q => (-1 : Int) ^ (insert u q ∩ S).card) =
          B.powerset.sum (fun q => (-1 : Int) ^ (q ∩ S).card) :=
        Finset.sum_congr rfl fun q _ => by
          have hinter : insert u q ∩ S = q ∩ S := by
            ext v; by_cases hvu : v = u <;> simp [hvu, huS]
          rw [hinter]
      rw [hsame, ih S hSB']
      have hcard : (insert u B).card = B.card + 1 := by simp [hu]
      rw [hcard, pow_succ]
      by_cases hS0 : S = ∅ <;> simp [hS0] <;> ring

lemma sum_chi_mul_chi {n : Nat} (z x : Finset (Fin n)) :
    (Finset.univ : Finset (Finset (Fin n))).sum (fun T => chi T z * chi T x) =
      if x = z then (2 : Int) ^ n else 0 := by
  have h1 : ∀ T : Finset (Fin n),
      chi T z * chi T x = (-1 : Int) ^ (T ∩ shiftB z x).card := by
    intro T
    rw [← chi_shift, chi, Finset.inter_comm]
  simp_rw [h1]
  have huniv : (Finset.univ : Finset (Finset (Fin n))) = (Finset.univ : Finset (Fin n)).powerset := by
    ext T; simp
  rw [huniv, sum_powerset_chi Finset.univ (shiftB z x) (Finset.subset_univ _)]
  have hsd : shiftB z x = ∅ ↔ x = z := by
    rw [shiftB_eq_symmDiff, ← Finset.bot_eq_empty, symmDiff_eq_bot, eq_comm]
  simp [hsd]

-- Definitions matching the statement
def spectrumB {n k : Nat} (seed : Fin k → Finset (Fin n) → Bool) (i : Fin k) (T : Finset (Fin n)) : Int :=
  ((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i x)).sum
    (fun x => (-1 : Int) ^ (x ∩ T).card)

def divisorB {n k : Nat} (seed : Fin k → Finset (Fin n) → Bool) (T : Finset (Fin n)) : Nat :=
  (Finset.univ : Finset (Fin k)).gcd (fun i => (spectrumB seed i T).natAbs)

def oddSeedB {n k : Nat} (seed : Fin k → Finset (Fin n) → Bool) : Prop :=
  ∃ i : Fin k, Odd (((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i x)).card)

def InSpan {n k : Nat} (seed : Fin k → Finset (Fin n) → Bool) (f : Finset (Fin n) → Int) : Prop :=
  ∃ c : Fin k → Finset (Fin n) → Int, ∀ x : Finset (Fin n),
    (Finset.univ : Finset (Fin k)).sum
      (fun i => ((Finset.univ : Finset (Finset (Fin n))).filter (fun z => seed i (shiftB x z))).sum (c i)) =
      f x

def synthesizesB {n k : Nat} (seed : Fin k → Finset (Fin n) → Bool) (u : Nat) : Prop :=
  ∀ y : Finset (Fin n), InSpan seed (fun x => if x = y then (u : Int) else 0)

def kernelSizeB {n k : Nat} (seed : Fin k → Finset (Fin n) → Bool) (m : Nat) : Nat :=
  ((Finset.univ : Finset (Finset (Fin n) → Fin m)).filter (fun d =>
    ∀ i : Fin k, ∀ z : Finset (Fin n),
      (((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i (shiftB x z))).sum
        (fun x => (d x).val)) % m = 0)).card

lemma spectrum_parity {n k : Nat} (seed : Fin k → Finset (Fin n) → Bool) (i : Fin k) (T : Finset (Fin n)) :
    (spectrumB seed i T) % 2 =
      ((((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i x)).card : Int)) % 2 := by
  have h1 : ∀ s : Finset (Finset (Fin n)),
      (∑ x ∈ s, (-1 : Int) ^ (x ∩ T).card) % 2 = (s.card : Int) % 2 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert u s hu ih =>
      rw [Finset.sum_insert hu, Finset.card_insert_of_notMem hu, Nat.cast_add, Nat.cast_one]
      have hneg : ((-1 : Int) ^ (u ∩ T).card) % 2 = 1 := by
        rcases Nat.even_or_odd (u ∩ T).card with ⟨r, hr⟩ | ⟨r, hr⟩
        · rw [hr, ← two_mul, pow_mul]; norm_num
        · rw [hr, pow_add, pow_mul]; norm_num
      omega
  exact h1 _

lemma odd_natAbs_spectrum_iff {n k : Nat} (seed : Fin k → Finset (Fin n) → Bool)
    (i : Fin k) (T : Finset (Fin n)) :
    Odd (spectrumB seed i T).natAbs ↔
      Odd (((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i x)).card) := by
  have hp := spectrum_parity seed i T
  have habs : ((spectrumB seed i T).natAbs : Int) % 2 = (spectrumB seed i T) % 2 := by
    rcases Int.natAbs_eq (spectrumB seed i T) with h | h
    · rw [← h]
    · rw [h]; omega
  rw [← habs] at hp
  rw [Nat.odd_iff, Nat.odd_iff]
  omega

lemma odd_divisor_of_oddSeed {n k : Nat} (seed : Fin k → Finset (Fin n) → Bool)
    (hodd : oddSeedB seed) (T : Finset (Fin n)) : Odd (divisorB seed T) := by
  rcases hodd with ⟨i, hi⟩
  have hiT : Odd (spectrumB seed i T).natAbs := (odd_natAbs_spectrum_iff seed i T).mpr hi
  have hdvd : divisorB seed T ∣ (spectrumB seed i T).natAbs := Finset.gcd_dvd (Finset.mem_univ i)
  rcases hdvd with ⟨q, hq⟩
  rw [hq] at hiT
  by_contra hnot
  rw [Nat.odd_iff] at hnot
  have h2 : 2 ∣ divisorB seed T := Nat.dvd_of_mod_eq_zero (by omega)
  rcases dvd_mul_of_dvd_left h2 q with ⟨r, hr⟩
  rcases hiT with ⟨t, ht⟩
  omega

lemma even_divisor_empty_of_not_oddSeed {n k : Nat} (seed : Fin k → Finset (Fin n) → Bool)
    (hno : ¬ oddSeedB seed) : 2 ∣ divisorB seed ∅ := by
  refine Finset.dvd_gcd fun i _ => ?_
  have hnot : ¬ Odd (((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i x)).card) :=
    fun h => hno ⟨i, h⟩
  have hnotS : ¬ Odd (spectrumB seed i ∅).natAbs := mt (odd_natAbs_spectrum_iff seed i ∅).mp hnot
  rw [Nat.odd_iff] at hnotS
  omega

-- Convolution with a character
lemma sum_shift_chi {n k : Nat} (seed : Fin k → Finset (Fin n) → Bool)
    (i : Fin k) (T x : Finset (Fin n)) :
    ((Finset.univ : Finset (Finset (Fin n))).filter (fun z => seed i (shiftB x z))).sum (chi T) =
      spectrumB seed i T * chi T x := by
  have hbij : ((Finset.univ : Finset (Finset (Fin n))).filter (fun z => seed i (shiftB x z))).sum (chi T) =
      ((Finset.univ : Finset (Finset (Fin n))).filter (fun w => seed i w)).sum (fun w => chi T (shiftB x w)) := by
    refine Finset.sum_bij (fun z _ => shiftB x z) ?_ ?_ ?_ ?_
    · intro z hz; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩
    · intro z1 _ z2 _ heq
      have := congrArg (shiftB x) heq
      simpa [shiftB_invol] using this
    · intro w hw
      refine ⟨shiftB x w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, shiftB_invol x w⟩
      rw [shiftB_invol]; exact (Finset.mem_filter.mp hw).2
    · intro z _; rw [shiftB_invol]
  rw [hbij]
  have hmul : ∀ w : Finset (Fin n), chi T (shiftB x w) = chi T w * chi T x := by
    intro w; rw [chi_shift, mul_comm]
  simp_rw [hmul, ← Finset.sum_mul]
  rfl

-- ============================================================
-- Section 2: InSpan Algebra and Matrix Determinant
-- ============================================================

lemma inSpan_zero {n k : Nat} (seed : Fin k → Finset (Fin n) → Bool) :
    InSpan seed (fun _ => 0) :=
  ⟨fun _ _ => 0, fun _ => by simp⟩

lemma inSpan_add {n k : Nat} {seed : Fin k → Finset (Fin n) → Bool} {f g : Finset (Fin n) → Int}
    (hf : InSpan seed f) (hg : InSpan seed g) : InSpan seed (fun x => f x + g x) := by
  rcases hf with ⟨cf, hcf⟩
  rcases hg with ⟨cg, hcg⟩
  refine ⟨fun i z => cf i z + cg i z, fun x => ?_⟩
  simp_rw [Finset.sum_add_distrib]
  rw [hcf x, hcg x]

lemma inSpan_smul {n k : Nat} {seed : Fin k → Finset (Fin n) → Bool} {f : Finset (Fin n) → Int}
    (a : Int) (hf : InSpan seed f) : InSpan seed (fun x => a * f x) := by
  rcases hf with ⟨cf, hcf⟩
  refine ⟨fun i z => a * cf i z, fun x => ?_⟩
  simp_rw [← Finset.mul_sum]
  rw [hcf x]

lemma inSpan_sum {n k : Nat} {ι : Type*} {seed : Fin k → Finset (Fin n) → Bool}
    (s : Finset ι) (f : ι → Finset (Fin n) → Int)
    (hf : ∀ i ∈ s, InSpan seed (f i)) :
    InSpan seed (fun x => s.sum (fun i => f i x)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using inSpan_zero seed
  | insert i s hi ih =>
    rcases inSpan_add (hf i (Finset.mem_insert_self i s))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))) with ⟨c, hc⟩
    exact ⟨c, fun x => by dsimp only; rw [hc x, Finset.sum_insert hi]⟩

lemma inSpan_gcd_nat {n k : Nat} {ι : Type*} [DecidableEq ι]
    {seed : Fin k → Finset (Fin n) → Bool} {f : Finset (Fin n) → Int}
    (s : Finset ι) (g : ι → Nat)
    (hg : ∀ i ∈ s, InSpan seed (fun x => (g i : Int) * f x)) :
    InSpan seed (fun x => ((s.gcd g : Nat) : Int) * f x) := by
  induction s using Finset.induction_on with
  | empty => simpa using inSpan_zero seed
  | insert i s hi ih =>
    have h1 := hg i (Finset.mem_insert_self i s)
    have h2 := ih (fun j hj => hg j (Finset.mem_insert_of_mem hj))
    have hbez := Nat.gcd_eq_gcd_ab (g i) (s.gcd g)
    rcases inSpan_add (inSpan_smul (Nat.gcdA (g i) (s.gcd g)) h1)
      (inSpan_smul (Nat.gcdB (g i) (s.gcd g)) h2) with ⟨c, hc⟩
    refine ⟨c, fun x => ?_⟩
    rw [hc x, Finset.gcd_insert]
    change _ = ((Nat.gcd (g i) (s.gcd g) : Nat) : Int) * f x
    rw [hbez]; ring

lemma inSpan_divisor_chi {n k : Nat} (seed : Fin k → Finset (Fin n) → Bool) (T : Finset (Fin n)) :
    InSpan seed (fun x => (divisorB seed T : Int) * chi T x) := by
  refine inSpan_gcd_nat (Finset.univ : Finset (Fin k)) (fun i => (spectrumB seed i T).natAbs) ?_
  intro i _
  have hraw : InSpan seed (fun x => spectrumB seed i T * chi T x) := by
    refine ⟨fun j z => if j = i then chi T z else 0, fun x => ?_⟩
    rw [Finset.sum_eq_single i]
    · simp only [ite_true]; exact sum_shift_chi seed i T x
    · intro j _ hji; simp [hji]
    · intro h; exact False.elim (h (Finset.mem_univ i))
  rcases Int.natAbs_eq (spectrumB seed i T) with h | h
  · rcases hraw with ⟨c, hc⟩
    exact ⟨c, fun x => by rw [hc x, ← h]⟩
  · rcases inSpan_smul (-1) hraw with ⟨c, hc⟩
    refine ⟨c, fun x => ?_⟩
    dsimp only at hc ⊢
    have hneg : -1 * spectrumB seed i T = ((spectrumB seed i T).natAbs : Int) := by linarith
    rw [hc x, ← mul_assoc, hneg]

-- Matrix diagonalization: det(A_i) = ∏ T, spectrumB seed i T
def convMat {n k : Nat} (seed : Fin k → Finset (Fin n) → Bool) (i : Fin k) :
    Matrix (Finset (Fin n)) (Finset (Fin n)) Int :=
  fun x z => if seed i (shiftB x z) then 1 else 0

def walshMat (n : Nat) : Matrix (Finset (Fin n)) (Finset (Fin n)) Int :=
  fun T x => chi T x

lemma walshMat_mul_self (n : Nat) :
    walshMat n * walshMat n = ((2 : Int) ^ n) • (1 : Matrix (Finset (Fin n)) (Finset (Fin n)) Int) := by
  ext T x
  simp only [Matrix.mul_apply, walshMat, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  have hcomm : ∀ z : Finset (Fin n), chi T z * chi z x = chi z T * chi z x := by
    intro z; simp [chi, Finset.inter_comm]
  simp_rw [hcomm]
  rw [sum_chi_mul_chi T x]
  by_cases h : T = x <;> simp [h, eq_comm]

lemma walshMat_mul_convMat {n k : Nat} (seed : Fin k → Finset (Fin n) → Bool) (i : Fin k) :
    walshMat n * convMat seed i = Matrix.diagonal (fun T => spectrumB seed i T) * walshMat n := by
  ext T z
  rw [Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, walshMat, convMat]
  have h1 : (Finset.univ : Finset (Finset (Fin n))).sum
      (fun x => chi T x * if seed i (shiftB x z) then (1 : Int) else 0) =
      ((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i (shiftB z x))).sum (chi T) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [shiftB_comm x z]
    by_cases h : seed i (shiftB z x) = true <;> simp [h]
  rw [h1, sum_shift_chi]

lemma convMat_det {n k : Nat} (seed : Fin k → Finset (Fin n) → Bool) (i : Fin k) :
    (convMat seed i).det = (Finset.univ : Finset (Finset (Fin n))).prod (fun T => spectrumB seed i T) := by
  have hmul : walshMat n * convMat seed i * walshMat n =
      Matrix.diagonal (fun T => spectrumB seed i T) * (walshMat n * walshMat n) := by
    rw [walshMat_mul_convMat, Matrix.mul_assoc]
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hdet
  have hsq : (walshMat n * walshMat n).det ≠ 0 := by
    rw [walshMat_mul_self, Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (pow_ne_zero _ (by decide))
  rw [Matrix.det_mul] at hsq
  have hcancel : (walshMat n).det * (walshMat n).det * (convMat seed i).det =
      (walshMat n).det * (walshMat n).det *
        (Finset.univ : Finset (Finset (Fin n))).prod (fun T => spectrumB seed i T) := by
    calc (walshMat n).det * (walshMat n).det * (convMat seed i).det
        = (walshMat n).det * (convMat seed i).det * (walshMat n).det := by ring
      _ = ((Finset.univ : Finset (Finset (Fin n))).prod (fun T => spectrumB seed i T)) *
            ((walshMat n).det * (walshMat n).det) := hdet
      _ = (walshMat n).det * (walshMat n).det *
            (Finset.univ : Finset (Finset (Fin n))).prod (fun T => spectrumB seed i T) := by ring
  exact mul_left_cancel₀ hsq hcancel

lemma odd_convMat_det {n k : Nat} (seed : Fin k → Finset (Fin n) → Bool) (i : Fin k)
    (hi : Odd (((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i x)).card)) :
    Odd (convMat seed i).det.natAbs := by
  rw [convMat_det]
  have hprod : ∀ s : Finset (Finset (Fin n)),
      Odd (s.prod (fun T => spectrumB seed i T)).natAbs := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert T s hT ih =>
      rw [Finset.prod_insert hT, Int.natAbs_mul]
      exact Odd.mul ((odd_natAbs_spectrum_iff seed i T).mpr hi) ih
  exact hprod Finset.univ

lemma inSpan_convMat_det_delta {n k : Nat} (seed : Fin k → Finset (Fin n) → Bool)
    (i : Fin k) (y : Finset (Fin n)) :
    InSpan seed (fun x => (convMat seed i).det * (if x = y then (1 : Int) else 0)) := by
  refine ⟨fun j z => if j = i then (convMat seed i).adjugate z y else 0, fun x => ?_⟩
  rw [Finset.sum_eq_single i]
  · simp only [ite_true]
    have hmul := congrFun (congrFun (Matrix.mul_adjugate (convMat seed i)) x) y
    simp only [Matrix.mul_apply, convMat, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at hmul
    rw [← hmul, Finset.sum_filter]
    refine Finset.sum_congr rfl fun z _ => by
      by_cases h : seed i (shiftB x z) = true <;> simp [h]
  · intro j _ hji; simp [hji]
  · intro h; exact False.elim (h (Finset.mem_univ i))

-- ============================================================
-- Section 3: Parts 1 and 2 (Synthesizes Characterization)
-- ============================================================

lemma synthesizes_imp_dvd {n k : Nat} (seed : Fin k → Finset (Fin n) → Bool) {u : Nat}
    (hs : synthesizesB seed u) (T : Finset (Fin n)) : divisorB seed T ∣ u := by
  rcases hs ∅ with ⟨c, hc⟩
  have hhat : (Finset.univ : Finset (Finset (Fin n))).sum
      (fun x => chi T x * (Finset.univ : Finset (Fin k)).sum
        (fun i => ((Finset.univ : Finset (Finset (Fin n))).filter (fun z => seed i (shiftB x z))).sum (c i))) =
      (u : Int) := by
    have h1 : (Finset.univ : Finset (Finset (Fin n))).sum
        (fun x => chi T x * (if x = ∅ then (u : Int) else 0)) = (u : Int) := by
      rw [Finset.sum_eq_single (∅ : Finset (Fin n))]
      · simp [chi]
      · intro x _ hx; simp [hx]
      · intro h; exact False.elim (h (Finset.mem_univ _))
    simpa [hc] using h1
  have hswap : (Finset.univ : Finset (Finset (Fin n))).sum
      (fun x => chi T x * (Finset.univ : Finset (Fin k)).sum
        (fun i => ((Finset.univ : Finset (Finset (Fin n))).filter (fun z => seed i (shiftB x z))).sum (c i))) =
      (Finset.univ : Finset (Fin k)).sum
        (fun i => spectrumB seed i T *
          (Finset.univ : Finset (Finset (Fin n))).sum (fun z => c i z * chi T z)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    have hinner : (Finset.univ : Finset (Finset (Fin n))).sum
        (fun x => if seed i (shiftB x z) = true then chi T x * c i z else 0) =
        c i z * ((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i (shiftB z x))).sum (chi T) := by
      rw [Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [shiftB_comm x z]
      by_cases h : seed i (shiftB z x) = true <;> simp [h] <;> ring
    rw [hinner, sum_shift_chi]
    ring
  rw [hswap] at hhat
  have hdvd_int : (divisorB seed T : Int) ∣ (u : Int) := by
    rw [← hhat]
    refine Finset.dvd_sum fun i _ => ?_
    have hdi : divisorB seed T ∣ (spectrumB seed i T).natAbs := Finset.gcd_dvd (Finset.mem_univ i)
    have hdi_int : (divisorB seed T : Int) ∣ spectrumB seed i T := by
      exact Int.ofNat_dvd_left.mpr hdi
    exact dvd_mul_of_dvd_left hdi_int _
  exact Int.ofNat_dvd.mp hdvd_int

lemma synthesizes_of_oddSeed_dvd {n k : Nat} (seed : Fin k → Finset (Fin n) → Bool)
    (hodd : oddSeedB seed) {u : Nat}
    (hdvd : (Finset.univ : Finset (Finset (Fin n))).lcm (divisorB seed) ∣ u) :
    synthesizesB seed u := by
  intro y
  have hpow2 : InSpan seed (fun x => (2 : Int) ^ n * (if x = y then (u : Int) else 0)) := by
    have heach : ∀ T ∈ (Finset.univ : Finset (Finset (Fin n))),
        InSpan seed (fun x => (chi T y * (u : Int)) * chi T x) := by
      intro T _
      have hdT : divisorB seed T ∣ u := dvd_trans (Finset.dvd_lcm (Finset.mem_univ T)) hdvd
      rcases hdT with ⟨q, hq⟩
      have h1 := inSpan_smul (chi T y * (q : Int)) (inSpan_divisor_chi seed T)
      rcases h1 with ⟨c, hc⟩
      refine ⟨c, fun x => ?_⟩
      rw [hc x, hq]; push_cast; ring
    rcases inSpan_sum (Finset.univ : Finset (Finset (Fin n)))
      (fun T x => (chi T y * (u : Int)) * chi T x) heach with ⟨c, hc⟩
    refine ⟨c, fun x => ?_⟩
    dsimp only at hc ⊢
    rw [hc x]
    have hpull : (Finset.univ : Finset (Finset (Fin n))).sum (fun T => chi T y * (u : Int) * chi T x) =
        (u : Int) * (Finset.univ : Finset (Finset (Fin n))).sum (fun T => chi T y * chi T x) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun T _ => by ring
    rw [hpull, sum_chi_mul_chi y x]
    by_cases hxy : x = y <;> simp [hxy] <;> ring
  rcases hodd with ⟨i0, hi0⟩
  have hdet_raw : InSpan seed (fun x => ((convMat seed i0).det.natAbs : Int) *
      (if x = y then (u : Int) else 0)) := by
    have h1 := inSpan_smul (u : Int) (inSpan_convMat_det_delta seed i0 y)
    rcases Int.natAbs_eq (convMat seed i0).det with h | h
    · rcases h1 with ⟨c, hc⟩
      exact ⟨c, fun x => by rw [hc x, ← h]; by_cases hxy : x = y <;> simp [hxy] <;> ring⟩
    · rcases inSpan_smul (-1) h1 with ⟨c, hc⟩
      exact ⟨c, fun x => by rw [hc x, h]; by_cases hxy : x = y <;> simp [hxy] <;> ring⟩
  let D : Nat := (convMat seed i0).det.natAbs
  have hDodd : Odd D := odd_convMat_det seed i0 hi0
  have hcop : Nat.Coprime D (2 ^ n) := Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hDodd)
  have hbez := Nat.gcd_eq_gcd_ab D (2 ^ n)
  rw [hcop.gcd_eq_one] at hbez
  rcases inSpan_add (inSpan_smul (Nat.gcdA D (2 ^ n)) hdet_raw)
    (inSpan_smul (Nat.gcdB D (2 ^ n)) hpow2) with ⟨c, hc⟩
  refine ⟨c, fun x => ?_⟩
  rw [hc x]
  have h1 : (1 : Int) = (D : Int) * Nat.gcdA D (2 ^ n) + (2 : Int) ^ n * Nat.gcdB D (2 ^ n) := by
    simpa using hbez
  calc Nat.gcdA D (2 ^ n) * ((D : Int) * if x = y then (u : Int) else 0) +
        Nat.gcdB D (2 ^ n) * ((2 : Int) ^ n * if x = y then (u : Int) else 0)
      = ((D : Int) * Nat.gcdA D (2 ^ n) + (2 : Int) ^ n * Nat.gcdB D (2 ^ n)) *
          (if x = y then (u : Int) else 0) := by ring
    _ = 1 * (if x = y then (u : Int) else 0) := by rw [← h1]
    _ = if x = y then (u : Int) else 0 := one_mul _

-- ============================================================
-- Section 4: Part 3 (Kernel Size via CRT + Walsh over ZMod b)
-- ============================================================

def zmodKernel {n k : Nat} (seed : Fin k → Finset (Fin n) → Bool) (m : Nat) [NeZero m] :
    Finset (Finset (Fin n) → ZMod m) :=
  (Finset.univ : Finset (Finset (Fin n) → ZMod m)).filter (fun d =>
    ∀ i : Fin k, ∀ z : Finset (Fin n),
      ((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i (shiftB x z))).sum d = 0)

lemma kernelSizeB_eq_zmodKernel {n k : Nat} (seed : Fin k → Finset (Fin n) → Bool)
    (m : Nat) [NeZero m] :
    kernelSizeB seed m = (zmodKernel seed m).card := by
  have hm : 0 < m := NeZero.pos m
  unfold kernelSizeB zmodKernel
  refine Finset.card_bij (fun d _ x => (d x).val) ?_ ?_ ?_
  · intro d hd
    have hd' := (Finset.mem_filter.mp hd).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i z => ?_⟩
    have hsum : (((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i (shiftB x z))).sum
        (fun x => ((d x).val : ZMod m))) =
        ((((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i (shiftB x z))).sum
          (fun x => (d x).val) : Nat) : ZMod m) := by simp
    rw [hsum, ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_of_mod_eq_zero (hd' i z)
  · intro d1 _ d2 _ heq
    funext x
    apply Fin.ext
    have hx := congrFun heq x
    have h1 := congrArg ZMod.val hx
    rw [ZMod.val_natCast_of_lt (d1 x).isLt, ZMod.val_natCast_of_lt (d2 x).isLt] at h1
    exact h1
  · intro g hg
    have hg' := (Finset.mem_filter.mp hg).2
    refine ⟨fun x => ⟨(g x).val, ZMod.val_lt (g x)⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · intro i z
      apply Nat.mod_eq_zero_of_dvd
      rw [← ZMod.natCast_eq_zero_iff]
      have hcast : ((((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i (shiftB x z))).sum
          (fun x => (g x).val) : Nat) : ZMod m) =
          ((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i (shiftB x z))).sum g := by
        simp [ZMod.natCast_zmod_val]
      rw [hcast]
      exact hg' i z
    · funext x; exact ZMod.natCast_zmod_val (g x)

lemma zmodKernel_mul_coprime {n k : Nat} (seed : Fin k → Finset (Fin n) → Bool)
    {a b : Nat} [NeZero a] [NeZero b] (hcop : Nat.Coprime a b) :
    letI : NeZero (a * b) := ⟨mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
    (zmodKernel seed (a * b)).card = (zmodKernel seed a).card * (zmodKernel seed b).card := by
  letI : NeZero (a * b) := ⟨mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  let e : ZMod (a * b) ≃+* ZMod a × ZMod b := ZMod.chineseRemainder hcop
  rw [← Finset.card_product]
  refine Finset.card_bij (fun d _ => (fun x => (e (d x)).1, fun x => (e (d x)).2)) ?_ ?_ ?_
  · intro d hd
    have hd' := (Finset.mem_filter.mp hd).2
    refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i z => ?_⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i z => ?_⟩⟩
    · have h1 := congrArg (fun v => (e v).1) (hd' i z)
      simpa [map_sum, map_zero, Prod.fst_sum] using h1
    · have h1 := congrArg (fun v => (e v).2) (hd' i z)
      simpa [map_sum, map_zero, Prod.snd_sum] using h1
  · intro d1 _ d2 _ heq
    funext x
    apply e.injective
    apply Prod.ext
    · exact congrFun (congrArg Prod.fst heq) x
    · exact congrFun (congrArg Prod.snd heq) x
  · rintro ⟨da, db⟩ hab
    rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    refine ⟨fun x => e.symm (da x, db x), Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i z => ?_⟩, ?_⟩
    · apply e.injective
      rw [map_sum, map_zero]
      apply Prod.ext
      · have h1 : (∑ x ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i (shiftB x z)),
            e (e.symm (da x, db x))).1 =
            ∑ x ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i (shiftB x z)), da x := by
          simp [Prod.fst_sum]
        rw [h1]; exact ha' i z
      · have h2 : (∑ x ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i (shiftB x z)),
            e (e.symm (da x, db x))).2 =
            ∑ x ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i (shiftB x z)), db x := by
          simp [Prod.snd_sum]
        rw [h2]; exact hb' i z
    · apply Prod.ext <;> (funext x; simp)

lemma zmodKernel_two_pow_of_oddSeed {n k : Nat} (seed : Fin k → Finset (Fin n) → Bool)
    (hodd : oddSeedB seed) (a : Nat) :
    letI : NeZero (2 ^ a) := ⟨pow_ne_zero a (by decide)⟩
    (zmodKernel seed (2 ^ a)).card = 1 := by
  letI : NeZero (2 ^ a) := ⟨pow_ne_zero a (by decide)⟩
  rcases hodd with ⟨i0, hi0⟩
  have hsing : zmodKernel seed (2 ^ a) = {0} := by
    ext d
    simp only [zmodKernel, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hd
      let A := convMat seed i0
      have hAd : ∀ z : Finset (Fin n),
          (Finset.univ : Finset (Finset (Fin n))).sum (fun x => (A z x : ZMod (2 ^ a)) * d x) = 0 := by
        intro z
        have h1 : (Finset.univ : Finset (Finset (Fin n))).sum (fun x => (A z x : ZMod (2 ^ a)) * d x) =
            ((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i0 (shiftB x z))).sum d := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [A, convMat]
          rw [shiftB_comm z x]
          by_cases h : seed i0 (shiftB x z) = true <;> simp [h]
        rw [h1]; exact hd i0 z
      have hdet_mul : ∀ y : Finset (Fin n), (A.det : ZMod (2 ^ a)) * d y = 0 := by
        intro y
        have hadj := Matrix.adjugate_mul A
        have hsum0 : (Finset.univ : Finset (Finset (Fin n))).sum (fun z =>
            (A.adjugate y z : ZMod (2 ^ a)) *
              (Finset.univ : Finset (Finset (Fin n))).sum (fun x => (A z x : ZMod (2 ^ a)) * d x)) = 0 := by
          simp [hAd]
        have hrearr : (Finset.univ : Finset (Finset (Fin n))).sum (fun z =>
            (A.adjugate y z : ZMod (2 ^ a)) *
              (Finset.univ : Finset (Finset (Fin n))).sum (fun x => (A z x : ZMod (2 ^ a)) * d x)) =
            (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
              (((A.adjugate * A) y x : Int) : ZMod (2 ^ a)) * d x) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [Matrix.mul_apply, Int.cast_sum, Int.cast_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun z _ => by ring
        rw [hrearr, hadj] at hsum0
        have heval : (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
            (((A.det • (1 : Matrix (Finset (Fin n)) (Finset (Fin n)) Int)) y x : Int) : ZMod (2 ^ a)) * d x) =
            (A.det : ZMod (2 ^ a)) * d y := by
          rw [Finset.sum_eq_single y]
          · simp
          · intro x _ hxy; simp [Matrix.one_apply, Ne.symm hxy]
          · intro h; exact False.elim (h (Finset.mem_univ y))
        rwa [heval] at hsum0
      have hcop : Nat.Coprime A.det.natAbs (2 ^ a) :=
        Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr (odd_convMat_det seed i0 hi0))
      have hunit : IsUnit (A.det : ZMod (2 ^ a)) := by
        rcases Int.natAbs_eq A.det with h | h
        · rw [h]; simpa using (ZMod.isUnit_iff_coprime A.det.natAbs (2 ^ a)).mpr hcop
        · rw [h, Int.cast_neg]
          simpa using ((ZMod.isUnit_iff_coprime A.det.natAbs (2 ^ a)).mpr hcop).neg
      funext y
      exact hunit.mul_right_eq_zero.mp (hdet_mul y)
    · rintro rfl i z; simp
  rw [hsing, Finset.card_singleton]

lemma card_zmod_annihilator (b d : Nat) [NeZero b] :
    ((Finset.univ : Finset (ZMod b)).filter (fun v => (d : ZMod b) * v = 0)).card =
      Nat.gcd b d := by
  have hb : 0 < b := NeZero.pos b
  let g := Nat.gcd b d
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left d hb
  have hg_dvd_b : g ∣ b := Nat.gcd_dvd_left b d
  let step := b / g
  have hstep_mul : step * g = b := Nat.div_mul_cancel hg_dvd_b
  have hstep_pos : 0 < step := by
    by_contra h0
    have h0' : step = 0 := Nat.eq_zero_of_not_pos h0
    have hb0 : 0 = b := by simpa [h0'] using hstep_mul
    omega
  have hcop : Nat.Coprime step (d / g) := Nat.coprime_div_gcd_div_gcd hg_pos (m := b) (n := d)
  change _ = g
  rw [← Finset.card_range g]
  refine Finset.card_bij (fun (v : ZMod b) _ => v.val / step) ?_ ?_ ?_
  · intro v hv
    have hvlt : v.val < b := ZMod.val_lt v
    have hlt : v.val / step < g := by
      rw [Nat.div_lt_iff_lt_mul hstep_pos, mul_comm, hstep_mul]; exact hvlt
    exact Finset.mem_range.mpr hlt
  · intro v1 hv1 v2 hv2 heq
    have h1 : (d : ZMod b) * v1 = 0 := (Finset.mem_filter.mp hv1).2
    have h2 : (d : ZMod b) * v2 = 0 := (Finset.mem_filter.mp hv2).2
    have hdvd1 : step ∣ v1.val := by
      have hcast : ((d * v1.val : Nat) : ZMod b) = 0 := by
        simpa [Nat.cast_mul, ZMod.natCast_zmod_val] using h1
      have hbd : b ∣ d * v1.val := (ZMod.natCast_eq_zero_iff _ _).mp hcast
      have hbd' : g * step ∣ g * ((d / g) * v1.val) := by
        rcases hbd with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        have hdg : g * (d / g) = d := Nat.mul_div_cancel' (Nat.gcd_dvd_right b d)
        calc g * ((d / g) * v1.val) = (g * (d / g)) * v1.val := by ring
          _ = d * v1.val := by rw [hdg]
          _ = b * t := ht
          _ = (step * g) * t := by rw [← hstep_mul]
          _ = (g * step) * t := by ring
      have hst : step ∣ (d / g) * v1.val := (Nat.mul_dvd_mul_iff_left hg_pos).mp hbd'
      exact hcop.dvd_of_dvd_mul_left hst
    have hdvd2 : step ∣ v2.val := by
      have hcast : ((d * v2.val : Nat) : ZMod b) = 0 := by
        simpa [Nat.cast_mul, ZMod.natCast_zmod_val] using h2
      have hbd : b ∣ d * v2.val := (ZMod.natCast_eq_zero_iff _ _).mp hcast
      have hbd' : g * step ∣ g * ((d / g) * v2.val) := by
        rcases hbd with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        have hdg : g * (d / g) = d := Nat.mul_div_cancel' (Nat.gcd_dvd_right b d)
        calc g * ((d / g) * v2.val) = (g * (d / g)) * v2.val := by ring
          _ = d * v2.val := by rw [hdg]
          _ = b * t := ht
          _ = (step * g) * t := by rw [← hstep_mul]
          _ = (g * step) * t := by ring
      have hst : step ∣ (d / g) * v2.val := (Nat.mul_dvd_mul_iff_left hg_pos).mp hbd'
      exact hcop.dvd_of_dvd_mul_left hst
    have hval : v1.val = v2.val := by
      rw [← Nat.mul_div_cancel' hdvd1, ← Nat.mul_div_cancel' hdvd2, heq]
    exact ZMod.val_injective b hval
  · intro q hq
    have hqlt : q < g := Finset.mem_range.mp hq
    have hqstep_lt : q * step < b := by
      calc q * step < g * step := Nat.mul_lt_mul_of_pos_right hqlt hstep_pos
        _ = b := by rw [mul_comm, hstep_mul]
    refine ⟨((q * step : Nat) : ZMod b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · have hmul : (d : ZMod b) * ((q * step : Nat) : ZMod b) = ((d * (q * step) : Nat) : ZMod b) := by
        simp [Nat.cast_mul]
      rw [hmul, ZMod.natCast_eq_zero_iff]
      have hdg : d = (d / g) * g := (Nat.div_mul_cancel (Nat.gcd_dvd_right b d)).symm
      refine ⟨(d / g) * q, ?_⟩
      calc d * (q * step) = (d / g) * g * (q * step) := by rw [← hdg]
        _ = (step * g) * ((d / g) * q) := by ring
        _ = b * ((d / g) * q) := by rw [hstep_mul]
    · rw [ZMod.val_natCast_of_lt hqstep_lt, Nat.mul_div_cancel q hstep_pos]

lemma card_pi_filter_eq_prod {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (P : α → β → Prop) [∀ a, DecidablePred (P a)] :
    ((Finset.univ : Finset (α → β)).filter (fun f => ∀ a, P a (f a))).card =
      (Finset.univ : Finset α).prod (fun a => ((Finset.univ : Finset β).filter (fun b => P a b)).card) := by
  have heq : (Finset.univ : Finset (α → β)).filter (fun f => ∀ a, P a (f a)) =
      Fintype.piFinset (fun a => (Finset.univ : Finset β).filter (fun b => P a b)) := by
    ext f; simp [Fintype.mem_piFinset]
  rw [heq, Fintype.card_piFinset]

lemma zmodKernel_odd {n k : Nat} (seed : Fin k → Finset (Fin n) → Bool)
    (b : Nat) [NeZero b] (hodd : Odd b) :
    (zmodKernel seed b).card =
      (Finset.univ : Finset (Finset (Fin n))).prod (fun T => Nat.gcd b (divisorB seed T)) := by
  let W : (Finset (Fin n) → ZMod b) → (Finset (Fin n) → ZMod b) :=
    fun f T => (Finset.univ : Finset (Finset (Fin n))).sum (fun x => (chi T x : ZMod b) * f x)
  have hW_invol : ∀ f x, W (W f) x = ((2 : ZMod b) ^ n) * f x := by
    intro f x
    simp only [W]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hrearr : (Finset.univ : Finset (Finset (Fin n))).sum (fun y =>
        (Finset.univ : Finset (Finset (Fin n))).sum (fun T => (chi x T : ZMod b) * ((chi T y : ZMod b) * f y))) =
        (Finset.univ : Finset (Finset (Fin n))).sum (fun y =>
          (((Finset.univ : Finset (Finset (Fin n))).sum (fun T => chi T x * chi T y) : Int) : ZMod b) * f y) := by
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Int.cast_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun T _ => ?_
      have hc : chi x T = chi T x := by simp [chi, Finset.inter_comm]
      rw [hc, Int.cast_mul]; ring
    rw [hrearr]
    simp_rw [sum_chi_mul_chi]
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hyx; simp [hyx]
    · intro h; exact False.elim (h (Finset.mem_univ x))
  have h2unit : IsUnit ((2 : ZMod b) ^ n) := by
    have hcop : Nat.Coprime (2 ^ n) b := Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hodd)
    have h1 := (ZMod.isUnit_iff_coprime (2 ^ n) b).mpr hcop
    simpa using h1
  have hW_inj : Function.Injective W := by
    intro f1 f2 heq
    funext x
    have h1 : W (W f1) x = W (W f2) x := congrFun (congrArg W heq) x
    rw [hW_invol, hW_invol] at h1
    exact h2unit.mul_left_cancel h1
  have hW_surj : Function.Surjective W := Finite.injective_iff_surjective.mp hW_inj
  have hW_zero : ∀ f, W f = 0 ↔ f = 0 := by
    intro f
    constructor
    · intro h
      apply hW_inj
      rw [h]; funext T; simp [W]
    · rintro rfl; funext T; simp [W]
  have hW_conv : ∀ (d : Finset (Fin n) → ZMod b) (i : Fin k) (T : Finset (Fin n)),
      W (fun z => ((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i (shiftB x z))).sum d) T =
        (spectrumB seed i T : ZMod b) * W d T := by
    intro d i T
    simp only [W]
    simp_rw [Finset.mul_sum, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hinner : (Finset.univ : Finset (Finset (Fin n))).sum
        (fun z => if seed i (shiftB x z) = true then (chi T z : ZMod b) * d x else 0) =
        ((((Finset.univ : Finset (Finset (Fin n))).filter (fun z => seed i (shiftB x z))).sum (chi T) : Int) : ZMod b) * d x := by
      rw [Finset.sum_filter, Int.cast_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun z _ => by
        by_cases h : seed i (shiftB x z) = true <;> simp [h]
    rw [hinner, sum_shift_chi, Int.cast_mul]; ring
  have hiff_gcd : ∀ (T : Finset (Fin n)) (v : ZMod b),
      (∀ i : Fin k, (spectrumB seed i T : ZMod b) * v = 0) ↔ (divisorB seed T : ZMod b) * v = 0 := by
    intro T v
    constructor
    · intro h
      have hgen : ∀ s : Finset (Fin k),
          (∀ i ∈ s, ((spectrumB seed i T).natAbs : ZMod b) * v = 0) →
          ((s.gcd (fun i => (spectrumB seed i T).natAbs) : Nat) : ZMod b) * v = 0 := by
        intro s
        induction s using Finset.induction_on with
        | empty => intro _; simp
        | insert i s hi ih =>
          intro hall
          have h1 := hall i (Finset.mem_insert_self i s)
          have h2 := ih (fun j hj => hall j (Finset.mem_insert_of_mem hj))
          let a1 : Nat := (spectrumB seed i T).natAbs
          let a2 : Nat := s.gcd (fun i => (spectrumB seed i T).natAbs)
          rw [Finset.gcd_insert]
          change ((Nat.gcd a1 a2 : Nat) : ZMod b) * v = 0
          have hbez := Nat.gcd_eq_gcd_ab a1 a2
          have hbezZ : ((Nat.gcd a1 a2 : Nat) : ZMod b) =
              (a1 : ZMod b) * (Nat.gcdA a1 a2 : ZMod b) +
              (a2 : ZMod b) * (Nat.gcdB a1 a2 : ZMod b) := by
            have := congrArg (Int.cast (R := ZMod b)) hbez
            simpa using this
          rw [hbezZ]
          calc ((a1 : ZMod b) * (Nat.gcdA a1 a2 : ZMod b) +
                (a2 : ZMod b) * (Nat.gcdB a1 a2 : ZMod b)) * v
              = (Nat.gcdA a1 a2 : ZMod b) * ((a1 : ZMod b) * v) +
                (Nat.gcdB a1 a2 : ZMod b) * ((a2 : ZMod b) * v) := by ring
            _ = 0 := by rw [h1, h2]; ring
      apply hgen Finset.univ
      intro i _
      rcases Int.natAbs_eq (spectrumB seed i T) with he | he
      · have hi := h i; rw [he, Int.cast_natCast] at hi; exact hi
      · have hi := h i; rw [he, Int.cast_neg, Int.cast_natCast, neg_mul, neg_eq_zero] at hi; exact hi
    · intro h i
      have hdvd : divisorB seed T ∣ (spectrumB seed i T).natAbs := Finset.gcd_dvd (Finset.mem_univ i)
      rcases hdvd with ⟨q, hq⟩
      have habs : ((spectrumB seed i T).natAbs : ZMod b) * v = 0 := by
        rw [hq, Nat.cast_mul]
        calc ((divisorB seed T : ZMod b) * (q : ZMod b)) * v
            = (q : ZMod b) * ((divisorB seed T : ZMod b) * v) := by ring
          _ = 0 := by rw [h, mul_zero]
      rcases Int.natAbs_eq (spectrumB seed i T) with he | he
      · rw [he]; simpa using habs
      · rw [he, Int.cast_neg, neg_mul, neg_eq_zero]; simpa using habs
  have hcard_W : (zmodKernel seed b).card =
      ((Finset.univ : Finset (Finset (Fin n) → ZMod b)).filter
        (fun g => ∀ T : Finset (Fin n), (divisorB seed T : ZMod b) * g T = 0)).card := by
    refine Finset.card_bij (fun d _ => W d) ?_ ?_ ?_
    · intro d hd
      have hd' := (Finset.mem_filter.mp hd).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun T => (hiff_gcd T (W d T)).mp fun i => ?_⟩
      rw [← hW_conv d i T]
      have hz : (fun z => ((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i (shiftB x z))).sum d) = 0 :=
        funext (hd' i)
      rw [hz]; simp [W]
    · intro d1 _ d2 _ heq; exact hW_inj heq
    · intro g hg
      have hg' := (Finset.mem_filter.mp hg).2
      rcases hW_surj g with ⟨d, hdW⟩
      refine ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i z => ?_⟩, hdW⟩
      have hW0 : W (fun z => ((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i (shiftB x z))).sum d) = 0 := by
        funext T
        rw [hW_conv d i T, hdW]
        exact (hiff_gcd T (g T)).mpr (hg' T) i
      exact congrFun ((hW_zero _).mp hW0) z
  rw [hcard_W, card_pi_filter_eq_prod (fun T (v : ZMod b) => (divisorB seed T : ZMod b) * v = 0)]
  refine Finset.prod_congr rfl fun T _ => card_zmod_annihilator b (divisorB seed T)

lemma exists_two_pow_mul_odd (m : Nat) (hm : 0 < m) :
    ∃ a b : Nat, 0 < b ∧ Odd b ∧ m = 2 ^ a * b := by
  suffices h : ∀ s m : Nat, m ≤ s → 0 < m → ∃ a b : Nat, 0 < b ∧ Odd b ∧ m = 2 ^ a * b from
    h m m le_rfl hm
  intro s
  induction s with
  | zero => intro m hle hm; omega
  | succ s ih =>
    intro m hle hm
    by_cases h2 : m % 2 = 0
    · rcases ih (m / 2) (by omega) (by omega) with ⟨a, b, hbpos, hbodd, heq⟩
      refine ⟨a + 1, b, hbpos, hbodd, ?_⟩
      have hmul : 2 ^ (a + 1) * b = 2 * (2 ^ a * b) := by rw [pow_succ]; ring
      omega
    · exact ⟨0, m, hm, Nat.odd_iff.mpr (by omega), by simp⟩

lemma kernelSizeB_formula {n k : Nat} (seed : Fin k → Finset (Fin n) → Bool)
    (m : Nat) (hm : 0 < m) (hcond : Odd m ∨ oddSeedB seed) :
    kernelSizeB seed m =
      (Finset.univ : Finset (Finset (Fin n))).prod (fun T => Nat.gcd m (divisorB seed T)) := by
  rcases exists_two_pow_mul_odd m hm with ⟨a, b, hbpos, hbodd, rfl⟩
  letI : NeZero (2 ^ a) := ⟨pow_ne_zero a (by decide)⟩
  letI : NeZero b := ⟨Nat.ne_of_gt hbpos⟩
  letI : NeZero (2 ^ a * b) := ⟨mul_ne_zero (NeZero.ne (2 ^ a)) (NeZero.ne b)⟩
  have hcop : Nat.Coprime (2 ^ a) b := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hbodd)
  rw [kernelSizeB_eq_zmodKernel, zmodKernel_mul_coprime seed hcop, zmodKernel_odd seed b hbodd]

  have hgcd_mul : ∀ d : Nat, Nat.gcd (2 ^ a * b) d = Nat.gcd (2 ^ a) d * Nat.gcd b d := by
    intro d
    rw [Nat.gcd_comm, Nat.gcd_comm (2 ^ a), Nat.gcd_comm b]
    exact hcop.gcd_mul d
  rcases hcond with hmodd | hseed
  · have ha0 : a = 0 := by
      by_contra hne
      have h2dvd : 2 ∣ 2 ^ a * b := dvd_mul_of_dvd_left (dvd_pow_self 2 hne) b
      rw [Nat.odd_iff] at hmodd
      rcases h2dvd with ⟨q, hq⟩; omega
    subst ha0
    have h1 : (zmodKernel seed (2 ^ 0)).card = 1 := by
      have hsub : Subsingleton (Finset (Fin n) → ZMod (2 ^ 0)) := by
        change Subsingleton (Finset (Fin n) → ZMod 1); infer_instance
      have hne : (zmodKernel seed (2 ^ 0)).Nonempty :=
        ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ _ => by simp⟩⟩
      rcases hne with ⟨d0, hd0⟩
      have hsing : zmodKernel seed (2 ^ 0) = {d0} := by
        ext d; simp only [Finset.mem_singleton]
        exact ⟨fun _ => @Subsingleton.elim _ hsub d d0, fun h => h ▸ hd0⟩
      rw [hsing, Finset.card_singleton]
    rw [h1, one_mul]
    simp only [pow_zero, one_mul]
  · rw [zmodKernel_two_pow_of_oddSeed seed hseed a, one_mul]
    refine Finset.prod_congr rfl fun T _ => ?_
    rw [hgcd_mul (divisorB seed T)]
    have hcop2 : Nat.Coprime (2 ^ a) (divisorB seed T) :=
      Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr (odd_divisor_of_oddSeed seed hseed T))
    rw [hcop2.gcd_eq_one, one_mul]

lemma kernelSizeB_eq_one_iff {n k : Nat} (seed : Fin k → Finset (Fin n) → Bool)
    (m : Nat) (hm : 0 < m) :
    kernelSizeB seed m = 1 ↔ ∀ T : Finset (Fin n), Nat.Coprime m (divisorB seed T) := by
  by_cases hcond : Odd m ∨ oddSeedB seed
  · rw [kernelSizeB_formula seed m hm hcond]
    constructor
    · intro h1 T
      have hpos : ∀ X ∈ (Finset.univ : Finset (Finset (Fin n))), 0 < Nat.gcd m (divisorB seed X) :=
        fun X _ => Nat.gcd_pos_of_pos_left _ hm
      have hne0 : ∀ X ∈ (Finset.univ : Finset (Finset (Fin n))), Nat.gcd m (divisorB seed X) ≠ 0 :=
        fun X hX => Nat.ne_of_gt (hpos X hX)
      have hle : Nat.gcd m (divisorB seed T) ≤ 1 := by
        have hdvd : Nat.gcd m (divisorB seed T) ∣ 1 := by
          rw [← h1]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ T)
        exact Nat.le_of_dvd (by decide) hdvd
      have hgt0 := hpos T (Finset.mem_univ T)
      exact Nat.coprime_iff_gcd_eq_one.mpr (by omega)
    · intro hall
      exact Finset.prod_eq_one fun T _ => (hall T).gcd_eq_one
  · have hnotOdd : ¬ Odd m := fun h => hcond (Or.inl h)
    have hnotSeed : ¬ oddSeedB seed := fun h => hcond (Or.inr h)
    have hm_even : m % 2 = 0 := by rw [Nat.odd_iff] at hnotOdd; omega
    constructor
    · intro hk1
      exfalso
      let d0 : Finset (Fin n) → Fin m := fun _ => ⟨0, hm⟩
      let d1 : Finset (Fin n) → Fin m := fun _ => ⟨m / 2, by omega⟩
      have hd0 : d0 ∈ (Finset.univ : Finset (Finset (Fin n) → Fin m)).filter (fun d =>
          ∀ i : Fin k, ∀ z : Finset (Fin n),
            (((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i (shiftB x z))).sum
              (fun x => (d x).val)) % m = 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ _ => by simp [d0]⟩
      have hd1 : d1 ∈ (Finset.univ : Finset (Finset (Fin n) → Fin m)).filter (fun d =>
          ∀ i : Fin k, ∀ z : Finset (Fin n),
            (((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i (shiftB x z))).sum
              (fun x => (d x).val)) % m = 0) := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i z => ?_⟩
        simp only [d1, Finset.sum_const, smul_eq_mul]
        have hcard_eq : ((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i (shiftB x z))).card =
            ((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i x)).card := by
          refine Finset.card_bij (fun x _ => shiftB x z) ?_ ?_ ?_
          · intro x hx; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
          · intro x1 _ x2 _ heq
            have := congrArg (fun w => shiftB w z) heq
            simpa [shiftB_invol_right] using this
          · intro w hw
            refine ⟨shiftB w z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, shiftB_invol_right w z⟩
            rw [shiftB_invol_right]; exact (Finset.mem_filter.mp hw).2
        rw [hcard_eq]
        have hev : ((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i x)).card % 2 = 0 := by
          have : ¬ Odd (((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i x)).card) :=
            fun h => hnotSeed ⟨i, h⟩
          rw [Nat.odd_iff] at this; omega
        have hmul : ((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i x)).card * (m / 2) =
            (((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i x)).card / 2) * m := by
          have hc2 : ((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i x)).card =
              2 * (((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i x)).card / 2) := by omega
          have hm2 : m = 2 * (m / 2) := by omega
          calc ((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i x)).card * (m / 2)
              = (2 * (((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i x)).card / 2)) * (m / 2) := by rw [← hc2]
            _ = (((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i x)).card / 2) * (2 * (m / 2)) := by ring
            _ = (((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i x)).card / 2) * m := by rw [← hm2]
        rw [hmul, Nat.mul_mod_left]
      have hne01 : d0 ≠ d1 := by
        intro heq
        have := congrArg Fin.val (congrFun heq ∅)
        simp only [d0, d1] at this; omega
      have hge2 : 2 ≤ kernelSizeB seed m := by
        have hsub : ({d0, d1} : Finset _) ⊆ (Finset.univ : Finset (Finset (Fin n) → Fin m)).filter (fun d =>
            ∀ i : Fin k, ∀ z : Finset (Fin n),
              (((Finset.univ : Finset (Finset (Fin n))).filter (fun x => seed i (shiftB x z))).sum
                (fun x => (d x).val)) % m = 0) := by
          intro d hd
          rcases Finset.mem_insert.mp hd with rfl | hd'
          · exact hd0
          · rw [Finset.mem_singleton.mp hd']; exact hd1
        have hc := Finset.card_le_card hsub
        rw [Finset.card_pair hne01] at hc
        exact hc
      omega
    · intro hall
      exfalso
      have h2d : 2 ∣ divisorB seed ∅ := even_divisor_empty_of_not_oddSeed seed hnotSeed
      have h2m : 2 ∣ m := Nat.dvd_of_mod_eq_zero hm_even
      have h2g : 2 ∣ Nat.gcd m (divisorB seed ∅) := Nat.dvd_gcd h2m h2d
      rw [(hall ∅).gcd_eq_one] at h2g
      exact absurd (Nat.le_of_dvd (by decide) h2g) (by decide)

end PEqualNP.Outside.L_lib_1154_aux

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.L_lib_1154 : ∀ (n k : Nat) (seed : Fin k → Finset (Fin n) → Bool),
  let Bits := Finset (Fin n)
  let cube := (Finset.univ : Finset Bits)
  let bank := (Finset.univ : Finset (Fin k))
  let shift := fun (x z : Bits) => (x \ z) ∪ (z \ x)
  let pass := fun (i : Fin k) (z x : Bits) => seed i (shift x z)
  let spectrum := fun (i : Fin k) (T : Bits) =>
    (cube.filter (fun x => seed i x)).sum (fun x => (-1 : Int) ^ (x ∩ T).card)
  let divisor := fun (T : Bits) => bank.gcd (fun i => (spectrum i T).natAbs)
  let oddSeed := ∃ i, Odd ((cube.filter (fun x => seed i x)).card)
  let synthesizes := fun (u : Nat) =>
    ∀ y : Bits, ∃ c : Fin k → Bits → Int, ∀ x : Bits,
      bank.sum (fun i => (cube.filter (fun z => pass i z x)).sum (c i)) =
        if x = y then (u : Int) else 0
  let kernelSize := fun (m : Nat) =>
    ((Finset.univ : Finset (Bits → Fin m)).filter (fun d =>
      ∀ i : Fin k, ∀ z : Bits, ((cube.filter (fun x => pass i z x)).sum
        (fun x => (d x).val)) % m = 0)).card
  (synthesizes 1 ↔ ∀ T : Bits, divisor T = 1) ∧
  (oddSeed → ∀ u : Nat, synthesizes u ↔ cube.lcm divisor ∣ u) ∧
  (∀ m : Nat, 0 < m →
    (kernelSize m = 1 ↔ ∀ T : Bits, Nat.Coprime m (divisor T)) ∧
    ((Odd m ∨ oddSeed) → kernelSize m = cube.prod (fun T => Nat.gcd m (divisor T)))) := by
  intro n k seed Bits cube bank shift pass spectrum divisor oddSeed synthesizes kernelSize
  have hdiv_eq : divisor = PEqualNP.Outside.L_lib_1154_aux.divisorB seed := rfl
  have hodd_eq : oddSeed = PEqualNP.Outside.L_lib_1154_aux.oddSeedB seed := rfl
  have hsyn_eq : synthesizes = PEqualNP.Outside.L_lib_1154_aux.synthesizesB seed := rfl
  have hker_eq : kernelSize = PEqualNP.Outside.L_lib_1154_aux.kernelSizeB seed := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hsyn_eq, hdiv_eq]
    constructor
    · intro h1 T
      exact Nat.eq_one_of_dvd_one (PEqualNP.Outside.L_lib_1154_aux.synthesizes_imp_dvd seed h1 T)
    · intro hall
      have hodd : PEqualNP.Outside.L_lib_1154_aux.oddSeedB seed := by
        by_contra hno
        have h2 := PEqualNP.Outside.L_lib_1154_aux.even_divisor_empty_of_not_oddSeed seed hno
        rw [hall ∅] at h2
        exact absurd (Nat.le_of_dvd (by decide) h2) (by decide)
      have hlcm : (Finset.univ : Finset (Finset (Fin n))).lcm (PEqualNP.Outside.L_lib_1154_aux.divisorB seed) ∣ 1 :=
        Finset.lcm_dvd fun T _ => by rw [hall T]
      exact PEqualNP.Outside.L_lib_1154_aux.synthesizes_of_oddSeed_dvd seed hodd hlcm
  · rw [hodd_eq, hsyn_eq, hdiv_eq]
    intro hodd u
    constructor
    · intro hsu
      exact Finset.lcm_dvd fun T _ => PEqualNP.Outside.L_lib_1154_aux.synthesizes_imp_dvd seed hsu T
    · intro hdvd
      exact PEqualNP.Outside.L_lib_1154_aux.synthesizes_of_oddSeed_dvd seed hodd hdvd
  · intro m hm
    rw [hker_eq, hdiv_eq, hodd_eq]
    exact ⟨PEqualNP.Outside.L_lib_1154_aux.kernelSizeB_eq_one_iff seed m hm,
      fun hcond => PEqualNP.Outside.L_lib_1154_aux.kernelSizeB_formula seed m hm hcond⟩
