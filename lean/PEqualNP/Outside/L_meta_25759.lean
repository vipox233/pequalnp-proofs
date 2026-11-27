import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25759_aux

open scoped BigOperators

variable {ι α : Type*} [Fintype α] [DecidableEq α]

def moment (s : Finset ι) (coord : ι → α) (sign : ι → α → ℤ) (a b : α) : ℤ :=
  ∑ x ∈ s, if coord x = a then sign x b else 0

theorem trace_identity (s : Finset ι) (coord : ι → α) (sign : ι → α → ℤ) :
    (∑ x ∈ s, ∑ y ∈ s, sign x (coord y) * sign y (coord x)) =
      ∑ a : α, ∑ b : α, moment s coord sign a b * moment s coord sign b a := by
  symm
  simp only [moment, Finset.sum_mul, Finset.mul_sum]
  let f (a b : α) (y x : ι) :=
    (if coord x = a then sign x b else 0) * (if coord y = b then sign y a else 0)
  change (∑ a : α, ∑ b : α, ∑ y ∈ s, ∑ x ∈ s, f a b y x) = _
  calc
    _ = ∑ a : α, ∑ y ∈ s, ∑ b : α, ∑ x ∈ s, f a b y x := by
      exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ y ∈ s, ∑ a : α, ∑ b : α, ∑ x ∈ s, f a b y x := Finset.sum_comm
    _ = ∑ y ∈ s, ∑ a : α, ∑ x ∈ s, ∑ b : α, f a b y x := by
      exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ y ∈ s, ∑ x ∈ s, ∑ a : α, ∑ b : α, f a b y x := by
      exact Finset.sum_congr rfl fun y _ => Finset.sum_comm
    _ = ∑ y ∈ s, ∑ x ∈ s, sign x (coord y) * sign y (coord x) := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro x _
      simp [f, ite_mul, mul_ite]
    _ = _ := Finset.sum_comm

theorem trace_le_energy (s : Finset ι) (coord : ι → α) (sign : ι → α → ℤ) :
    (∑ x ∈ s, ∑ y ∈ s, sign x (coord y) * sign y (coord x)) ≤
      ∑ a : α, ∑ b : α, (moment s coord sign a b)^2 := by
  rw [trace_identity]
  let m := moment s coord sign
  have h : 2 * (∑ a : α, ∑ b : α, m a b * m b a) ≤
      2 * (∑ a : α, ∑ b : α, m a b ^ 2) := by
    have hs : (∑ a : α, ∑ b : α, 2 * (m a b * m b a)) ≤
        ∑ a : α, ∑ b : α, (m a b ^ 2 + m b a ^ 2) := by
      gcongr with a _ b _
      nlinarith [sq_nonneg (m a b - m b a)]
    simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hs
    have ht : (∑ a : α, ∑ b : α, m b a ^ 2) = ∑ a : α, ∑ b : α, m a b ^ 2 :=
      Finset.sum_comm
    rw [ht] at hs
    linarith
  exact le_of_mul_le_mul_left h (by norm_num)

theorem trace_bound_of_fibers (s : Finset ι) (coord : ι → α) (sign : ι → α → ℤ)
    (energyPerPoint : ℤ)
    (h : ∀ a : α, (∑ b : α, (moment s coord sign a b)^2) ≤
      energyPerPoint * (s.filter fun x => coord x = a).card) :
    (∑ x ∈ s, ∑ y ∈ s, sign x (coord y) * sign y (coord x)) ≤
      energyPerPoint * s.card := by
  refine (trace_le_energy s coord sign).trans ?_
  calc
    _ ≤ ∑ a : α, energyPerPoint * (s.filter fun x => coord x = a).card :=
      Finset.sum_le_sum fun a _ => h a
    _ = energyPerPoint * s.card := by
      rw [← Finset.mul_sum, ← Nat.cast_sum]
      congr 1
      have hc : (∑ a : α, (s.filter fun x => coord x = a).card) = s.card := by
        simpa using (Finset.sum_card_fiberwise_eq_card_filter s (Finset.univ : Finset α) coord)
      exact_mod_cast hc

end PEqualNP.Outside.L_meta_25759_aux

namespace PEqualNP.Outside.L_meta_25759_aux

open scoped BigOperators

def bitSign (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem bitSign_false : bitSign false = 1 := rfl
@[simp] theorem bitSign_true : bitSign true = -1 := rfl

theorem cube_mgf {k : ℕ} (u : Fin k → ℝ) :
    (∑ x : Fin k → Bool, Real.exp (∑ i, u i * bitSign (x i))) ≤
      (2 : ℝ)^k * Real.exp ((∑ i, (u i)^2) / 2) := by
  classical
  simp only [Real.exp_sum]
  rw [show (∑ x : Fin k → Bool, ∏ i, Real.exp (u i * bitSign (x i))) =
      ∏ i : Fin k, ∑ b : Bool, Real.exp (u i * bitSign b) by
    simpa only [Fintype.piFinset_univ] using (Finset.sum_prod_piFinset (Finset.univ : Finset Bool)
      (fun i : Fin k => fun b => Real.exp (u i * bitSign b)))]
  calc
    _ ≤ ∏ i : Fin k, 2 * Real.exp ((u i)^2 / 2) := by
      apply Finset.prod_le_prod₀
      · intro i _
        positivity
      · intro i _
        rw [Fintype.sum_bool]
        simp only [bitSign_false, bitSign_true, mul_one, mul_neg]
        have h := Real.cosh_le_exp_half_sq (u i)
        rw [Real.cosh_eq] at h
        linarith
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.sum_div]
      simp

theorem signed_cube_mgf {k : ℕ} (u : Fin k → ℝ) (s : Finset (Fin k → Bool))
    (flip : (Fin k → Bool) → Bool) :
    (∑ x ∈ s, Real.exp (∑ i, u i * (bitSign (flip x) * bitSign (x i)))) ≤
      2 * (2 : ℝ)^k * Real.exp ((∑ i, (u i)^2) / 2) := by
  classical
  let e : (Fin k → Bool) → ℝ := fun x => Real.exp (∑ i, u i * bitSign (x i))
  let f : (Fin k → Bool) → ℝ := fun x => Real.exp (∑ i, (-u i) * bitSign (x i))
  calc
    _ ≤ ∑ x ∈ s, (e x + f x) := by
      apply Finset.sum_le_sum
      intro x _
      cases flip x <;> simp [e, f] <;> positivity
    _ ≤ ∑ x : Fin k → Bool, (e x + f x) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      intro x _ _
      dsimp [e, f]
      positivity
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      have hp := cube_mgf u
      have hn := cube_mgf fun i => -u i
      simp only [neg_sq] at hn
      dsimp [e, f]
      linarith

theorem exp_average_le_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hs : s.Nonempty) :
    (s.card : ℝ) * Real.exp ((∑ x ∈ s, f x) / s.card) ≤
      ∑ x ∈ s, Real.exp (f x) := by
  let a : ℝ := (∑ x ∈ s, f x) / s.card
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  have hmean : (s.card : ℝ) * a = ∑ x ∈ s, f x := by
    dsimp [a]
    field_simp
  have h : (s.card : ℝ) ≤ ∑ x ∈ s, Real.exp (f x - a) := by
    calc
      _ = ∑ x ∈ s, (f x - a + 1) := by
        simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, hmean]
      _ ≤ _ := Finset.sum_le_sum fun x _ => Real.add_one_le_exp (f x - a)
  have hh := mul_le_mul_of_nonneg_right h (Real.exp_pos a).le
  rw [Finset.sum_mul] at hh
  simpa only [← Real.exp_add, sub_add_cancel] using hh

def signedMoment {k : ℕ} (s : Finset (Fin k → Bool))
    (flip : (Fin k → Bool) → Bool) (i : Fin k) : ℝ :=
  ∑ x ∈ s, bitSign (flip x) * bitSign (x i)

theorem cube_energy {k : ℕ} (s : Finset (Fin k → Bool))
    (flip : (Fin k → Bool) → Bool) (hs : s.Nonempty) :
    (∑ i, (signedMoment s flip i)^2) ≤
      2 * (s.card : ℝ)^2 * Real.log (2 * (2 : ℝ)^k / s.card) := by
  classical
  let m := signedMoment s flip
  let h : ℝ := s.card
  have hh : 0 < h := by
    change (0 : ℝ) < (s.card : ℝ)
    exact_mod_cast hs.card_pos
  let u i := m i / h
  let Q := ∑ i, (u i)^2
  let f (x : Fin k → Bool) := ∑ i, u i * (bitSign (flip x) * bitSign (x i))
  have hu (i : Fin k) : m i = h * u i := by
    dsimp [u]
    field_simp
  have hf : (∑ x ∈ s, f x) / h = Q := by
    apply (div_eq_iff hh.ne').mpr
    dsimp only [f, Q]
    rw [Finset.sum_comm, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.mul_sum]
    change u i * m i = _
    rw [hu]
    ring
  have hmgf := (exp_average_le_sum s f hs).trans (signed_cube_mgf u s flip)
  change h * Real.exp ((∑ x ∈ s, f x) / h) ≤ 2 * (2 : ℝ)^k * Real.exp (Q / 2) at hmgf
  rw [hf] at hmgf
  have hfactor : Real.exp Q = Real.exp (Q / 2) * Real.exp (Q / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfactor, ← mul_assoc] at hmgf
  have hexp : Real.exp (Q / 2) ≤ 2 * (2 : ℝ)^k / h := by
    apply (le_div_iff₀ hh).mpr
    rw [mul_comm]
    exact le_of_mul_le_mul_right hmgf (Real.exp_pos _)
  have hlog : Q / 2 ≤ Real.log (2 * (2 : ℝ)^k / h) := by
    rw [← Real.log_exp (Q / 2)]
    exact Real.log_le_log (Real.exp_pos _) hexp
  change (∑ i, (m i)^2) ≤ 2 * h^2 * Real.log (2 * (2 : ℝ)^k / h)
  have he : (∑ i, (m i)^2) = h^2 * Q := by
    dsimp only [Q]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hu]
    ring
  rw [he]
  have hb : Q ≤ 2 * Real.log (2 * (2 : ℝ)^k / h) := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hb (sq_nonneg h)]

noncomputable def finBitsEquiv (k : ℕ) : Fin (2^k) ≃ (Fin k → Bool) := by
  let f (x : Fin (2^k)) (i : Fin k) := x.val.testBit i
  apply Equiv.ofBijective f
  apply (Fintype.bijective_iff_injective_and_card f).mpr
  constructor
  · intro x y h
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < k
    · exact congrFun h (⟨i, hi⟩ : Fin k)
    · have hpow : 2^k ≤ (2 : ℕ)^i :=
        Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hi)
      rw [Nat.testBit_lt_two_pow (x.isLt.trans_le hpow), Nat.testBit_lt_two_pow (y.isLt.trans_le hpow)]
  · simp [Fintype.card_fun]

theorem cube_energy_density {k a : ℕ} (ha : 4 ≤ a) (s : Finset (Fin k → Bool))
    (flip : (Fin k → Bool) → Bool) (hcard : (s.card : ℝ) ≤ (2:ℝ)^k / 2^a) :
    (∑ i, (signedMoment s flip i)^2) ≤
      2 * (a : ℝ) * ((2:ℝ)^k / 2^a) * s.card := by
  classical
  by_cases hs : s.Nonempty
  swap
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs, signedMoment]
  let h : ℝ := s.card
  let H : ℝ := (2:ℝ)^k / 2^a
  let l : ℝ := Real.log (2 * (2:ℝ)^a)
  have hh : 0 < h := by
    change (0 : ℝ) < (s.card : ℝ)
    exact_mod_cast hs.card_pos
  have hH : 0 < H := by dsimp [H]; positivity
  have hl : l = ((a : ℝ) + 1) * Real.log 2 := by
    dsimp [l]
    rw [← pow_succ', Real.log_pow, Nat.cast_succ]
  have ha' : (4:ℝ) ≤ a := by exact_mod_cast ha
  have hlo : 1 ≤ l := by
    rw [hl]
    nlinarith [Real.log_two_gt_d9]
  have hhi : l ≤ a := by
    rw [hl]
    nlinarith [Real.log_two_lt_d9]
  have hsplit : Real.log (2 * (2 : ℝ)^k / h) = l + Real.log (H / h) := by
    dsimp [l, H]
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have hterm : h * Real.log (H/h) ≤ H - h := by
    have hb := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hH hh)) hh.le
    have hc : h * (H/h-1) = H-h := by field_simp
    exact hb.trans_eq hc
  change h ≤ H at hcard
  have ht : h * Real.log (2 * (2 : ℝ)^k / h) ≤ (a : ℝ) * H := by
    rw [hsplit, mul_add]
    have hd := mul_le_mul_of_nonneg_right hlo (sub_nonneg.mpr hcard)
    have he := mul_le_mul_of_nonneg_right hhi hH.le
    nlinarith
  refine (cube_energy s flip hs).trans ?_
  change 2 * h^2 * Real.log (2 * (2 : ℝ)^k / h) ≤ 2 * (a : ℝ) * H * h
  nlinarith [mul_le_mul_of_nonneg_right ht hh.le]

end PEqualNP.Outside.L_meta_25759_aux

namespace PEqualNP.Outside.L_meta_25759_aux

open scoped BigOperators

def gateRadix (f : Bool → Bool → Bool) : ℕ :=
  let ones := ((Finset.univ : Finset (Bool × Bool)).filter (fun z => f z.1 z.2)).card
  if ones = 0 ∨ ones = 4 then 1 else if ones = 2 then 2 else 3

def gateTable (a b c d : Bool) : Bool → Bool → Bool
  | false, false => a
  | false, true => b
  | true, false => c
  | true, true => d

theorem gate_eq_table (f : Bool → Bool → Bool) :
    f = gateTable (f false false) (f false true) (f true false) (f true true) := by
  funext a b
  cases a <;> cases b <;> rfl

theorem gate_color (f : Bool → Bool → Bool) :
    ∃ c : Bool × Bool → Fin (gateRadix f), ∀ x y : Bool × Bool,
      c x = c y → f x.1 y.2 = f y.1 x.2 := by
  have h : ∀ a b c d : Bool,
      ∃ col : Bool × Bool → Fin (gateRadix (gateTable a b c d)), ∀ x y : Bool × Bool,
        col x = col y → gateTable a b c d x.1 y.2 = gateTable a b c d y.1 x.2 := by
    decide
  rw [gate_eq_table f]
  exact h _ _ _ _

theorem gate_embed (f : Bool → Bool → Bool) :
    ∃ e : Fin (gateRadix f) → Bool × Bool, ∀ x y : Fin (gateRadix f),
      x ≠ y → f (e x).1 (e y).2 ≠ f (e y).1 (e x).2 := by
  have h : ∀ a b c d : Bool,
      ∃ emb : Fin (gateRadix (gateTable a b c d)) → Bool × Bool,
        ∀ x y, x ≠ y → gateTable a b c d (emb x).1 (emb y).2 ≠
          gateTable a b c d (emb y).1 (emb x).2 := by
    decide
  rw [gate_eq_table f]
  exact h _ _ _ _

section Count

variable {ι σ α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]

def errors (target : ι → ι → Bool) (sig : ι → ι → σ) (out : Finset ι → σ → Bool) : ℕ :=
  ((Finset.univ : Finset (ι × ι)).filter fun z => out {z.1,z.2} (sig z.1 z.2) ≠ target z.1 z.2).card

def clashes (target : ι → ι → Bool) (color : ι → α) : ℕ :=
  ((Finset.univ : Finset (ι × ι)).filter fun z => color z.1 = color z.2 ∧ target z.1 z.2 ≠ target z.2 z.1).card

theorem clashes_le_twice_errors (target : ι → ι → Bool) (color : ι → α)
    (sig : ι → ι → σ) (out : Finset ι → σ → Bool)
    (hs : ∀ x y, color x = color y → sig x y = sig y x) :
    clashes target color ≤ 2 * errors target sig out := by
  classical
  let E : Finset (ι × ι) := Finset.univ.filter fun z => out {z.1,z.2} (sig z.1 z.2) ≠ target z.1 z.2
  let C : Finset (ι × ι) := Finset.univ.filter fun z => color z.1 = color z.2 ∧ target z.1 z.2 ≠ target z.2 z.1
  let rev : (ι × ι) ↪ (ι × ι) := (Equiv.prodComm ι ι).toEmbedding
  have hh : C ⊆ E ∪ E.map rev := by
    rintro ⟨x, y⟩ hz
    have hc : color x = color y ∧ target x y ≠ target y x := (Finset.mem_filter.mp hz).2
    rw [Finset.mem_union]
    by_cases he : out {x,y} (sig x y) ≠ target x y
    · left
      simp [E, he]
    · right
      refine Finset.mem_map.mpr ⟨(y,x), ?_, rfl⟩
      have hh : out {y,x} (sig y x) = target x y := by
        rw [Finset.pair_comm, ← hs _ _ hc.1]
        exact not_not.mp he
      simp [E, hh, hc.2]
  change C.card ≤ 2 * E.card
  calc
    _ ≤ (E ∪ E.map rev).card := Finset.card_le_card hh
    _ ≤ _ := by simpa [two_mul] using (Finset.card_union_le E (E.map rev))

noncomputable def upperOut (target : ι → ι → Bool) [DecidableEq σ]
    (sig : ι → ι → σ) (pair : Finset ι) (round : σ) : Bool :=
  decide (∃ x y, ({x,y} : Finset ι) = pair ∧ sig x y = round ∧ target x y = true)

theorem two_errors_le_clashes (target : ι → ι → Bool) (color : ι → α)
    [DecidableEq σ] (sig : ι → ι → σ)
    (hd : ∀ x y, color x ≠ color y → sig x y ≠ sig y x) :
    2 * errors target sig (upperOut target sig) ≤ clashes target color := by
  classical
  let E : Finset (ι × ι) := Finset.univ.filter fun z =>
    upperOut target sig {z.1,z.2} (sig z.1 z.2) ≠ target z.1 z.2
  let C : Finset (ι × ι) := Finset.univ.filter fun z => color z.1 = color z.2 ∧ target z.1 z.2 ≠ target z.2 z.1
  let rev : (ι × ι) ↪ (ι × ι) := (Equiv.prodComm ι ι).toEmbedding
  have heinfo (x y : ι) (h : (x,y) ∈ E) :
      target x y = false ∧ target y x = true ∧ color x = color y := by
    have hn : upperOut target sig {x,y} (sig x y) ≠ target x y := (Finset.mem_filter.mp h).2
    have hf : target x y = false := by
      cases hb : target x y
      · rfl
      · exfalso
        apply hn
        rw [hb]
        exact decide_eq_true ⟨x,y,rfl,rfl,hb⟩
    have ht : upperOut target sig {x,y} (sig x y) = true := by simpa [hf] using hn
    obtain ⟨a,b,hpair,hsig,htrue⟩ := of_decide_eq_true ht
    have ha : a = x ∨ a = y := by
      have hh : a ∈ ({a,b} : Finset ι) := by simp
      simpa [hpair] using hh
    have hb : b = x ∨ b = y := by
      have hh : b ∈ ({a,b} : Finset ι) := by simp
      simpa [hpair] using hh
    have hne : x ≠ y := by
      intro hxy
      subst y
      simp at ha hb
      subst a
      subst b
      simp [hf] at htrue
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exfalso
      rw [ha,hb] at hpair
      have hh : y ∈ ({x,y} : Finset ι) := by simp
      rw [← hpair] at hh
      exact hne ((by simpa using hh : y = x).symm)
    · simp [ha,hb,hf] at htrue
    · rw [ha,hb] at htrue hsig
      exact ⟨hf, htrue, by_contra fun hh => hd _ _ hh hsig.symm⟩
    · exfalso
      rw [ha,hb] at hpair
      have hh : x ∈ ({x,y} : Finset ι) := by simp
      rw [← hpair] at hh
      exact hne (by simpa using hh)
  have hs : E ∪ E.map rev ⊆ C := by
    rintro ⟨x,y⟩ h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨hf,ht,hc⟩ := heinfo x y h
      simp [C, hc, hf, ht]
    · obtain ⟨⟨a,b⟩,hab,heq⟩ := Finset.mem_map.mp h
      change (b,a) = (x,y) at heq
      cases heq
      obtain ⟨hf,ht,hc⟩ := heinfo y x hab
      simp [C, hc.symm, hf, ht]
  have hdj : Disjoint E (E.map rev) := by
    refine Finset.disjoint_left.mpr ?_
    rintro ⟨x,y⟩ he hm
    obtain ⟨⟨a,b⟩,hab,heq⟩ := Finset.mem_map.mp hm
    change (b,a) = (x,y) at heq
    cases heq
    have hf := (heinfo y x hab).1
    have ht := (heinfo x y he).2.1
    simp [hf] at ht
  change 2 * E.card ≤ C.card
  calc
    _ = (E ∪ E.map rev).card := by simp [Finset.card_union_of_disjoint hdj, two_mul]
    _ ≤ _ := Finset.card_le_card hs

end Count

end PEqualNP.Outside.L_meta_25759_aux

namespace PEqualNP.Outside.L_meta_25759_aux

open scoped BigOperators

def signInt (b : Bool) : ℤ := if b then -1 else 1

@[simp] theorem signInt_false : signInt false = 1 := rfl
@[simp] theorem signInt_true : signInt true = -1 := rfl

theorem signInt_xor (a b : Bool) : signInt (xor a b) = signInt a * signInt b := by
  cases a <;> cases b <;> decide

@[simp] theorem signInt_mul_self (a : Bool) : signInt a * signInt a = 1 := by
  cases a <;> decide

@[simp] theorem coe_signInt (a : Bool) : (signInt a : ℝ) = bitSign a := by
  cases a <;> norm_num

section Count

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

def swapTrace (target : ι → ι → Bool) (s : Finset ι) : ℤ :=
  ∑ x ∈ s, ∑ y ∈ s, signInt (target x y) * signInt (target y x)

def localClashes (target : ι → ι → Bool) (s : Finset ι) : ℕ :=
  ((s ×ˢ s).filter fun z => target z.1 z.2 ≠ target z.2 z.1).card

omit [Fintype ι] [DecidableEq ι] in
theorem square_eq_localClashes_add_trace (target : ι → ι → Bool) (s : Finset ι) :
    (s.card : ℤ)^2 = 2 * localClashes target s + swapTrace target s := by
  classical
  let t := s ×ˢ s
  have h : ∀ z ∈ t, (1 : ℤ) =
      2 * (if target z.1 z.2 ≠ target z.2 z.1 then 1 else 0) +
        signInt (target z.1 z.2) * signInt (target z.2 z.1) := by
    intro z _
    cases target z.1 z.2 <;> cases target z.2 z.1 <;> decide
  have hh := Finset.sum_congr rfl h
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  have hcard : (∑ z ∈ t, (if target z.1 z.2 ≠ target z.2 z.1 then 1 else 0 : ℤ)) =
      localClashes target s := by
    rw [← Finset.sum_filter]
    simp [t, localClashes]
  rw [hcard] at hh
  simpa [t, swapTrace, Finset.sum_product, Finset.card_product, pow_two] using hh

def cls (color : ι → α) (a : α) : Finset ι := Finset.univ.filter (fun x => color x = a)

omit [DecidableEq ι] in
theorem sum_cls (color : ι → α) : (∑ a, (cls color a).card) = Fintype.card ι := by
  simpa [cls] using (Finset.sum_card_fiberwise_eq_card_filter Finset.univ Finset.univ color)

theorem sum_local_clashes (target : ι → ι → Bool) (color : ι → α) :
    (∑ a, localClashes target (cls color a)) = clashes target color := by
  let all := (Finset.univ : Finset (ι × ι)).filter fun z =>
    color z.1 = color z.2 ∧ target z.1 z.2 ≠ target z.2 z.1
  have h (a : α) : localClashes target (cls color a) = (all.filter fun z => color z.1 = a).card := by
    unfold localClashes
    congr 1
    ext z
    simp only [Finset.mem_filter, Finset.mem_product, cls, Finset.mem_univ, true_and, all]
    constructor
    · rintro ⟨⟨h₁,h₂⟩,hd⟩
      exact ⟨⟨h₁.trans h₂.symm,hd⟩, h₁⟩
    · rintro ⟨⟨he,hd⟩,h₁⟩
      exact ⟨⟨h₁,he.symm.trans h₁⟩,hd⟩
  simpa [h, clashes, all] using
    (Finset.sum_card_fiberwise_eq_card_filter all Finset.univ (fun z => color z.1))

theorem lower_of_trace_bound (target : ι → ι → Bool) (color : ι → α) (c : ℤ)
    (h : ∀ a, swapTrace target (cls color a) ≤ c * (cls color a).card) :
    (Fintype.card ι : ℤ)^2 ≤ (Fintype.card α : ℤ) *
      (2 * clashes target color + c * (Fintype.card ι : ℤ)) := by
  let n (a : α) : ℤ := (cls color a).card
  have hn : (∑ a, n a) = (Fintype.card ι : ℤ) := by
    change (∑ a, ((cls color a).card : ℤ)) = (Fintype.card ι : ℤ)
    exact_mod_cast sum_cls color
  have h1 : (∑ a, (n a)^2) ≤ 2 * clashes target color + c * (Fintype.card ι : ℤ) := by
    have h2 : (∑ a, (n a)^2) ≤ ∑ a, (2 * localClashes target (cls color a) + c * n a) := by
      apply Finset.sum_le_sum
      intro a _
      rw [show (n a)^2 = 2 * localClashes target (cls color a) + swapTrace target (cls color a) from
        square_eq_localClashes_add_trace target (cls color a)]
      exact add_le_add (le_refl _) (h a)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hn] at h2
    have hc : (∑ a, (localClashes target (cls color a) : ℤ)) = (clashes target color : ℤ) := by
      exact_mod_cast sum_local_clashes target color
    simpa [hc] using h2
  have h2 : (∑ a, n a)^2 ≤ (Fintype.card α : ℤ) * ∑ a, (n a)^2 := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset α)) (f := n))
  rw [hn] at h2
  exact h2.trans (mul_le_mul_of_nonneg_left h1 (by positivity))

theorem sum_squares_eq (target : ι → ι → Bool) (color : ι → α) :
    (∑ a, ((cls color a).card : ℤ)^2) =
      2 * (clashes target color : ℤ) + ∑ a, swapTrace target (cls color a) := by
  have h (a : α) := square_eq_localClashes_add_trace target (cls color a)
  calc
    _ = ∑ a, (2 * (localClashes target (cls color a) : ℤ) + swapTrace target (cls color a)) :=
      Finset.sum_congr rfl fun a _ => h a
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      have hc : (∑ a, (localClashes target (cls color a) : ℤ)) = (clashes target color : ℤ) := by
        exact_mod_cast sum_local_clashes target color
      rw [hc]

end Count

end PEqualNP.Outside.L_meta_25759_aux

namespace PEqualNP.Outside.L_meta_25759_aux

open scoped BigOperators

def coordOf {k a : ℕ} (π : Equiv.Perm (Fin (2^k))) (x : Fin (2^k)) : Fin (2^a) :=
  ⟨(π x).val % 2^a, Nat.mod_lt _ (by positivity)⟩

theorem residueFiberCard {k a : ℕ} (hka : a ≤ k) (π : Equiv.Perm (Fin (2^k)))
    (j : Fin (2^a)) : (cls (coordOf π) j).card = 2^(k-a) := by
  classical
  have hp : (2:ℕ)^k = 2^(k-a) * 2^a := by rw [← pow_add, Nat.sub_add_cancel hka]
  let e : Fin (2^k) ≃ Fin (2^(k-a)) × Fin (2^a) := π.trans ((finCongr hp).trans finProdFinEquiv.symm)
  have he (x : Fin (2^k)) : coordOf π x = (e x).2 := by
    apply Fin.ext
    rfl
  let f : Fin (2^(k-a)) ↪ Fin (2^k) := ⟨fun i => e.symm (i,j), by
    intro i j h
    exact congrArg Prod.fst (e.symm.injective h)⟩
  have heq : cls (coordOf π) j = Finset.univ.map f := by
    ext x
    constructor
    · intro hx
      have hxj : (e x).2 = j := by simpa [cls, he] using hx
      refine Finset.mem_map.mpr ⟨(e x).1, Finset.mem_univ _, ?_⟩
      change e.symm ((e x).1,j) = x
      rw [← hxj]
      exact e.symm_apply_apply x
    · intro hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx
      simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and, he]
      change (e (e.symm (i,j))).2 = j
      rw [e.apply_symm_apply]
  rw [heq, Finset.card_map]
  simp

def rawSigned {k a : ℕ} (flip : Fin (2^k) → Bool) (x : Fin (2^k)) (i : Fin (2^a)) : ℤ :=
  signInt (flip x) * signInt (x.val.testBit i.val)

theorem selectorFiberEnergy {k a : ℕ} (ha : 4 ≤ a) (hk : 2^a ≤ k) (hka : a ≤ k)
    (π : Equiv.Perm (Fin (2^k))) (flip : Fin (2^k) → Bool) (s : Finset (Fin (2^k)))
    (j : Fin (2^a)) :
    (∑ b, (moment s (coordOf π) (rawSigned flip) j b)^2) ≤
      (2 * a * 2^(k-a) : ℤ) * (s.filter fun x => coordOf π x = j).card := by
  classical
  let F := s.filter fun x => coordOf π x = j
  let e := finBitsEquiv k
  let U := F.map e.toEmbedding
  let ff (x : Fin k → Bool) := flip (e.symm x)
  let inc : Fin (2^a) ↪ Fin k := ⟨fun i => ⟨i.val, i.isLt.trans_le hk⟩,
    fun _ _ h => Fin.ext (congrArg (fun q : Fin k => q.val) h)⟩
  have hp : (2:ℝ)^k = 2^(k-a) * 2^a := by rw [← pow_add, Nat.sub_add_cancel hka]
  have hkdiv : (2:ℝ)^k / 2^a = 2^(k-a) := by rw [hp]; exact mul_div_cancel_right₀ _ (by positivity)
  have hU : (U.card : ℝ) ≤ (2:ℝ)^k / 2^a := by
    rw [hkdiv]
    have hf : F.card ≤ 2^(k-a) := by
      rw [← residueFiberCard hka π j]
      apply Finset.card_le_card
      simp only [F, cls, Finset.filter_subset_filter, Finset.subset_univ]
    simpa [U] using (show (F.card : ℝ) ≤ (2:ℝ)^(k-a) by exact_mod_cast hf)
  have hm (i : Fin (2^a)) : (moment s (coordOf π) (rawSigned flip) j i : ℝ) =
      signedMoment U ff (inc i) := by
    have hh : moment s (coordOf π) (rawSigned flip) j i = ∑ x ∈ F, rawSigned flip x i := by
      simp [moment, F, Finset.sum_filter]
    rw [hh, Int.cast_sum, signedMoment]
    dsimp [U]
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro x _
    change (rawSigned flip x i : ℝ) = bitSign (flip (e.symm (e x))) * bitSign ((e x) (inc i))
    rw [e.symm_apply_apply]
    simp only [rawSigned, Int.cast_mul, coe_signInt] <;> rfl
  have hmain := cube_energy_density ha U ff hU
  simp only [hkdiv, U, Finset.card_map] at hmain
  have hsub : (∑ b : Fin (2^a), (signedMoment U ff (inc b))^2) ≤
      ∑ b : Fin k, (signedMoment U ff b)^2 := by
    calc
      _ = ∑ i ∈ (Finset.univ : Finset (Fin (2^a))).map inc, (signedMoment U ff i)^2 :=
        (Finset.sum_map _ _ _).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  have hR := hsub.trans hmain
  simp only [← hm] at hR
  exact_mod_cast hR

theorem selectorTraceBound {k a : ℕ} (ha : 4 ≤ a) (hk : 2^a ≤ k) (hka : a ≤ k)
    (π : Equiv.Perm (Fin (2^k))) (rf cf : Fin (2^k) → Bool) (s : Finset (Fin (2^k))) :
    swapTrace (fun x y => xor (x.val.testBit (coordOf (a := a) π y).val) (xor (rf x) (cf (π y)))) s ≤
      (2 * a * 2^(k-a) : ℤ) * s.card := by
  let f (x : Fin (2^k)) := xor (rf x) (cf (π x))
  have hb := trace_bound_of_fibers s (coordOf π) (rawSigned f) _
    (selectorFiberEnergy ha hk hka π f s)
  convert hb using 1
  unfold swapTrace
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp only [signInt_xor, rawSigned, f]
  ring

theorem lowerMenu (k addrBits : ℕ) (ha : 4 ≤ addrBits) (hk : 2^addrBits ≤ k) :
    let N := 2^k
    let r := 2^addrBits
    let I := Fin N
    ∀ (q : ℕ) (op : Fin q → Bool → Bool → Bool),
      let D := ∏ t : Fin q, gateRadix (op t)
      ∀ (π : Equiv.Perm I) (rf cf : I → Bool) (R C : Fin q → I → Bool)
        (out : Finset I → (Fin q → Bool) → Bool),
        let H := fun x y => xor (x.val.testBit ((π y).val % r)) (xor (rf x) (cf (π y)))
        let e := errors H (fun x y t => op t (R t x) (C t (π y))) out
        r*N^2 ≤ 4*r*D*e + 2*addrBits*D*N^2 := by
  classical
  dsimp only
  intro q op π rf cf R C out
  let H := fun (x y : Fin (2^k)) => xor (x.val.testBit (coordOf (a := addrBits) π y).val) (xor (rf x) (cf (π y)))
  let S x y := fun t => op t (R t x) (C t (π y))
  let A := (t : Fin q) → Fin (gateRadix (op t))
  let N : ℕ := 2^k
  let r : ℕ := 2^addrBits
  let D : ℕ := ∏ t : Fin q, gateRadix (op t)
  change r*N^2 ≤ 4*r*D*errors H S out + 2*addrBits*D*N^2
  choose digits hd using fun t : Fin q => gate_color (op t)
  let color (x : Fin (2^k)) : A := fun t => digits t (R t x,C t (π x))
  have hc : ∀ x y, color x = color y → S x y = S y x := by
    intro x y he
    funext t
    exact hd t _ _ (congrFun he t)
  have hCol := clashes_le_twice_errors H color S out hc
  have hka : addrBits ≤ k := (Nat.lt_two_pow_self (n := addrBits)).le.trans hk
  have hl := lower_of_trace_bound H color (2 * addrBits * 2^(k-addrBits))
    (fun i => selectorTraceBound ha hk hka π rf cf (cls color i))
  have hdCard : Fintype.card A = D := by simp [A, D, Fintype.card_pi]
  rw [hdCard, Fintype.card_fin] at hl
  change (N : ℤ)^2 ≤ (D : ℤ) *
    (2 * (clashes H color : ℤ) + (2 * addrBits * 2^(k-addrBits) : ℤ) * N) at hl
  have hcolI : (clashes H color : ℤ) ≤ 2 * (errors H S out : ℤ) := by exact_mod_cast hCol
  have hbound : (N : ℤ)^2 ≤ (D : ℤ) *
    (4 * (errors H S out : ℤ) + (2 * addrBits * 2^(k-addrBits) : ℤ) * N) := by
    refine hl.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    linarith
  have hmul : (r : ℤ) * 2^(k-addrBits) = (N : ℤ) := by
    simp only [r, N, Nat.cast_pow, Nat.cast_ofNat]
    rw [← pow_add, Nat.add_sub_of_le hka]
  have hres := mul_le_mul_of_nonneg_left hbound (show (0 : ℤ) ≤ (r : ℤ) by positivity)
  have heq : (r : ℤ) * ((D : ℤ) *
        (4 * (errors H S out : ℤ) + (2 * addrBits * 2^(k-addrBits) : ℤ) * N)) =
      4 * (r : ℤ) * D * errors H S out + 2 * (addrBits : ℤ) * D * N^2 := by
    calc
      _ = 4 * (r : ℤ) * D * errors H S out + 2 * (addrBits : ℤ) * D * ((r : ℤ) * 2^(k-addrBits)) * N := by ring
      _ = _ := by rw [hmul]; ring
  rw [heq] at hres
  exact_mod_cast hres

end PEqualNP.Outside.L_meta_25759_aux

namespace PEqualNP.Outside.L_meta_25759_aux

open scoped BigOperators

section Bits

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def fixedBits (s : Finset ι) (pat : ι → Bool) : Finset (ι → Bool) :=
  Finset.univ.filter fun x => ∀ i ∈ s, x i = pat i

theorem fixedBits_card (s : Finset ι) (pat : ι → Bool) :
    (fixedBits s pat).card = 2 ^ (Fintype.card ι - s.card) := by
  classical
  let e : {x // x ∈ fixedBits s pat} ≃ ({i // i ∉ s} → Bool) := {
    toFun := fun x i => x.val i.val
    invFun := fun x => ⟨fun i => if h : i ∈ s then pat i else x ⟨i,h⟩, by
      simp only [fixedBits, Finset.mem_filter, Finset.mem_univ, true_and]
      intro i hi
      simp [hi]⟩
    left_inv := by
      intro x
      apply Subtype.ext
      funext i
      by_cases h : i ∈ s
      · have hx : ∀ i ∈ s, x.val i = pat i := (Finset.mem_filter.mp x.property).2
        simp [h, hx i h]
      · simp [h]
    right_inv := by
      intro x
      funext i
      simp [i.property]
  }
  have he := Fintype.card_congr e
  simpa [Fintype.card_subtype_compl, Fintype.card_fun] using he

theorem fixedBits_inter_same (s t : Finset ι) (pat : ι → Bool) :
    fixedBits s pat ∩ fixedBits t pat = fixedBits (s ∪ t) pat := by
  ext x
  simp [fixedBits, Finset.mem_union]
  constructor
  · rintro ⟨hs, ht⟩ i (hi | hi)
    · exact hs i hi
    · exact ht i hi
  · intro h
    exact ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩

end Bits

section Hall

variable {J Ω : Type*} [Fintype J] [DecidableEq J] [DecidableEq Ω]

theorem capacitated_hall (A : J → Finset Ω) (h : ℕ)
    (hc : ∀ s : Finset J, s.card * h ≤ (s.biUnion A).card) :
    ∃ f : J × Fin h → Ω, Function.Injective f ∧ ∀ j t, f (j,t) ∈ A j := by
  classical
  obtain ⟨f,hf,hm⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' (fun p : J × Fin h => A p.1)).mp (by
      intro s
      let t := s.image Prod.fst
      have hh : s ⊆ t ×ˢ (Finset.univ : Finset (Fin h)) := by
        intro p hp
        exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem Prod.fst hp, Finset.mem_univ _⟩
      have hu : t.biUnion A = s.biUnion (fun p => A p.1) := by
        ext x
        simp [t, Finset.mem_biUnion]
      calc
        s.card ≤ (t ×ˢ (Finset.univ : Finset (Fin h))).card := Finset.card_le_card hh
        _ = t.card * h := by simp
        _ ≤ (t.biUnion A).card := hc t
        _ = _ := congrArg Finset.card hu)
  exact ⟨f,hf,fun j t => hm (j,t)⟩

theorem cover_hall_of_intersections (A : J → Finset Ω) (h single overlap : ℕ)
    (hsingle : ∀ j, (A j).card = single) (hoverlap : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ overlap)
    (hpos : 0 < single)
    (hload : h * (single + (Fintype.card J - 1) * overlap) ≤ single^2) :
    ∀ s : Finset J, s.card * h ≤ (s.biUnion A).card := by
  classical
  intro s
  by_cases hs : s.Nonempty
  swap
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]
  let U := s.biUnion A
  let w (j : J) (x : Ω) : ℕ := if x ∈ A j then 1 else 0
  let m (x : Ω) := ∑ j ∈ s, w j x
  have subA (j : J) (hj : j ∈ s) : A j ⊆ U := by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨j,hj,hx⟩
  have hsum (j : J) (hj : j ∈ s) : (∑ x ∈ U, w j x) = single := by
    unfold w
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hfil : U.filter (fun x => x ∈ A j) = A j := by
      ext x
      exact Finset.mem_filter.trans (and_iff_right_of_imp (fun hx => subA j hj hx))
    rw [hfil]
    simpa using hsingle j
  have hfirst : (∑ x ∈ U, m x) = s.card * single := by
    unfold m
    rw [Finset.sum_comm]
    calc
      _ = ∑ j ∈ s, single := Finset.sum_congr rfl hsum
      _ = _ := by simp
  have hpair (i j : J) (hi : i ∈ s) : (∑ x ∈ U, w i x * w j x) = (A i ∩ A j).card := by
    unfold w
    simp only [ite_mul, one_mul, zero_mul, ← ite_and]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hfil : U.filter (fun x => x ∈ A i ∧ x ∈ A j) = A i ∩ A j := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_inter]
      exact and_iff_right_of_imp (fun hx => subA i hi hx.1)
    simp [hfil]
  have hsecond : (∑ x ∈ U, (m x)^2) ≤ s.card * (single + (Fintype.card J - 1) * overlap) := by
    unfold m
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ i ∈ s, ∑ j ∈ s, (A i ∩ A j).card := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun j _ => by simpa only [mul_comm] using hpair i j hi)
      _ ≤ ∑ _i ∈ s, (single + (Fintype.card J - 1) * overlap) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [← Finset.sum_erase_add _ _ hi, Finset.inter_self, hsingle]
        have hr : (∑ j ∈ s.erase i, (A i ∩ A j).card) ≤ (Fintype.card J - 1) * overlap := by
          calc
            _ ≤ ∑ _j ∈ s.erase i, overlap :=
              Finset.sum_le_sum fun _j hmem => hoverlap _ _ (Finset.ne_of_mem_erase hmem).symm
            _ = (s.erase i).card * overlap := by simp
            _ ≤ _ := by
              apply Nat.mul_le_mul_right
              rw [Finset.card_erase_of_mem hi]
              exact Nat.sub_le_sub_right (Finset.card_le_univ s) _
        omega
      _ = _ := by simp
  have hcs := sq_sum_le_card_mul_sum_sq (s := U) (f := m)
  rw [hfirst] at hcs
  have hb := hcs.trans (Nat.mul_le_mul_left U.card hsecond)
  let V := single + (Fintype.card J - 1) * overlap
  have hsmall : (s.card * h) * (s.card * V) ≤ (s.card * single)^2 := by
    have hh := Nat.mul_le_mul_left (s.card^2) hload
    convert hh using 1 <;> (try dsimp [V]) <;> ring
  have hc : (s.card * h) * (s.card * V) ≤ U.card * (s.card * V) := hsmall.trans hb
  exact Nat.le_of_mul_le_mul_right hc (Nat.mul_pos hs.card_pos (by dsimp [V]; omega))

end Hall

end PEqualNP.Outside.L_meta_25759_aux

namespace PEqualNP.Outside.L_meta_25759_aux

variable {I J : Type*}

def axisFlip (family : I → Option J) (mask : J → Bool) (w : I → Bool) (i : I) : Bool :=
  xor (w i) ((family i).elim false mask)

theorem axisFlip_axisFlip (family : I → Option J) (mask mask' : J → Bool) (w : I → Bool) :
    axisFlip family mask (axisFlip family mask' w) = axisFlip family (fun j => xor (mask j) (mask' j)) w := by
  funext i
  cases h : family i <;> simp [h, axisFlip]
  grind

def normalizedWords (anchor : J → I) := {w : I → Bool // ∀ j, w (anchor j) = false}

def normalizeWord (family : I → Option J) (anchor : J → I)
    (ha : ∀ j, family (anchor j) = some j) (w : I → Bool) : normalizedWords anchor :=
  ⟨axisFlip family (fun j => w (anchor j)) w, by
    intro j
    simp [axisFlip, ha]⟩

def wordAxes (family : I → Option J) (anchor : J → I) (ha : ∀ j, family (anchor j) = some j) :
    (I → Bool) ≃ normalizedWords anchor × (J → Bool) where
  toFun w := (normalizeWord family anchor ha w, fun j => w (anchor j))
  invFun z := axisFlip family z.2 z.1.val
  left_inv w := by
    funext i
    cases h : family i <;> simp [normalizeWord, axisFlip, h]
  right_inv z := by
    have hz (j : J) := z.1.property j
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      funext i
      cases h : family i <;> simp [normalizeWord, axisFlip, h, ha, hz]
    · funext j
      simp [axisFlip, ha, hz]

theorem normalizeWord_axisFlip (family : I → Option J) (anchor : J → I)
    (ha : ∀ j, family (anchor j) = some j) (mask : J → Bool) (w : I → Bool) :
    normalizeWord family anchor ha (axisFlip family mask w) = normalizeWord family anchor ha w := by
  apply Subtype.ext
  funext i
  cases h : family i with
  | none => simp [normalizeWord, axisFlip, ha, h]
  | some j =>
    simp [normalizeWord, axisFlip, ha, h]
    cases mask j <;> cases w (anchor j) <;> decide

theorem flip_block_counts_zero (family : I → Option J)
    (mask : J → Bool) (s : Finset (I → Bool)) (pivot extBit : I)
    (swap : (I → Bool) ≃ (I → Bool))
    (hswap : ∀ w, swap w = axisFlip family mask w)
    (hp : (family pivot).elim false mask = true)
    (he : (family extBit).elim false mask = false)
    (hs : ∀ w, swap w ∈ s ↔ w ∈ s) :
    (∑ w ∈ s, (if xor (w pivot) (w extBit) then (-1 : ℤ) else 1)) = 0 := by
  classical
  let f (w : I → Bool) : ℤ := if xor (w pivot) (w extBit) then -1 else 1
  have hneg (w) : f (swap w) = -f w := by
    simp only [f, hswap, axisFlip, hp, he]
    cases w pivot <;> cases w extBit <;> decide
  have hsum : (∑ w ∈ s, f w) = ∑ w ∈ s, f (swap w) := by
    symm
    apply Finset.sum_bij' (fun w _ => swap w) (fun w _ => swap.symm w)
    · intro w hw
      exact (hs w).2 hw
    · intro w hw
      exact (hs (swap.symm w)).1 (by simpa using hw)
    · intro w _
      exact swap.symm_apply_apply w
    · intro w _
      exact swap.apply_symm_apply w
    · intro w _
      rfl
  simp only [hneg, Finset.sum_neg_distrib] at hsum
  change (∑ w ∈ s, f w) = 0
  omega

end PEqualNP.Outside.L_meta_25759_aux

namespace PEqualNP.Outside.L_meta_25759_aux

open scoped BigOperators

theorem extend_slots {A X Y : Type*} [Fintype A] [Fintype X] [Fintype Y]
    (f : A ↪ X) (g : A ↪ Y) (hcard : Fintype.card X = Fintype.card Y) :
    ∃ e : X ≃ Y, ∀ a, e (f a) = g a := by
  classical
  let ex : A ≃ Set.range f := Equiv.ofInjective f f.injective
  let ey : A ≃ Set.range g := Equiv.ofInjective g g.injective
  have hx := Fintype.card_congr ex
  have hy := Fintype.card_congr ey
  let cx : ((Set.range f)ᶜ : Set X) ≃ ((Set.range g)ᶜ : Set Y) :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_compl_set, Fintype.card_compl_set, ← hx, ← hy, hcard])
  let mx := Equiv.Set.sumCompl (Set.range f)
  let my := Equiv.Set.sumCompl (Set.range g)
  let e := mx.symm.trans ((ex.symm.trans ey).sumCongr cx) |>.trans my
  refine ⟨e, fun a => ?_⟩
  have hm : mx.symm (f a) = Sum.inl (ex a) := by
    apply mx.injective
    simp [mx, ex]
  simp [e, hm, ey, my]

def slotColor {M D : ℕ} (hd : 0 < D) (x : Fin M) : Fin D :=
  ⟨x.val % D, Nat.mod_lt _ hd⟩

theorem slotColor_bounds {M D : ℕ} (hd : 0 < D) (z : Fin D) :
    M / D ≤ ((Finset.univ : Finset (Fin M)).filter (fun x => slotColor hd x = z)).card ∧
      ((Finset.univ : Finset (Fin M)).filter (fun x => slotColor hd x = z)).card ≤ M/D+1 := by
  let S := (Finset.univ : Finset (Fin M)).filter fun x => slotColor hd x = z
  have hz (x : Fin M) : x ∈ S ↔ x.val % D = z.val := by
    simp [S, slotColor, Fin.ext_iff]
  have hq : (M / D) * D ≤ M := Nat.div_mul_le_self ..
  constructor
  · let f (i : Fin (M/D)) : Fin M := ⟨i.val * D + z.val, by
      have hi : (i.val+1)*D ≤ M := (Nat.mul_le_mul_right D i.isLt).trans hq
      rw [Nat.add_mul] at hi
      have hzlt := z.isLt
      omega⟩
    have hf (i : Fin (M/D)) : f i ∈ S := by simp [hz, f, Nat.add_mod, Nat.mod_eq_of_lt z.isLt]
    have hi : Function.Injective f := by
      intro a b he
      apply Fin.ext
      have h := congrArg Fin.val he
      change a.val*D+z.val = b.val*D+z.val at h
      exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_right_cancel h)
    simpa using (Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin (M/D))))
      (t := S) f (fun a _ => hf a) hi.injOn)
  · let f (x : S) : Fin (M/D+1) := ⟨x.val.val / D, by
      exact Nat.lt_succ_of_le (Nat.div_le_div_right x.val.isLt.le)⟩
    have hi : Function.Injective f := by
      intro a b he
      apply Subtype.ext
      apply Fin.ext
      have h := congrArg Fin.val he
      change a.val.val / D = b.val.val / D at h
      have ha := (hz a.val).1 a.property
      have hb := (hz b.val).1 b.property
      calc
        a.val.val = (a.val.val % D) + D * (a.val.val / D) := (Nat.mod_add_div _ _).symm
        _ = (b.val.val % D) + D * (b.val.val / D) := by rw [ha, hb, h]
        _ = b.val.val := Nat.mod_add_div _ _
    simpa using Fintype.card_le_of_injective f hi

end PEqualNP.Outside.L_meta_25759_aux

namespace PEqualNP.Outside.L_meta_25759_aux

open scoped BigOperators

theorem balanced_squares {D : ℕ} (m : Fin D → ℤ) (q : ℤ)
    (hmin : ∀ i, q ≤ m i) (hmax : ∀ i, m i ≤ q+1) :
    4 * (D : ℤ) * (∑ i, (m i)^2) ≤ 4 * (∑ i, m i)^2 + (D : ℤ)^2 := by
  have hi (i : Fin D) : (m i)^2 ≤ (2*q+1)*m i - q*(q+1) := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hmin i)) (sub_nonpos.mpr (hmax i))]
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin D))) (fun i _ => hi i)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hs
  rw [mul_left_comm q (D : ℤ)] at hs
  let M : ℤ := ∑ i, m i
  change (∑ i, (m i)^2) ≤ (2*q+1)*M - (D : ℤ)*(q*(q+1)) at hs
  have hmul := mul_le_mul_of_nonneg_left hs (show (0:ℤ) ≤ 4 * D by positivity)
  change 4 * (D : ℤ) * (∑ i, (m i)^2) ≤ 4 * M^2 + (D : ℤ)^2
  nlinarith only [hmul, sq_nonneg (2 * (M - (D : ℤ)*q) - D)]

theorem final_upper_arithmetic (a r N D L b h e W : ℤ)
    (hr : r = 2*L*b) (hN : N = 2*L*h) (hab : a ≤ 4*b)
    (hr0 : 0 ≤ r) (hD : 1 ≤ D) (hDL : D ≤ L) (hb0 : 0 ≤ b)
    (hLoads : 4*D*W ≤ 4*N^2 + D^2*h^2)
    (hTrace : 4*e + L*h^2 ≤ W) :
    256*r*D*e + a*D*N^2 ≤ 64*r*N^2 := by
  have hDin : 0 ≤ D := by omega
  have hc := (mul_le_mul_of_nonneg_left hTrace (show 0 ≤ 4*D by positivity)).trans hLoads
  have hd : D^2*h^2 ≤ D*L*h^2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hDL (mul_nonneg hDin (sq_nonneg h))]
  have hcore : 16*D*e + 3*D*L*h^2 ≤ 4*N^2 := by linarith
  have htotal := mul_le_mul_of_nonneg_left hcore (show 0 ≤ 16*r by positivity)
  have haD : a*D ≤ 24*D*b := by
    have hA : a ≤ 24*b := by linarith
    nlinarith only [mul_le_mul_of_nonneg_right hA hDin]
  have haN := mul_le_mul_of_nonneg_right haD (sq_nonneg N)
  have heq : 24*D*b*N^2 = 48*r*D*L*h^2 := by rw [hr,hN]; ring
  rw [heq] at haN
  linarith

end PEqualNP.Outside.L_meta_25759_aux

namespace PEqualNP.Outside.L_meta_25759_aux

structure BlockParameters (k a : ℕ) where
  b : ℕ
  L : ℕ
  t : ℕ
  bTwo : 2 ≤ b
  bLower : 2*b ≤ a
  bUpper : a < 4*b
  Lpos : 0 < L
  coordSize : (2*L)*b = 2^a
  enoughBlocks : 2^(b-1) ≤ L
  exponentSize : L+1+a+t = k

theorem blockParameters_exists {k a : ℕ} (ha : 4 ≤ a) (hk : 2^a ≤ k) : Nonempty (BlockParameters k a) := by
  let d := (a/2).log2
  let b := 2^d
  let L := 2^(a-d-1)
  have hd : 1 ≤ d := by
    exact (Nat.le_log2 (show a/2 ≠ 0 by omega)).2 (show 2^1 ≤ a/2 by omega)
  have hbt : 2 ≤ b := by
    change (2:ℕ)^1 ≤ 2^d
    exact Nat.pow_le_pow_right (by decide) hd
  have hbl : 2*b ≤ a := by
    have hh : b ≤ a/2 := Nat.log2_self_le (by omega)
    omega
  have hbu : a < 4*b := by
    have hh : a/2 < 2^(d+1) := Nat.lt_log2_self
    rw [pow_succ] at hh
    omega
  have hdb : d < b := Nat.lt_two_pow_self
  have hL : 0 < L := by dsimp [L]; positivity
  have hcoord : (2*L)*b = 2^a := by
    dsimp [L,b]
    calc
      _ = 2^(1+(a-d-1)+d) := by rw [pow_add,pow_add]; simp
      _ = _ := by congr 1; omega
  have hLp : 2^(b-1) ≤ L := by
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hr16 : 16 ≤ 2^a := by
    change (2:ℕ)^4 ≤ 2^a
    exact Nat.pow_le_pow_right (by decide) ha
  have hL4 : 4*L ≤ 2^a := by
    rw [← hcoord]
    nlinarith [Nat.mul_le_mul_left (2*L) hbt]
  have ha2 : 2*a ≤ 2^a := by
    have hp : a ≤ 2^(a-1) := by
      have h' := Nat.lt_two_pow_self (n := a-1)
      omega
    calc
      2*a = a*2 := Nat.mul_comm _ _
      _ ≤ 2^(a-1) * 2 := Nat.mul_le_mul_right 2 hp
      _ = 2^a := by rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ a by omega)]
  have hexp : L+1+a ≤ k := by omega
  exact ⟨⟨b,L,k-(L+1+a),hbt,hbl,hbu,hL,hcoord,hLp,by omega⟩⟩

abbrev Coord (L b : ℕ) := Fin (2*L) × Fin b
abbrev Input (L b rest : ℕ) := Coord L b ⊕ Fin rest

def labelAxis {L b rest : ℕ} : Input L b rest → Option (Option (Fin L))
  | Sum.inr _ => none
  | Sum.inl (j, _) => if hj : j.val < L then some (some ⟨j.val,hj⟩) else some none

def activeBlock {L : ℕ} (j : Fin L) : Fin (2*L) := ⟨j.val, by have := j.isLt; omega⟩

def blockAnchor {L b rest : ℕ} (hL : 0 < L) (hb : 0 < b) : Option (Fin L) → Input L b rest
  | some j => Sum.inl (activeBlock j, ⟨0,hb⟩)
  | none => Sum.inl (⟨L,by omega⟩, ⟨0,hb⟩)

theorem axis_anchor {L b rest : ℕ} (hL : 0 < L) (hb : 0 < b) (j : Option (Fin L)) :
    labelAxis (blockAnchor (rest := rest) hL hb j) = some j := by
  cases j <;> simp [labelAxis, blockAnchor, activeBlock]

theorem anchor_injective {L b rest : ℕ} (hL : 0 < L) (hb : 0 < b) :
    Function.Injective (blockAnchor (rest := rest) hL hb) := by
  intro j m h
  have h' := congrArg labelAxis h
  simpa only [axis_anchor, Option.some.injEq] using h'

def blockOffsets {L b rest : ℕ} (j : Fin L) : Finset (Input L b rest) := by
  classical
  exact Finset.univ.map ⟨fun i : Fin (b-1) => Sum.inl (activeBlock j, ⟨i.val+1, by have := i.isLt; omega⟩), by
    intro x y h
    have ht := congrArg (fun q : Coord L b => q.2.val) (Sum.inl.inj h)
    change x.val+1 = y.val+1 at ht
    apply Fin.ext
    omega⟩

theorem card_offsets {L b rest : ℕ} (j : Fin L) : (blockOffsets (b := b) (rest := rest) j).card = b-1 := by
  simp [blockOffsets]

theorem offsets_disjoint {L b rest : ℕ} {j m : Fin L} (hjm : j ≠ m) :
    Disjoint (blockOffsets (b := b) (rest := rest) j) (blockOffsets m) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro z hz hw
  unfold blockOffsets at hz hw
  obtain ⟨u,_,hu⟩ := Finset.mem_map.mp hz
  obtain ⟨v,_,hv⟩ := Finset.mem_map.mp hw
  have hEq := Sum.inl.inj (hu.trans hv.symm)
  exact hjm (Fin.ext (congrArg (fun q : Coord L b => q.1.val) hEq))

theorem offsets_not_anchor {L b rest : ℕ} (hL : 0 < L) (hb : 0 < b)
    (j : Fin L) (q : Option (Fin L)) :
    blockAnchor (rest := rest) hL hb q ∉ blockOffsets j := by
  classical
  intro h
  unfold blockOffsets at h
  obtain ⟨i,_,hi⟩ := Finset.mem_map.mp h
  cases q <;> have he := Sum.inl.inj hi <;>
    have hm := congrArg (fun z : Coord L b => z.2.val) he <;> change i.val+1 = 0 at hm <;> omega

end PEqualNP.Outside.L_meta_25759_aux

namespace PEqualNP.Outside.L_meta_25759_aux

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]

noncomputable instance (a : J → I) : DecidableEq (normalizedWords a) := Classical.decEq _

noncomputable instance (a : J → I) : Fintype (normalizedWords a) := by
  classical
  unfold normalizedWords
  infer_instance

noncomputable def normalEvent (a : J → I) (s : Finset I) : Finset (normalizedWords a) := by
  classical
  exact Finset.univ.filter (fun w => ∀ i ∈ s, w.val i = false)

theorem normalEvent_card (a : J ↪ I) (s : Finset I) :
    (normalEvent a s).card = 2^(Fintype.card I - (Finset.univ.map a ∪ s).card) := by
  classical
  let P := Finset.univ.map a
  let B := fixedBits (P ∪ s) (fun _ => false)
  have hP (w : I → Bool) : (∀ j, w (a j) = false) ↔ ∀ i ∈ P, w i = false := by
    constructor
    · intro h i hi
      obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hi
      exact h j
    · intro h j
      exact h _ (Finset.mem_map.mpr ⟨j,Finset.mem_univ _,rfl⟩)
  have hB (w : I → Bool) : w ∈ B ↔ (∀ j, w (a j) = false) ∧ ∀ i ∈ s, w i = false := by
    unfold B
    rw [← fixedBits_inter_same]
    simp only [Finset.mem_inter, fixedBits, Finset.mem_filter, Finset.mem_univ, true_and, hP]
  let e : (normalEvent a s : Finset (normalizedWords a)) ≃ B := {
    toFun := fun w => ⟨w.val.val, (hB _).2 ⟨w.val.property, (Finset.mem_filter.mp w.property).2⟩⟩
    invFun := fun w => ⟨⟨w.val,((hB _).1 w.property).1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((hB _).1 w.property).2⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
  }
  have he : (normalEvent a s).card = B.card := by
    simpa using Fintype.card_congr e
  rw [he]
  exact fixedBits_card _ _

theorem card_normalized (a : J ↪ I) : Fintype.card (normalizedWords a) = 2^(Fintype.card I - Fintype.card J) := by
  classical
  simpa [normalEvent] using normalEvent_card a (∅ : Finset I)

theorem normalEvent_inter (a : J → I) (s t : Finset I) :
    normalEvent a s ∩ normalEvent a t = normalEvent a (s ∪ t) := by
  classical
  ext z
  simp only [normalEvent, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨hs,ht⟩ i (hi | hi)
    · exact hs i hi
    · exact ht i hi
  · intro h
    exact ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩

theorem event_load (K d L h : ℕ) (hK : 2*d ≤ K) (hL : 2^d ≤ L) (hfull : 2*L*h = 2^K) :
    h * (2^(K-d) + (L-1)*2^(K-2*d)) ≤ (2^(K-d))^2 := by
  have hc : 2^(K-d) = 2^(K-2*d)*2^d := by
    rw [← pow_add]
    congr 1
    omega
  have ht : 2^(K-d) * 2^d = 2^K := by rw [← pow_add]; congr 1; omega
  have hsq : (2^(K-d))^2 = 2^K * 2^(K-2*d) := by
    calc
      _ = 2^(K-d)*(2^(K-2*d)*2^d) := by rw [← hc, pow_two]
      _ = (2^(K-d)*2^d)*2^(K-2*d) := by ring
      _ = _ := by rw [ht]
  have hb : 2^(K-d) ≤ L*2^(K-2*d) := by
    rw [hc, mul_comm L]
    exact Nat.mul_le_mul_left _ hL
  have hh : 2^(K-d)+(L-1)*2^(K-2*d) ≤ (2*L)*2^(K-2*d) := by
    have hx := Nat.mul_le_mul_right (2^(K-2*d)) (Nat.sub_le L 1)
    nlinarith
  calc
    _ ≤ h*((2*L)*2^(K-2*d)) := Nat.mul_le_mul_left h hh
    _ = (2*L*h)*2^(K-2*d) := by ring
    _ = _ := by rw [hfull, hsq]

end PEqualNP.Outside.L_meta_25759_aux

namespace PEqualNP.Outside.L_meta_25759_aux

theorem active_mem_offsets {L b rest : ℕ} (j : Fin L) (u : Fin b) (hu : u.val ≠ 0) :
    Sum.inl (activeBlock j,u) ∈ blockOffsets (rest := rest) j := by
  classical
  unfold blockOffsets
  refine Finset.mem_map.mpr ⟨⟨u.val-1, ?_⟩, Finset.mem_univ _, ?_⟩
  · have := u.isLt
    omega
  · apply congrArg Sum.inl
    refine Prod.ext rfl (Fin.ext ?_)
    change u.val-1+1 = u.val
    omega

theorem choose_placement {k a : ℕ} (p : BlockParameters k a) (hk : 2^a ≤ k) :
    let X := Input p.L p.b (k-2^a)
    let anc : Option (Fin p.L) → X := blockAnchor p.Lpos (by have := p.bTwo; omega)
    ∃ e : normalizedWords anc ≃ Coord p.L p.b × Fin (2^p.t),
      ∀ w (j : Fin p.L) (u : Fin p.b), (e w).1.1 = activeBlock j →
        w.val (Sum.inl (activeBlock j,u)) = false := by
  classical
  dsimp only
  let b := p.b
  let L := p.L
  let X := Input L b (k-2^a)
  have hb : 0 < b := by have := p.bTwo; omega
  let anc : Option (Fin L) ↪ X := ⟨blockAnchor p.Lpos hb, anchor_injective p.Lpos hb⟩
  let A := Finset.univ.map anc
  let B (j : Fin L) := blockOffsets (rest := k-2^a) (b := b) j
  let E (j : Fin L) := normalEvent anc (B j)
  let K := k - (L+1)
  let d := b-1
  let h := b * 2^p.t
  have hX : Fintype.card X = k := by
    simp [X, Input, Coord, L, b, p.coordSize, Nat.add_sub_of_le hk]
  have hA : A.card = L+1 := by simp [A]
  have hB (j : Fin L) : (B j).card = d := card_offsets j
  have hab (i : Fin L) : Disjoint A (B i) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx hy
    obtain ⟨q,_,rfl⟩ := Finset.mem_map.mp hx
    exact offsets_not_anchor p.Lpos hb i q hy
  have hsingle (i : Fin L) : (E i).card = 2^(K-d) := by
    unfold E
    rw [normalEvent_card, Finset.card_union_of_disjoint (hab i), hA, hB, hX]
    rw [Nat.sub_sub]
  have hpair (i j : Fin L) (hij : i ≠ j) : (E i ∩ E j).card ≤ 2^(K-2*d) := by
    have hdij : Disjoint (B i) (B j) := offsets_disjoint hij
    have hD : Disjoint A (B i ∪ B j) := by
      refine Finset.disjoint_left.mpr ?_
      intro x hx hy
      rcases Finset.mem_union.mp hy with hy | hy
      · exact Finset.disjoint_left.mp (hab i) hx hy
      · exact Finset.disjoint_left.mp (hab j) hx hy
    unfold E
    rw [normalEvent_inter, normalEvent_card, Finset.card_union_of_disjoint hD,
      Finset.card_union_of_disjoint hdij, hA, hB, hB, hX]
    dsimp [K]
    apply Nat.pow_le_pow_right (by decide)
    omega
  have hK : 2*d ≤ K := by
    have he := p.exponentSize
    have hb := p.bLower
    dsimp [K,d,b,L]
    omega
  have hExp : K = a+p.t := by have he := p.exponentSize; dsimp [K,L]; omega
  have hFull : 2*L*h = 2^K := by
    rw [hExp, pow_add, ← p.coordSize]
    dsimp [h,b,L]
    ring
  have hE : ∀ s : Finset (Fin L), s.card*h ≤ (s.biUnion E).card := by
    apply cover_hall_of_intersections E h (2^(K-d)) (2^(K-2*d)) hsingle hpair (by positivity)
    rw [Fintype.card_fin]
    exact event_load K d L h hK p.enoughBlocks hFull
  obtain ⟨f,hinj,hmem⟩ := capacitated_hall E h hE
  let src : Fin L × Fin h ↪ normalizedWords anc := ⟨f,hinj⟩
  let split : Fin h ≃ Fin b × Fin (2^p.t) := finProdFinEquiv.symm
  let dst : Fin L × Fin h ↪ Coord L b × Fin (2^p.t) := ⟨fun z =>
    ((activeBlock z.1,(split z.2).1),(split z.2).2), by
      intro u v he
      apply Prod.ext
      · exact Fin.ext (congrArg (fun z : Coord L b × Fin (2^p.t) => z.1.1.val) he)
      · apply split.injective
        exact congrArg (fun z : Coord L b × Fin (2^p.t) => (z.1.2,z.2)) he⟩
  have hcard : Fintype.card (normalizedWords anc) = Fintype.card (Coord L b × Fin (2^p.t)) := by
    rw [card_normalized anc,hX]
    simp only [Fintype.card_option, Fintype.card_fin]
    change 2^K = _
    rw [← hFull]
    simp [Coord,h] <;> ring
  obtain ⟨e,he⟩ := extend_slots src dst hcard
  refine ⟨e,fun w j u hw => ?_⟩
  let i := split.symm ((e w).1.2,(e w).2)
  have hi : dst (j,i) = e w := by
    change ((activeBlock j,(split i).1),(split i).2) = e w
    simp only [i,Equiv.apply_symm_apply]
    exact Prod.ext (Prod.ext hw.symm rfl) rfl
  have hwf : src (j,i) = w := e.injective ((he (j,i)).trans hi)
  have hm : w ∈ E j := by rw [← hwf]; exact hmem j i
  by_cases hu : u.val = 0
  · have hu' : u = (⟨0,hb⟩ : Fin b) := Fin.ext hu
    subst u
    exact w.property (some j)
  · exact (Finset.mem_filter.mp hm).2 _ (active_mem_offsets j u hu)

end PEqualNP.Outside.L_meta_25759_aux

namespace PEqualNP.Outside.L_meta_25759_aux

open scoped BigOperators

variable {k a : ℕ}

abbrev LabelInput (p : BlockParameters k a) := Input p.L p.b (k-2^a)

def labelAnchor (p : BlockParameters k a) : Option (Fin p.L) → LabelInput p :=
  blockAnchor p.Lpos (by have := p.bTwo; omega)

abbrev Place (p : BlockParameters k a) := normalizedWords (labelAnchor p) ≃ Coord p.L p.b × Fin (2^p.t)

def coordEncode (p : BlockParameters k a) : Coord p.L p.b ≃ Fin (2^a) :=
  finProdFinEquiv.trans (finCongr p.coordSize)

def inputEncode (p : BlockParameters k a) (hk : 2^a ≤ k) : LabelInput p ≃ Fin k :=
  (Equiv.sumCongr (coordEncode p) (Equiv.refl _)).trans
    (finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hk)))

noncomputable def labelEncode (p : BlockParameters k a) (hk : 2^a ≤ k) : Fin (2^k) ≃ (LabelInput p → Bool) :=
  (finBitsEquiv k).trans ((inputEncode p hk).symm.arrowCongr (Equiv.refl Bool))

theorem labelEncode_inl (p : BlockParameters k a) (hk : 2^a ≤ k) (x : Fin (2^k)) (c : Coord p.L p.b) :
    labelEncode p hk x (Sum.inl c) = x.val.testBit (coordEncode p c).val := rfl

def placeAxis (p : BlockParameters k a) : LabelInput p → Option (Option (Fin p.L)) := labelAxis

theorem placeAxis_anchor (p : BlockParameters k a) (j : Option (Fin p.L)) :
    placeAxis p (labelAnchor p j) = some j := axis_anchor p.Lpos _ j

def wordLoc (p : BlockParameters k a) (e : Place p) (w : LabelInput p → Bool) : Coord p.L p.b :=
  (e (normalizeWord (placeAxis p) (labelAnchor p) (placeAxis_anchor p) w)).1

theorem wordLoc_flip (p : BlockParameters k a) (e : Place p) (mask : Option (Fin p.L) → Bool)
    (w : LabelInput p → Bool) : wordLoc p e (axisFlip (placeAxis p) mask w) = wordLoc p e w := by
  unfold wordLoc
  rw [normalizeWord_axisFlip]

def wordFlip (p : BlockParameters k a) (e : Place p) (w : LabelInput p → Bool) : Bool :=
  if h : (wordLoc p e w).1.val < p.L then
    w (labelAnchor p (some ⟨(wordLoc p e w).1.val,h⟩)) else false

noncomputable def matchingPair (p : BlockParameters k a) (hk : 2^a ≤ k) (e : Place p) :
    Fin (2^k) ≃ Fin (2^(k-a)) × Fin (2^a) := by
  let Q := Option (Fin p.L) → Bool
  let W := wordAxes (placeAxis p) (labelAnchor p) (placeAxis_anchor p)
  let shuffle : (Coord p.L p.b × Fin (2^p.t)) × Q ≃ (Fin (2^p.t) × Q) × Coord p.L p.b := {
    toFun := fun z => ((z.1.2,z.2),z.1.1)
    invFun := fun z => ((z.2,z.1.1),z.1.2)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
  }
  have hQ : Fintype.card (Fin (2^p.t) × Q) = 2^(k-a) := by
    simp [Q, ← pow_add]
    have h := p.exponentSize
    omega
  let E := (Fintype.equivFinOfCardEq hQ).prodCongr (coordEncode p)
  exact (labelEncode p hk).trans (W.trans ((e.prodCongr (Equiv.refl Q)).trans (shuffle.trans E)))

noncomputable def matchingπ (p : BlockParameters k a) (hk : 2^a ≤ k) (e : Place p) : Equiv.Perm (Fin (2^k)) := by
  have hN : (2:ℕ)^(k-a) * 2^a = 2^k := by
    rw [← pow_add, Nat.sub_add_cancel]
    exact (Nat.lt_two_pow_self (n := a)).le.trans hk
  exact (matchingPair p hk e).trans (finProdFinEquiv.trans (finCongr hN))

theorem matchingπ_coord (p : BlockParameters k a) (hk : 2^a ≤ k) (e : Place p) (x : Fin (2^k)) :
    coordOf (matchingπ p hk e) x = coordEncode p (wordLoc p e (labelEncode p hk x)) := by
  apply Fin.ext
  let y := coordEncode p (wordLoc p e (labelEncode p hk x))
  change (y.val + 2^a*(matchingPair p hk e x).1.val) % 2^a = y.val
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt y.isLt

end PEqualNP.Outside.L_meta_25759_aux

namespace PEqualNP.Outside.L_meta_25759_aux

open scoped BigOperators

theorem sum_negated_by_perm {I : Type*} (S : Finset I) (T : Equiv.Perm I) (f : I → ℤ)
    (hS : ∀ x, T x ∈ S ↔ x ∈ S) (hF : ∀ x ∈ S, f (T x) = -f x) :
    (∑ x ∈ S, f x) = 0 := by
  have hsum : (∑ x ∈ S, f x) = ∑ x ∈ S, f (T x) := by
    symm
    apply Finset.sum_bij' (fun x _ => T x) (fun x _ => T.symm x)
    · exact fun x hx => (hS x).2 hx
    · exact fun x hx => (hS (T.symm x)).1 (by simpa using hx)
    · exact fun x _ => T.symm_apply_apply x
    · exact fun x _ => T.apply_symm_apply x
    · exact fun _ _ => rfl
  have hsum' : (∑ x ∈ S, f (T x)) = -(∑ x ∈ S, f x) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl hF
  rw [hsum'] at hsum
  omega

variable {k a : ℕ}

def axisPerm (p : BlockParameters k a) (mask : Option (Fin p.L) → Bool) :
    Equiv.Perm (LabelInput p → Bool) := by
  let T := axisFlip (placeAxis p) mask
  have h : Function.Involutive T := by
    intro w
    funext i
    simp only [T,axisFlip]
    cases w i <;> cases (placeAxis p i).elim false mask <;> decide
  exact ⟨T,T,h,h⟩

theorem axis_active (p : BlockParameters k a) (j : Fin p.L) (v : Fin p.b) :
    placeAxis p (Sum.inl (activeBlock j,v)) = some (some j) := by
  simp [placeAxis, labelAxis, activeBlock]

theorem axis_selected_other (p : BlockParameters k a) (j : Fin p.L) (v : Coord p.L p.b)
    (hv : v.1 ≠ activeBlock j) :
    (placeAxis p (Sum.inl v)).elim false (fun z => decide (z=some j)) = false := by
  rcases v with ⟨g,b⟩
  by_cases h : g.val < p.L
  · have hne : (⟨g.val,h⟩ : Fin p.L) ≠ j := by
      intro he
      apply hv
      exact Fin.ext (congrArg (fun j : Fin p.L => j.val) he)
    simp [placeAxis, labelAxis, h, hne]
  · simp [placeAxis, labelAxis, h]

theorem axis_on_tested (p : BlockParameters k a) (v : Coord p.L p.b) :
    (placeAxis p (Sum.inl v)).elim false (fun _ => true) = true := by
  rcases v with ⟨g,b⟩
  by_cases h : g.val < p.L <;> simp [placeAxis, labelAxis, h]

theorem placed_fiber_card (p : BlockParameters k a) (hk : 2^a ≤ k) (e : Place p) (u : Coord p.L p.b) :
    (cls (fun x => wordLoc p e (labelEncode p hk x)) u).card = 2^(k-a) := by
  have ha := (Nat.lt_two_pow_self (n := a)).le.trans hk
  rw [← residueFiberCard ha (matchingπ p hk e) (coordEncode p u)]
  congr 1
  unfold cls
  apply Finset.filter_congr
  intro x _
  rw [matchingπ_coord, (coordEncode p).injective.eq_iff]

theorem placed_moment (p : BlockParameters k a) (hk : 2^a ≤ k) (e : Place p)
    (qualified : ∀ w (j : Fin p.L) (v : Fin p.b), (e w).1.1 = activeBlock j →
      w.val (Sum.inl (activeBlock j,v)) = false)
    (P : Coord p.L p.b → Prop) [DecidablePred P] (u v : Coord p.L p.b) :
    let loc := fun x => wordLoc p e (labelEncode p hk x)
    let sign := fun x c => signInt (xor (labelEncode p hk x (Sum.inl c)) (wordFlip p e (labelEncode p hk x)))
    moment (Finset.univ.filter (fun x => P (loc x))) loc sign u v =
      if P u ∧ u.1.val < p.L ∧ v.1 = u.1 then (2:ℤ)^(k-a) else 0 := by
  classical
  dsimp only
  let w := labelEncode p hk
  let loc (x : Fin (2^k)) := wordLoc p e (w x)
  let F := cls loc u
  let f (x : Fin (2^k)) := signInt (xor (w x (Sum.inl v)) (wordFlip p e (w x)))
  have hfib (x : Fin (2^k)) : x ∈ F ↔ loc x = u := by simp [F,cls]
  have hselect : moment (Finset.univ.filter (fun x => P (loc x))) loc
      (fun x c => signInt (xor (w x (Sum.inl c)) (wordFlip p e (w x)))) u v =
      ∑ x ∈ F, if P u then f x else 0 := by
    unfold moment
    rw [← Finset.sum_filter]
    by_cases ht : P u
    · simp only [ht, ite_true]
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hfib]
      constructor
      · exact And.right
      · intro hh
        exact ⟨hh ▸ ht,hh⟩
    · simp only [ht, ite_false, Finset.sum_const_zero]
      have hempty : ((Finset.univ.filter (fun x => P (loc x))).filter (fun x => loc x = u)) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rintro x ⟨hp,he⟩
        exact ht (he ▸ hp)
      simp [hempty]
  change _ = _
  rw [hselect]
  by_cases hp : P u
  swap
  · simp [hp]
  simp only [hp, true_and, ite_true]
  have hflip_pos (x : Fin (2^k)) (hx : loc x = u) (hu : u.1.val < p.L) :
      wordFlip p e (w x) = w x (labelAnchor p (some ⟨u.1.val,hu⟩)) := by
    unfold wordFlip
    change (if h : (loc x).1.val < p.L then w x (labelAnchor p (some ⟨(loc x).1.val,h⟩)) else false) = _
    simp [hx,hu]
  have hflip_neg (x : Fin (2^k)) (hx : loc x = u) (hu : ¬u.1.val < p.L) :
      wordFlip p e (w x) = false := by
    unfold wordFlip
    change (if h : (loc x).1.val < p.L then w x (labelAnchor p (some ⟨(loc x).1.val,h⟩)) else false) = _
    simp [hx, hu]
  let toggle (mask : Option (Fin p.L) → Bool) : Equiv.Perm (Fin (2^k)) :=
    w.trans ((axisPerm p mask).trans w.symm)
  have htoggle (mask : Option (Fin p.L) → Bool) (x : Fin (2^k)) :
      w (toggle mask x) = axisFlip (placeAxis p) mask (w x) := by
    change w (w.symm (axisFlip (placeAxis p) mask (w x))) = _
    rw [w.apply_symm_apply]
  have hloc (mask : Option (Fin p.L) → Bool) (x : Fin (2^k)) : loc (toggle mask x) = loc x := by
    change wordLoc p e (w (toggle mask x)) = _
    rw [htoggle, wordLoc_flip]
  by_cases hu : u.1.val < p.L
  · let j : Fin p.L := ⟨u.1.val,hu⟩
    have hj : activeBlock j = u.1 := Fin.ext rfl
    by_cases hv : v.1 = u.1
    · simp only [hu,hv,true_and,ite_true]
      have hall (x : Fin (2^k)) (hx : x ∈ F) : f x = 1 := by
        have hx' := (hfib x).1 hx
        have h := qualified (normalizeWord (placeAxis p) (labelAnchor p) (placeAxis_anchor p) (w x)) j v.2 (by
          change (loc x).1 = activeBlock j
          rw [hx',hj])
        have hv' : v = (activeBlock j,v.2) := Prod.ext (hv.trans hj.symm) rfl
        change axisFlip _ _ (w x) _ = false at h
        simp [axisFlip, axis_active] at h
        unfold f
        rw [hflip_pos x hx' hu, show w x (Sum.inl v) = w x (Sum.inl (activeBlock j,v.2)) from congrArg (fun c => w x (Sum.inl c)) hv']
        change signInt (xor _ (w x (labelAnchor p (some j)))) = 1
        simp [h]
      rw [Finset.sum_congr rfl hall]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      have hc := placed_fiber_card p hk e u
      change (cls loc u).card = _ at hc
      change ((cls loc u).card : ℤ) = _
      exact_mod_cast hc
    · simp only [hu,hv,and_false,ite_false]
      let m (z : Option (Fin p.L)) := decide (z = some j)
      refine sum_negated_by_perm F (toggle m) f (fun x => by simp only [hfib,hloc]) ?_
      intro x hx
      have hx' := (hfib x).1 hx
      have hxt := (hloc m x).trans hx'
      have hxv : v.1 ≠ activeBlock j := fun hh => hv (hh.trans hj)
      unfold f
      rw [hflip_pos (toggle m x) hxt hu, hflip_pos x hx' hu, htoggle]
      have ht : decide (some (⟨u.1.val,hu⟩ : Fin p.L) = some j) = true := decide_eq_true rfl
      simp only [axisFlip, axis_selected_other p j v hxv, placeAxis_anchor, Option.elim_some, m, ht]
      cases w x (Sum.inl v) <;> cases w x (labelAnchor p (some j)) <;> decide
  · simp only [hu,false_and,ite_false]
    let m : Option (Fin p.L) → Bool := fun _ => true
    refine sum_negated_by_perm F (toggle m) f (fun x => by simp only [hfib,hloc]) ?_
    intro x hx
    have hx' := (hfib x).1 hx
    have hxt := (hloc m x).trans hx'
    unfold f
    rw [hflip_neg (toggle m x) hxt hu, hflip_neg x hx' hu, htoggle]
    simp only [axisFlip, m, axis_on_tested]
    cases w x (Sum.inl v) <;> decide

end PEqualNP.Outside.L_meta_25759_aux

namespace PEqualNP.Outside.L_meta_25759_aux

open scoped BigOperators

theorem block_product_sum {M b : ℕ} (good : Fin M → Prop) [DecidablePred good]
    (H : ℤ) (m : (Fin M × Fin b) → (Fin M × Fin b) → ℤ)
    (hm : ∀ u v, m u v = if good u.1 ∧ v.1 = u.1 then H else 0) :
    (∑ u, ∑ v, m u v * m v u) =
      ((Finset.univ.filter good).card : ℤ) * ((b : ℤ)*H)^2 := by
  classical
  have hs (u v : Fin M × Fin b) : m u v = m v u := by
    rw [hm,hm]
    by_cases he : v.1 = u.1
    · simp [he]
    · simp [he,Ne.symm he]
  have hline (u : Fin M × Fin b) : (∑ v, m u v * m v u) =
      if good u.1 then (b : ℤ)*H^2 else 0 := by
    simp only [← hs u, hm, Fintype.sum_prod_type]
    by_cases he : good u.1
    · simp [he, Finset.sum_ite_eq', pow_two]
    · simp [he]
  simp_rw [hline]
  rw [Fintype.sum_prod_type]
  have hc (i : Fin M) : (∑ _j : Fin b, if good i then (b : ℤ)*H^2 else 0) =
      if good i then ((b : ℤ)*H)^2 else 0 := by
    by_cases hi : good i <;> simp [hi] <;> ring
  simp_rw [hc]
  rw [← Finset.sum_filter]
  simp

theorem support_card_of_fibers {ι : Type*} [Fintype ι] {M b H : ℕ}
    (loc : ι → Fin M × Fin b) (good : Fin M → Prop) [DecidablePred good]
    (hf : ∀ u, (cls loc u).card = H) :
    ((Finset.univ : Finset ι).filter (fun x => good (loc x).1)).card =
      ((Finset.univ : Finset (Fin M)).filter good).card * (b*H) := by
  let S := (Finset.univ : Finset ι).filter (fun x => good (loc x).1)
  have hx (u : Fin M × Fin b) : (S.filter (fun x => loc x = u)).card =
      if good u.1 then H else 0 := by
    by_cases he : good u.1
    · rw [if_pos he,←hf u]
      congr 1
      ext x
      simp only [S,cls,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · exact And.right
      · intro hh
        exact ⟨hh ▸ he,hh⟩
    · rw [if_neg he]
      have hempty : S.filter (fun x => loc x = u) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
        rintro x ⟨h,hh⟩
        exact he (hh ▸ h)
      simp [hempty]
  have hS : (∑ u, (S.filter (fun x => loc x = u)).card) = S.card := by
    simpa using (Finset.sum_card_fiberwise_eq_card_filter S Finset.univ loc)
  change S.card = _
  rw [← hS]
  simp_rw [hx]
  rw [Fintype.sum_prod_type]
  have h (i : Fin M) : (∑ _j : Fin b, if good i then H else 0) = if good i then b*H else 0 := by
    by_cases hi : good i <;> simp [hi]
  simp_rw [h]
  rw [← Finset.sum_filter]
  simp

theorem active_block_count (L : ℕ) :
    ((Finset.univ : Finset (Fin (2*L))).filter (fun i => i.val < L)).card = L := by
  let inc : Fin L ↪ Fin (2*L) := ⟨fun i => ⟨i.val,by have := i.isLt; omega⟩,
    fun _ _ h => Fin.ext (congrArg (fun x : Fin (2*L) => x.val) h)⟩
  have h : (Finset.univ : Finset (Fin (2*L))).filter (fun i => i.val < L) = Finset.univ.map inc := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_map]
    constructor
    · exact fun hi => ⟨⟨i.val,hi⟩,rfl⟩
    · rintro ⟨j,rfl⟩
      exact j.isLt
  simp [h]

theorem totalBlock_square_bound (D M : ℕ) (hD : 0 < D) :
    4 * (D : ℤ) * (∑ z : Fin D, ((cls (slotColor (M := M) hD) z).card : ℤ)^2) ≤
      4 * (M : ℤ)^2 + (D : ℤ)^2 := by
  let m (z : Fin D) : ℤ := (cls (slotColor (M := M) hD) z).card
  have hb := balanced_squares m ((M/D : ℕ) : ℤ)
    (fun z => by dsimp [m]; exact_mod_cast (slotColor_bounds (M := M) hD z).1)
    (fun z => by dsimp [m]; exact_mod_cast (slotColor_bounds (M := M) hD z).2)
  have hm : (∑ z, m z) = (M : ℤ) := by
    dsimp [m]
    exact_mod_cast (show (∑ z, (cls (slotColor (M := M) hD) z).card) = M by simpa using
      (sum_cls (slotColor (M := M) hD)))
  rw [hm] at hb
  exact hb

end PEqualNP.Outside.L_meta_25759_aux

namespace PEqualNP.Outside.L_meta_25759_aux

open scoped BigOperators

theorem gateRadix_pos (f : Bool → Bool → Bool) : 0 < gateRadix f := by
  unfold gateRadix
  dsimp only
  split
  · decide
  · split <;> decide

theorem upperMenu (k a : ℕ) (ha : 4 ≤ a) (hk : 2^a ≤ k) :
    let N := 2^k
    let r := 2^a
    let I := Fin N
    ∃ (π : Equiv.Perm I) (flip : I → Bool), ∀ (q : ℕ) (op : Fin q → Bool → Bool → Bool),
      let D := ∏ t : Fin q, gateRadix (op t)
      a*D ≤ r → ∃ (R C : Fin q → I → Bool) (out : Finset I → (Fin q → Bool) → Bool),
        let H := fun x y => xor (x.val.testBit ((π y).val % r)) (xor (flip x) false)
        let e := errors H (fun x y t => op t (R t x) (C t (π y))) out
        256*r*D*e + a*D*N^2 ≤ 64*r*N^2 := by
  classical
  dsimp only
  obtain ⟨p⟩ := blockParameters_exists ha hk
  obtain ⟨placement, qualified⟩ := choose_placement p hk
  let π := matchingπ p hk placement
  let word := labelEncode p hk
  let loc (x : Fin (2^k)) := wordLoc p placement (word x)
  let flip (x : Fin (2^k)) := wordFlip p placement (word x)
  let H (x y : Fin (2^k)) := xor (word x (Sum.inl (loc y))) (flip x)
  have hTruth (x y : Fin (2^k)) : H x y =
      xor (x.val.testBit ((π y).val % 2^a)) (xor (flip x) false) := by
    have hcoord : (π y).val % 2^a = (coordEncode p (loc y)).val :=
      congrArg Fin.val (matchingπ_coord p hk placement y)
    rw [hcoord]
    simp [H, word, labelEncode_inl]
  refine ⟨π,flip,fun q op hbudget => ?_⟩
  let D : ℕ := ∏ t : Fin q, gateRadix (op t)
  have hD : 0 < D := Finset.prod_pos fun t _ => gateRadix_pos (op t)
  have hDL : D ≤ p.L := by
    have hh : (2*p.b)*D ≤ (2*p.b)*p.L := by
      calc
        _ ≤ a*D := Nat.mul_le_mul_right D p.bLower
        _ ≤ 2^a := hbudget
        _ = _ := by rw [← p.coordSize]; ring
    exact Nat.le_of_mul_le_mul_left hh (by have := p.bTwo; positivity)
  let c (i : Fin (2*p.L)) := slotColor hD i
  let color (x : Fin (2^k)) := c (loc x).1
  let A := (t : Fin q) → Fin (gateRadix (op t))
  have hCardA : D = Fintype.card A := by simp [D,A,Fintype.card_pi]
  let eColor : Fin D ≃ A := Fintype.equivOfCardEq (by simpa using hCardA)
  choose dig hdig using fun t : Fin q => gate_embed (op t)
  let R (t : Fin q) (x : Fin (2^k)) := (dig t (eColor (color x) t)).1
  let C (t : Fin q) (x : Fin (2^k)) := (dig t (eColor (color (π.symm x)) t)).2
  let S (x y : Fin (2^k)) := fun t => op t (R t x) (C t (π y))
  have hSep (x y : Fin (2^k)) (hd : color x ≠ color y) : S x y ≠ S y x := by
    intro hs
    apply hd
    apply eColor.injective
    funext t
    by_contra hn
    exact hdig t _ _ hn (by simpa [S,R,C] using congrFun hs t)
  let out := upperOut H S
  let W : ℤ := ∑ z : Fin D, ((cls color z).card : ℤ)^2
  let B : ℤ := (p.b : ℤ) * (2:ℤ)^(k-a)
  let N : ℤ := (2:ℤ)^k
  let r : ℤ := (2:ℤ)^a
  have hN : N = (2*(p.L:ℤ))*B := by
    change (2:ℤ)^k = (2*(p.L:ℤ))*((p.b:ℤ)*2^(k-a))
    have hh : (2:ℕ)^k = (2*p.L)*(p.b*2^(k-a)) := by
      rw [← Nat.mul_assoc, p.coordSize, ← pow_add, Nat.add_sub_of_le ((Nat.lt_two_pow_self (n := a)).le.trans hk)]
    exact_mod_cast hh
  have hr : r = 2*(p.L:ℤ)*(p.b:ℤ) := by dsimp [r]; exact_mod_cast p.coordSize.symm
  have hcSize (z : Fin D) : (cls color z).card = (cls c z).card * (p.b*2^(k-a)) :=
    support_card_of_fibers loc (fun i => c i = z) (placed_fiber_card p hk placement)
  have hLoads : 4*(D:ℤ)*W ≤ 4*N^2 + (D:ℤ)^2*B^2 := by
    let V : ℤ := ∑ z : Fin D, ((cls c z).card : ℤ)^2
    have he : W = B^2*V := by
      unfold W V
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      simp only [hcSize, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, B]
      ring
    have hv : 4*(D:ℤ)*V ≤ 4*(2*(p.L:ℤ))^2+(D:ℤ)^2 := by
      simpa [V,c] using totalBlock_square_bound D (2*p.L) hD
    calc
      _ = B^2*(4*(D:ℤ)*V) := by rw [he]; ring
      _ ≤ B^2*(4*(2*(p.L:ℤ))^2+(D:ℤ)^2) := mul_le_mul_of_nonneg_left hv (sq_nonneg B)
      _ = _ := by rw [hN]; ring
  have hTraceLine (z : Fin D) : swapTrace H (cls color z) =
      ((Finset.univ.filter fun i : Fin (2*p.L) => c i = z ∧ i.val < p.L).card : ℤ)*B^2 := by
    let sign (x : Fin (2^k)) (u : Coord p.L p.b) := signInt (xor (word x (Sum.inl u)) (flip x))
    let m := moment (cls color z) loc sign
    have hEq : swapTrace H (cls color z) = ∑ u, ∑ v, m u v*m v u :=
      trace_identity (cls color z) loc sign
    rw [hEq]
    have hh (u v : Coord p.L p.b) : m u v =
        if (c u.1 = z ∧ u.1.val < p.L) ∧ v.1 = u.1 then (2:ℤ)^(k-a) else 0 := by
      simpa only [m,loc,sign,word,flip,cls,color,and_assoc] using
        placed_moment p hk placement qualified (fun w => c w.1 = z) u v
    exact block_product_sum (fun i : Fin (2*p.L) => c i = z ∧ i.val < p.L) _ m hh
  have hActive : (∑ z : Fin D,
      ((Finset.univ.filter fun i : Fin (2*p.L) => c i = z ∧ i.val < p.L).card : ℤ)) = (p.L : ℤ) := by
    let all := (Finset.univ : Finset (Fin (2*p.L))).filter (fun i => i.val < p.L)
    have hh : (∑ z : Fin D, (all.filter fun i => c i = z).card) = p.L := by
      calc
        _ = all.card := by simpa using (Finset.sum_card_fiberwise_eq_card_filter all Finset.univ c)
        _ = _ := active_block_count p.L
    push_cast
    exact_mod_cast (show (∑ z : Fin D, (Finset.univ.filter fun i : Fin (2*p.L) => c i = z ∧ i.val < p.L).card) = p.L by
      simpa [all,Finset.filter_filter,and_comm] using hh)
  have hTrace : (∑ z : Fin D, swapTrace H (cls color z)) = (p.L : ℤ)*B^2 := by
    simp_rw [hTraceLine]
    rw [← Finset.sum_mul,hActive]
  have hE := two_errors_le_clashes H color S hSep
  have hE' : 2*(errors H S out : ℤ) ≤ (clashes H color : ℤ) := by exact_mod_cast hE
  have hSum := sum_squares_eq H color
  rw [hTrace] at hSum
  change W = _ at hSum
  have hscore : 4*(errors H S out : ℤ) + (p.L : ℤ)*B^2 ≤ W := by linarith
  have hUpper := final_upper_arithmetic a r N D p.L p.b B (errors H S out) W hr hN
    (by exact_mod_cast p.bUpper.le) (by dsimp [r]; positivity) (by exact_mod_cast hD)
    (by exact_mod_cast hDL) (by positivity) hLoads hscore
  have hNat : 256*2^a*D*(errors H S out)+a*D*(2^k)^2 ≤ 64*2^a*(2^k)^2 := by
    dsimp only [r,N] at hUpper
    exact_mod_cast hUpper
  refine ⟨R,C,out,?_⟩
  change 256*2^a*D*errors (fun x y => xor (x.val.testBit ((π y).val % 2^a)) (xor (flip x) false)) S out
    + a*D*(2^k)^2 ≤ 64*2^a*(2^k)^2
  simp_rw [← hTruth]
  exact hNat

end PEqualNP.Outside.L_meta_25759_aux

theorem PEqualNP.Outside.L_meta_25759 : (∀ (k addrBits : ℕ), 4 ≤ addrBits → 2^addrBits ≤ k →
  let N := 2^k
  let r := 2^addrBits
  let I := Fin N
  let G := fun (x y : I) => x.val.testBit (y.val % r)
  let rad := fun (f : Bool → Bool → Bool) =>
    let ones := ((Finset.univ : Finset (Bool × Bool)).filter (fun z => f z.1 z.2)).card
    if ones = 0 ∨ ones = 4 then 1 else if ones = 2 then 2 else 3
  let errors := fun (q : ℕ) (op : Fin q → Bool → Bool → Bool) (π : Equiv.Perm I)
      (rf cf : I → Bool) (R C : Fin q → I → Bool) (out : Finset I → (Fin q → Bool) → Bool) =>
    ((Finset.univ : Finset (I × I)).filter (fun z =>
      out {z.1,z.2} (fun t => op t (R t z.1) (C t (π z.2))) ≠
        xor (G z.1 (π z.2)) (xor (rf z.1) (cf (π z.2))))).card
  (∀ (q : ℕ) (op : Fin q → Bool → Bool → Bool),
    let D := ∏ t : Fin q, rad (op t)
    ∀ (π : Equiv.Perm I) (rf cf : I → Bool) (R C : Fin q → I → Bool)
      (out : Finset I → (Fin q → Bool) → Bool),
      r*N^2 ≤ 4*r*D*errors q op π rf cf R C out + 2*addrBits*D*N^2) ∧
  ∃ (π : Equiv.Perm I) (flip : I → Bool), ∀ (q : ℕ) (op : Fin q → Bool → Bool → Bool),
    let D := ∏ t : Fin q, rad (op t)
    addrBits*D ≤ r → ∃ (R C : Fin q → I → Bool) (out : Finset I → (Fin q → Bool) → Bool),
      256*r*D*errors q op π flip (fun _ => false) R C out + addrBits*D*N^2 ≤ 64*r*N^2) := by
  intro k addrBits ha hk
  constructor
  · exact PEqualNP.Outside.L_meta_25759_aux.lowerMenu k addrBits ha hk
  · obtain ⟨π, flip, h⟩ := PEqualNP.Outside.L_meta_25759_aux.upperMenu k addrBits ha hk
    refine ⟨π, flip, ?_⟩
    intro q op
    dsimp only
    intro budget
    obtain ⟨R, C, out, score⟩ := h q op (by simpa only [PEqualNP.Outside.L_meta_25759_aux.gateRadix] using budget)
    refine ⟨R, C, out, ?_⟩
    simpa only [PEqualNP.Outside.L_meta_25759_aux.errors, PEqualNP.Outside.L_meta_25759_aux.gateRadix] using score
