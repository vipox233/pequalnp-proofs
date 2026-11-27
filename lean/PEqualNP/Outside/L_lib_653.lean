import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_653_aux

open scoped Classical

abbrev K := ZMod 2

private lemma zmod2_add_self (a : K) : a + a = 0 := by
  fin_cases a <;> rfl

private lemma zmod2_sub_eq_add (a b : K) : a - b = a + b := by
  fin_cases a <;> fin_cases b <;> rfl

private lemma zmod2_mul_self (a : K) : a * a = a := by
  fin_cases a <;> rfl

private lemma zmod2_add_add_cancel (a b : K) : a + (a + b) = b := by
  fin_cases a <;> fin_cases b <;> rfl

private lemma zmod2_neg (a : K) : -a = a := by
  fin_cases a <;> rfl

private lemma zmod2_add_eq_zero {a b : K} (h : a + b = 0) : a = b := by
  have h1 := congrArg (· + b) h
  simpa [add_assoc, zmod2_add_self] using h1

private lemma zmod2_eq_zero_or_one (a : K) : a = 0 ∨ a = 1 := by
  revert a; decide

private lemma zmod2_vadd_self {V : Type*} [AddCommGroup V] [Module K V] (v : V) :
    v + v = 0 := by
  calc v + v = (1 : K) • v + (1 : K) • v := by simp
    _ = ((1 : K) + (1 : K)) • v := (add_smul 1 1 v).symm
    _ = (0 : K) • v := by congr 1
    _ = 0 := zero_smul K v

private lemma zmod2_vneg {V : Type*} [AddCommGroup V] [Module K V] (v : V) :
    -v = v := neg_eq_iff_add_eq_zero.mpr (zmod2_vadd_self v)

private def MOp {k : ℕ} (d : ℕ) (x : ZMod k → K) : ZMod k → K :=
  fun i => x i + x (i + (d : ZMod k)) + x (i - (d : ZMod k))

private def AOp {k : ℕ} (x : ZMod k → K) : ZMod k → K :=
  fun i => x (i + 1) + x (i - 1)

private lemma MOp_add {k : ℕ} (d : ℕ) (x y : ZMod k → K) (i : ZMod k) :
    MOp d (x + y) i = MOp d x i + MOp d y i := by
  simp only [MOp, Pi.add_apply]
  ring

private lemma AOp_add {k : ℕ} (x y : ZMod k → K) (i : ZMod k) :
    AOp (x + y) i = AOp x i + AOp y i := by
  simp only [AOp, Pi.add_apply]
  ring

private lemma MOp_AOp_comm {k : ℕ} (d : ℕ) (x : ZMod k → K) :
    MOp d (AOp x) = AOp (MOp d x) := by
  funext i
  simp only [MOp, AOp]
  have h1 : i + 1 + (d : ZMod k) = i + (d : ZMod k) + 1 := by ring
  have h2 : i + 1 - (d : ZMod k) = i - (d : ZMod k) + 1 := by ring
  have h3 : i - 1 + (d : ZMod k) = i + (d : ZMod k) - 1 := by ring
  have h4 : i - 1 - (d : ZMod k) = i - (d : ZMod k) - 1 := by ring
  rw [h1, h2, h3, h4]
  ring

private lemma MOp_comp_MOp {k : ℕ} (d : ℕ) (x : ZMod k → K) :
    MOp d (MOp d x) = MOp (2 * d) x := by
  funext i
  simp only [MOp, Nat.cast_mul, Nat.cast_ofNat]
  have h1 : i + (d : ZMod k) - (d : ZMod k) = i := by ring
  have h2 : i - (d : ZMod k) + (d : ZMod k) = i := by ring
  have h3 : i + (d : ZMod k) + (d : ZMod k) = i + 2 * (d : ZMod k) := by ring
  have h4 : i - (d : ZMod k) - (d : ZMod k) = i - 2 * (d : ZMod k) := by ring
  rw [h1, h2, h3, h4]
  have hcancel : ∀ a b c : K, a + b + c + (b + a) = c := by
    intro a b c; fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl
  generalize x i = a
  generalize x (i + (d : ZMod k)) = b
  generalize x (i - (d : ZMod k)) = c
  generalize x (i + 2 * (d : ZMod k)) = p
  generalize x (i - 2 * (d : ZMod k)) = q
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases p <;> fin_cases q <;> rfl

private lemma MOp_self_adjoint {k : ℕ} [NeZero k] (d : ℕ) (f g : ZMod k → K) :
    ∑ i : ZMod k, MOp d f i * g i = ∑ i : ZMod k, f i * MOp d g i := by
  simp only [MOp, add_mul, mul_add, Finset.sum_add_distrib]
  have h1 : ∑ i : ZMod k, f (i + (d : ZMod k)) * g i =
      ∑ i : ZMod k, f i * g (i - (d : ZMod k)) := by
    refine Fintype.sum_equiv (Equiv.addRight (d : ZMod k)) _ _ fun i => ?_
    simp [Equiv.addRight]
  have h2 : ∑ i : ZMod k, f (i - (d : ZMod k)) * g i =
      ∑ i : ZMod k, f i * g (i + (d : ZMod k)) := by
    refine Fintype.sum_equiv (Equiv.subRight (d : ZMod k)) _ _ fun i => ?_
    simp [Equiv.subRight]
  rw [h1, h2]
  ring

private lemma period_two_step {k : ℕ} {a : ZMod k → K} (hA : AOp a = 0) (i : ZMod k) :
    a (i + 2) = a i := by
  have h := congrFun hA (i + 1)
  simp only [AOp, Pi.zero_apply] at h
  have h1 : i + 1 + 1 = i + 2 := by ring
  have h2 : i + 1 - 1 = i := by ring
  rw [h1, h2] at h
  have h3 := congrArg (· + a i) h
  simpa [add_assoc, zmod2_add_self] using h3

private lemma period_two_mul {k : ℕ} {a : ZMod k → K} (hA : AOp a = 0) (d : ℕ) (i : ZMod k) :
    a (i + (2 * d : ℕ)) = a i ∧ a (i - (2 * d : ℕ)) = a i := by
  induction d generalizing i with
  | zero => simp
  | succ d ih =>
    have h1 : i + ((2 * (d + 1) : ℕ) : ZMod k) = (i + ((2 * d : ℕ) : ZMod k)) + 2 := by
      push_cast; ring
    have h2 : i - ((2 * (d + 1) : ℕ) : ZMod k) + 2 = i - ((2 * d : ℕ) : ZMod k) := by
      push_cast; ring
    constructor
    · rw [h1, period_two_step hA, (ih i).1]
    · rw [← period_two_step hA (i - ((2 * (d + 1) : ℕ) : ZMod k)), h2, (ih i).2]

private lemma MOp_two_fix_kerA {k : ℕ} (d : ℕ) {a : ZMod k → K} (hA : AOp a = 0) :
    MOp (2 * d) a = a := by
  funext i
  simp only [MOp]
  rw [(period_two_mul hA d i).1, (period_two_mul hA d i).2]
  generalize a i = x
  fin_cases x <;> rfl

private lemma card_ker_prod_eq {k : ℕ} [NeZero k] (d : ℕ) :
    ((Finset.univ : Finset (ZMod k → K)).filter (fun x => MOp (2 * d) (AOp x) = 0)).card =
      ((Finset.univ : Finset (ZMod k → K)).filter (fun a => AOp a = 0)).card *
      ((Finset.univ : Finset (ZMod k → K)).filter (fun b => MOp (2 * d) b = 0)).card := by
  rw [← Finset.card_product]
  refine Finset.card_bij (fun x _ => (MOp (2 * d) x, x + MOp (2 * d) x)) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hx ⊢
    have hA : AOp (MOp (2 * d) x) = 0 := by rw [← MOp_AOp_comm, hx]
    refine ⟨hA, ?_⟩
    funext i
    rw [MOp_add, MOp_two_fix_kerA d hA, zmod2_add_self]
    rfl
  · intro x1 _ x2 _ h
    have h1 : MOp (2 * d) x1 = MOp (2 * d) x2 := congrArg Prod.fst h
    have h2 : x1 + MOp (2 * d) x1 = x2 + MOp (2 * d) x2 := congrArg Prod.snd h
    funext i
    have h1i := congrFun h1 i
    have h2i := congrFun h2 i
    simp only [Pi.add_apply] at h2i
    rw [h1i] at h2i
    have h3 := congrArg (· + MOp (2 * d) x2 i) h2i
    simpa [add_assoc, zmod2_add_self] using h3
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hab
    obtain ⟨hAa, hMb⟩ := hab
    refine ⟨a + b, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      funext i
      rw [show AOp (a + b) = AOp a + AOp b from by funext j; exact AOp_add a b j,
        MOp_add, hAa, MOp_AOp_comm, hMb]
      simp [MOp, AOp]
    · have hMab : MOp (2 * d) (a + b) = a := by
        funext i
        rw [MOp_add, MOp_two_fix_kerA d hAa, hMb]
        simp
      ext i
      · exact congrFun hMab i
      · simp only [Pi.add_apply, hMab]
        rw [add_comm (a i) (b i), add_assoc, zmod2_add_self, add_zero]

private lemma card_ker_AOp {k : ℕ} [NeZero k] :
    ((Finset.univ : Finset (ZMod k → K)).filter (fun a => AOp a = 0)).card = 2 ^ Nat.gcd k 2 := by
  by_cases heven : 2 ∣ k
  · have hgcd : Nat.gcd k 2 = 2 := Nat.gcd_eq_right heven
    rw [hgcd]
    have hcard : (Fintype.card (K × K)) = 2 ^ 2 := by decide
    rw [← hcard, ← Finset.card_univ]
    refine Finset.card_bij (fun a _ => (a 0, a 1)) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro a1 ha1 a2 ha2 h
      have hA1 : AOp a1 = 0 := (Finset.mem_filter.mp ha1).2
      have hA2 : AOp a2 = 0 := (Finset.mem_filter.mp ha2).2
      have h0 : a1 0 = a2 0 := congrArg Prod.fst h
      have h1 : a1 1 = a2 1 := congrArg Prod.snd h
      funext i
      have hnat : ∀ n : ℕ, a1 (n : ZMod k) = a2 (n : ZMod k) := by
        intro n
        have h2 := period_two_mul hA1 (n / 2) ((n % 2 : ℕ) : ZMod k)
        have h2' := period_two_mul hA2 (n / 2) ((n % 2 : ℕ) : ZMod k)
        have heq : ((n % 2 : ℕ) : ZMod k) + ((2 * (n / 2) : ℕ) : ZMod k) = (n : ZMod k) := by
          rw [← Nat.cast_add]
          congr 1
          omega
        rw [← heq, h2.1, h2'.1]
        have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
        rcases hmod with hm | hm <;> simp [hm, h0, h1]
      simpa [ZMod.natCast_zmod_val] using hnat i.val
    · rintro ⟨c0, c1⟩ _
      let a : ZMod k → K := fun i => if i.val % 2 = 0 then c0 else c1
      have hk2 : 2 ≤ k := Nat.le_of_dvd (NeZero.pos k) heven
      have hv1 : (1 : ZMod k).val = 1 := by
        simpa using ZMod.val_natCast_of_lt (by omega : 1 < k)
      refine ⟨a, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        funext i
        simp only [AOp, a, Pi.zero_apply]
        have h1 : (i + 1).val % 2 = (i.val + 1) % 2 := by
          rw [ZMod.val_add, hv1]
          obtain ⟨m, rfl⟩ := heven
          rw [Nat.mod_mod_of_dvd _ (dvd_mul_right 2 m)]
        have h2 : (i - 1).val % 2 = (i.val + 1) % 2 := by
          have : (i - 1) + 1 = i := sub_add_cancel i 1
          have hsub : (i - 1 + 1).val % 2 = ((i - 1).val + 1) % 2 := by
            rw [ZMod.val_add, hv1]
            obtain ⟨m, rfl⟩ := heven
            rw [Nat.mod_mod_of_dvd _ (dvd_mul_right 2 m)]
          rw [this] at hsub
          omega
        rw [h1, h2]
        split_ifs <;> exact zmod2_add_self _
      · simp [a, hv1]
  · have hgcd : Nat.gcd k 2 = 1 := by
      have hdv := Nat.gcd_dvd_right k 2
      have hle : Nat.gcd k 2 ≤ 2 := Nat.le_of_dvd (by omega) hdv
      have hpos : 0 < Nat.gcd k 2 := Nat.gcd_pos_of_pos_right k (by omega)
      have hne2 : Nat.gcd k 2 ≠ 2 := fun h => heven (h ▸ Nat.gcd_dvd_left k 2)
      omega
    rw [hgcd]
    have hcard : (Fintype.card K) = 2 ^ 1 := by decide
    rw [← hcard, ← Finset.card_univ]
    refine Finset.card_bij (fun a _ => a 0) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro a1 ha1 a2 ha2 h0
      have hA1 : AOp a1 = 0 := (Finset.mem_filter.mp ha1).2
      have hA2 : AOp a2 = 0 := (Finset.mem_filter.mp ha2).2
      have hk_odd : k % 2 = 1 := by omega
      have hstep1 : ∀ (a : ZMod k → K), AOp a = 0 → ∀ i : ZMod k, a (i + 1) = a i := by
        intro a hA i
        have := (period_two_mul hA ((k + 1) / 2) i).1
        have heq : ((2 * ((k + 1) / 2) : ℕ) : ZMod k) = 1 := by
          have h1 : 2 * ((k + 1) / 2) = k + 1 := by omega
          rw [h1]
          simp
        rw [heq] at this
        exact this
      have hconst : ∀ (a : ZMod k → K), AOp a = 0 → ∀ i : ZMod k, a i = a 0 := by
        intro a hA i
        have hnat : ∀ n : ℕ, a (n : ZMod k) = a 0 := by
          intro n
          induction n with
          | zero => simp
          | succ n ih =>
            rw [Nat.cast_succ, hstep1 a hA, ih]
        simpa [ZMod.natCast_zmod_val] using hnat i.val
      funext i
      rw [hconst a1 hA1 i, hconst a2 hA2 i, h0]
    · intro c _
      refine ⟨fun _ => c, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      funext i
      exact zmod2_add_self c

private lemma exists_mul_mod_eq_one {a m : ℕ} (hcop : Nat.Coprime a m) (hm : 1 < m) :
    ∃ u : ℕ, (a * u) % m = 1 := by
  haveI : NeZero m := ⟨by omega⟩
  refine ⟨((ZMod.unitOfCoprime a hcop)⁻¹ : (ZMod m)ˣ).val.val, ?_⟩
  have h : (a : ZMod m) * (((ZMod.unitOfCoprime a hcop)⁻¹ : (ZMod m)ˣ).val.val : ZMod m) = 1 := by
    rw [ZMod.natCast_zmod_val, ← ZMod.coe_unitOfCoprime a hcop]
    exact_mod_cast Units.mul_inv (ZMod.unitOfCoprime a hcop)
  have hval := congrArg ZMod.val h
  rw [← Nat.cast_mul, ZMod.val_natCast] at hval
  have hv1 : (1 : ZMod m).val = 1 := by
    simpa using ZMod.val_natCast_of_lt hm
  omega

private lemma card_ker_MOp {k : ℕ} [NeZero k] (d : ℕ) :
    let s := Nat.gcd k d
    ((Finset.univ : Finset (ZMod k → K)).filter (fun b => MOp d b = 0)).card =
      2 ^ (if 3 ∣ k / s then 2 * s else 0) := by
  intro s
  have hs_pos : 0 < s := Nat.gcd_pos_of_pos_left d (NeZero.pos k)
  have hs_dvd_k : s ∣ k := Nat.gcd_dvd_left k d
  have hs_dvd_d : s ∣ d := Nat.gcd_dvd_right k d
  set m := k / s
  have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd (NeZero.pos k) hs_dvd_k) hs_pos
  have hsm : s * m = k := Nat.mul_div_cancel' hs_dvd_k
  have hcop : Nat.Coprime m (d / s) := by
    have := Nat.coprime_div_gcd_div_gcd hs_pos
    simpa [s, m] using this
  have hstep3 : ∀ (b : ZMod k → K), MOp d b = 0 → ∀ i : ZMod k,
      b (i + ((3 * d : ℕ) : ZMod k)) = b i := by
    intro b hMb i
    have h1 := congrFun hMb (i + (d : ZMod k))
    have h2 := congrFun hMb (i + ((2 * d : ℕ) : ZMod k))
    simp only [MOp, Pi.zero_apply] at h1 h2
    have ha : i + (d : ZMod k) + (d : ZMod k) = i + ((2 * d : ℕ) : ZMod k) := by push_cast; ring
    have hb : i + (d : ZMod k) - (d : ZMod k) = i := by ring
    have hc : i + ((2 * d : ℕ) : ZMod k) + (d : ZMod k) = i + ((3 * d : ℕ) : ZMod k) := by push_cast; ring
    have hd : i + ((2 * d : ℕ) : ZMod k) - (d : ZMod k) = i + (d : ZMod k) := by push_cast; ring
    rw [ha, hb] at h1
    rw [hc, hd] at h2
    have hsum := congrArg₂ (· + ·) h1 h2
    simp only [add_zero] at hsum
    generalize b i = x0 at hsum ⊢
    generalize b (i + (d : ZMod k)) = x1 at hsum
    generalize b (i + ((2 * d : ℕ) : ZMod k)) = x2 at hsum
    generalize b (i + ((3 * d : ℕ) : ZMod k)) = x3 at hsum ⊢
    have hr : x1 + x2 + x0 + (x2 + x3 + x1) = x3 + x0 + (x1 + x1) + (x2 + x2) := by ring
    rw [hr, zmod2_add_self, zmod2_add_self, add_zero, add_zero] at hsum
    exact zmod2_add_eq_zero hsum
  have hstep_3t : ∀ (b : ZMod k → K), MOp d b = 0 → ∀ (t : ℕ) (i : ZMod k),
      b (i + ((3 * t * d : ℕ) : ZMod k)) = b i := by
    intro b hMb t
    induction t with
    | zero => intro i; simp
    | succ t ih =>
      intro i
      have h1 : i + ((3 * (t + 1) * d : ℕ) : ZMod k) =
          (i + ((3 * t * d : ℕ) : ZMod k)) + ((3 * d : ℕ) : ZMod k) := by push_cast; ring
      rw [h1, hstep3 b hMb, ih]
  have hrec : ∀ (b : ZMod k → K), MOp d b = 0 → ∀ (t : ℕ) (i : ZMod k),
      b (i + (((t + 2) * d : ℕ) : ZMod k)) =
        b (i + ((t * d : ℕ) : ZMod k)) + b (i + (((t + 1) * d : ℕ) : ZMod k)) := by
    intro b hMb t i
    have h1 := congrFun hMb (i + (((t + 1) * d : ℕ) : ZMod k))
    simp only [MOp, Pi.zero_apply] at h1
    have ha : i + (((t + 1) * d : ℕ) : ZMod k) + (d : ZMod k) = i + (((t + 2) * d : ℕ) : ZMod k) := by
      push_cast; ring
    have hb : i + (((t + 1) * d : ℕ) : ZMod k) - (d : ZMod k) = i + ((t * d : ℕ) : ZMod k) := by
      push_cast; ring
    rw [ha, hb] at h1
    generalize b (i + ((t * d : ℕ) : ZMod k)) = x0 at h1 ⊢
    generalize b (i + (((t + 1) * d : ℕ) : ZMod k)) = x1 at h1 ⊢
    generalize b (i + (((t + 2) * d : ℕ) : ZMod k)) = x2 at h1 ⊢
    have hr : x1 + x2 + x0 = x2 + (x0 + x1) := by ring
    rw [hr] at h1
    exact zmod2_add_eq_zero h1
  have hcoset : ∀ i : ZMod k, ∃ (r : Fin s) (t : ℕ), i = (r.val : ZMod k) + ((t * d : ℕ) : ZMod k) := by
    intro i
    let r : Fin s := ⟨i.val % s, Nat.mod_lt _ hs_pos⟩
    have hq_eq : i.val = r.val + s * (i.val / s) := by
      dsimp only [r]
      have := Nat.div_add_mod i.val s
      omega
    by_cases hm1 : m = 1
    · refine ⟨r, 0, ?_⟩
      have hk_eq : k = s := by rw [← hsm, hm1, mul_one]
      have hdiv0 : i.val / s = 0 := Nat.div_eq_of_lt (by rw [← hk_eq]; exact i.val_lt)
      have : i.val = r.val := by rw [hdiv0, mul_zero, add_zero] at hq_eq; exact hq_eq
      simp [← this, ZMod.natCast_zmod_val]
    · have hm_gt1 : 1 < m := by omega
      obtain ⟨u, hu⟩ := exists_mul_mod_eq_one hcop.symm hm_gt1
      set q := i.val / s
      refine ⟨r, q * u, ?_⟩
      have hmul : (q * u * (d / s)) % m = q % m := by
        calc (q * u * (d / s)) % m
            = (q * ((d / s) * u)) % m := by ring_nf
          _ = ((q % m) * (((d / s) * u) % m)) % m := Nat.mul_mod _ _ _
          _ = ((q % m) * 1) % m := by rw [hu]
          _ = q % m := by simp
      have hmodk : (r.val + (q * u) * d) % k = i.val := by
        have hd_eq : d = s * (d / s) := (Nat.mul_div_cancel' hs_dvd_d).symm
        have h1 : (q * u) * d = s * (q * u * (d / s)) := by
          conv_lhs => rw [hd_eq]
          ring
        rw [h1]
        have h2 : (r.val + s * (q * u * (d / s))) % (s * m) =
            r.val + s * ((q * u * (d / s)) % m) := by
          have hr_lt : r.val < s := r.isLt
          have hrem_lt : r.val + s * ((q * u * (d / s)) % m) < s * m := by
            have := Nat.mod_lt (q * u * (d / s)) hm_pos
            nlinarith
          have hdvd : (s * m) ∣ (s * (q * u * (d / s)) - s * ((q * u * (d / s)) % m)) := by
            have : q * u * (d / s) - (q * u * (d / s)) % m = m * ((q * u * (d / s)) / m) := by
              have := Nat.div_add_mod (q * u * (d / s)) m
              omega
            rw [← Nat.mul_sub_left_distrib, this]
            exact ⟨(q * u * (d / s)) / m, by ring⟩
          have hle : s * ((q * u * (d / s)) % m) ≤ s * (q * u * (d / s)) :=
            Nat.mul_le_mul_left s (Nat.mod_le _ _)
          obtain ⟨c, hc⟩ := hdvd
          have htot : r.val + s * (q * u * (d / s)) = (r.val + s * ((q * u * (d / s)) % m)) + (s * m) * c := by
            omega
          rw [htot, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrem_lt]
        have hmod_eq : (r.val + s * (q * u * (d / s))) % k = (r.val + s * (q * u * (d / s))) % (s * m) := by
          rw [hsm]
        rw [hmod_eq, h2, hmul]
        have hq_lt : q < m :=
          Nat.div_lt_of_lt_mul (by rw [hsm]; exact i.val_lt)
        rw [Nat.mod_eq_of_lt hq_lt]
        omega
      have hcast : ((r.val + q * u * d : ℕ) : ZMod k) = (i.val : ZMod k) := by
        rw [← ZMod.natCast_mod (r.val + q * u * d) k, hmodk]
      simpa [ZMod.natCast_zmod_val, Nat.cast_add, Nat.cast_mul] using hcast.symm
  split_ifs with h3m
  · have hcard : Fintype.card (Fin s → K × K) = 2 ^ (2 * s) := by
      simp [Fintype.card_fin]
      rw [show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_mul]
    rw [← hcard, ← Finset.card_univ]
    refine Finset.card_bij (fun b _ => fun r : Fin s => (b (r.val : ZMod k), b ((r.val : ZMod k) + (d : ZMod k)))) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro b1 hb1 b2 hb2 h
      have hM1 : MOp d b1 = 0 := (Finset.mem_filter.mp hb1).2
      have hM2 : MOp d b2 = 0 := (Finset.mem_filter.mp hb2).2
      funext i
      obtain ⟨r, t, rfl⟩ := hcoset i
      have hr0 : b1 (r.val : ZMod k) = b2 (r.val : ZMod k) := congrArg Prod.fst (congrFun h r)
      have hr1 : b1 ((r.val : ZMod k) + (d : ZMod k)) = b2 ((r.val : ZMod k) + (d : ZMod k)) :=
        congrArg Prod.snd (congrFun h r)
      have hstep : ∀ t0 : ℕ, b1 ((r.val : ZMod k) + ((t0 * d : ℕ) : ZMod k)) =
          b2 ((r.val : ZMod k) + ((t0 * d : ℕ) : ZMod k)) := by
        intro t0
        have hq : t0 = 3 * (t0 / 3) + t0 % 3 := (Nat.div_add_mod t0 3).symm
        have heq : (r.val : ZMod k) + ((t0 * d : ℕ) : ZMod k) =
            ((r.val : ZMod k) + (((t0 % 3) * d : ℕ) : ZMod k)) + ((3 * (t0 / 3) * d : ℕ) : ZMod k) := by
          conv_lhs => rw [hq]
          push_cast; ring
        rw [heq, hstep_3t b1 hM1, hstep_3t b2 hM2]
        have hmod : t0 % 3 = 0 ∨ t0 % 3 = 1 ∨ t0 % 3 = 2 := by omega
        rcases hmod with hm0 | hm1 | hm2
        · simp [hm0, hr0]
        · simp [hm1, hr1]
        · rw [hm2]
          have h1 := hrec b1 hM1 0 (r.val : ZMod k)
          have h2 := hrec b2 hM2 0 (r.val : ZMod k)
          simp only [Nat.zero_add, Nat.zero_mul, Nat.cast_zero, add_zero, one_mul] at h1 h2
          rw [h1, h2, hr0, hr1]
      exact hstep t
    · intro f _
      obtain ⟨m3, hm3⟩ := h3m
      have h3s_dvd_k : 3 * s ∣ k := ⟨m3, by rw [← hsm, hm3]; ring⟩
      have hcop3 : Nat.Coprime 3 (d / s) := by
        have : 3 ∣ m := ⟨m3, hm3⟩
        exact hcop.coprime_dvd_left this
      obtain ⟨invD, hinvD⟩ := exists_mul_mod_eq_one hcop3.symm (by omega : 1 < 3)
      let tMod3 : ZMod k → ℕ := fun i => ((i.val / s) * invD) % 3
      let b : ZMod k → K := fun i =>
        let r : Fin s := ⟨i.val % s, Nat.mod_lt _ hs_pos⟩
        let t := tMod3 i
        if t = 0 then (f r).1 else if t = 1 then (f r).2 else (f r).1 + (f r).2
      have hshift : ∀ i : ZMod k,
          (i + (d : ZMod k)).val % s = i.val % s ∧
          tMod3 (i + (d : ZMod k)) = (tMod3 i + 1) % 3 := by
        intro i
        have hval : (i + (d : ZMod k)).val = (i.val + d) % k := by
          rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod]
        have hmod3s : (i.val + d) % k % (3 * s) = (i.val + d) % (3 * s) :=
          Nat.mod_mod_of_dvd _ h3s_dvd_k
        have hd_eq : d = s * (d / s) := (Nat.mul_div_cancel' hs_dvd_d).symm
        have hmods : (i + (d : ZMod k)).val % s = i.val % s := by
          rw [hval, Nat.mod_mod_of_dvd _ hs_dvd_k, hd_eq, Nat.add_mul_mod_self_left]
        refine ⟨hmods, ?_⟩
        have hdiv3 : ((i + (d : ZMod k)).val / s) % 3 = (i.val / s + d / s) % 3 := by
          have h1 : (i + (d : ZMod k)).val / s % 3 = ((i + (d : ZMod k)).val % (3 * s)) / s := by
            rw [Nat.mod_mul_left_div_self]
          have h2 : (i.val + d) % (3 * s) / s = (i.val + d) / s % 3 := by
            rw [Nat.mod_mul_left_div_self]
          rw [h1, hval, hmod3s, h2]
          conv_lhs => rw [hd_eq]
          rw [Nat.add_mul_div_left _ _ hs_pos]
        simp only [tMod3]
        calc (((i + (d : ZMod k)).val / s) * invD) % 3
            = ((((i + (d : ZMod k)).val / s) % 3) * (invD % 3)) % 3 := Nat.mul_mod _ _ _
          _ = (((i.val / s + d / s) % 3) * (invD % 3)) % 3 := by rw [hdiv3]
          _ = ((i.val / s + d / s) * invD) % 3 := (Nat.mul_mod _ _ _).symm
          _ = ((i.val / s) * invD + (d / s) * invD) % 3 := by ring_nf
          _ = (((i.val / s) * invD) % 3 + ((d / s) * invD) % 3) % 3 := Nat.add_mod _ _ _
          _ = (((i.val / s) * invD) % 3 + 1) % 3 := by rw [hinvD]
      have hMb : MOp d b = 0 := by
        funext i
        have h1 := hshift (i - (d : ZMod k))
        have h2 := hshift i
        rw [sub_add_cancel] at h1
        simp only [MOp, Pi.zero_apply]
        have hr1 : (i - (d : ZMod k)).val % s = i.val % s := h1.1.symm
        have hr2 : (i + (d : ZMod k)).val % s = i.val % s := h2.1
        set r0 : Fin s := ⟨i.val % s, Nat.mod_lt _ hs_pos⟩
        have hb0 : b i = (if tMod3 i = 0 then (f r0).1 else if tMod3 i = 1 then (f r0).2 else (f r0).1 + (f r0).2) := rfl
        have hb1 : b (i + (d : ZMod k)) =
            (if tMod3 (i + (d : ZMod k)) = 0 then (f r0).1 else if tMod3 (i + (d : ZMod k)) = 1 then (f r0).2 else (f r0).1 + (f r0).2) := by
          simp only [b]
          have : (⟨(i + (d : ZMod k)).val % s, Nat.mod_lt _ hs_pos⟩ : Fin s) = r0 := Fin.ext hr2
          rw [this]
        have hb2 : b (i - (d : ZMod k)) =
            (if tMod3 (i - (d : ZMod k)) = 0 then (f r0).1 else if tMod3 (i - (d : ZMod k)) = 1 then (f r0).2 else (f r0).1 + (f r0).2) := by
          simp only [b]
          have : (⟨(i - (d : ZMod k)).val % s, Nat.mod_lt _ hs_pos⟩ : Fin s) = r0 := Fin.ext hr1
          rw [this]
        rw [hb0, hb1, hb2, h2.2]
        have ht_lt : tMod3 (i - (d : ZMod k)) < 3 := Nat.mod_lt _ (by omega)
        have ht_eq : tMod3 i = (tMod3 (i - (d : ZMod k)) + 1) % 3 := h1.2
        rw [ht_eq]
        generalize tMod3 (i - (d : ZMod k)) = t at ht_lt ⊢
        generalize (f r0).1 = u
        generalize (f r0).2 = v
        have hcases : t = 0 ∨ t = 1 ∨ t = 2 := by omega
        rcases hcases with rfl | rfl | rfl <;> fin_cases u <;> fin_cases v <;> rfl
      refine ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMb⟩, ?_⟩
      funext r
      have hr_lt_k : r.val < k := lt_of_lt_of_le r.isLt (Nat.le_of_dvd (NeZero.pos k) hs_dvd_k)
      have hvr : (r.val : ZMod k).val = r.val := ZMod.val_natCast_of_lt hr_lt_k
      have hrmod : (r.val : ZMod k).val % s = r.val := by rw [hvr, Nat.mod_eq_of_lt r.isLt]
      have hrdiv : (r.val : ZMod k).val / s = 0 := by rw [hvr, Nat.div_eq_of_lt r.isLt]
      have ht0 : tMod3 (r.val : ZMod k) = 0 := by simp only [tMod3, hrdiv, zero_mul, Nat.zero_mod]
      have hsh := hshift (r.val : ZMod k)
      ext
      · simp only [b, ht0, ↓reduceIte]
        have : (⟨(r.val : ZMod k).val % s, Nat.mod_lt _ hs_pos⟩ : Fin s) = r := Fin.ext hrmod
        rw [this]
      · simp only [b, hsh.2, ht0]
        have hrmod2 : ((r.val : ZMod k) + (d : ZMod k)).val % s = r.val := by rw [hsh.1, hrmod]
        have : (⟨((r.val : ZMod k) + (d : ZMod k)).val % s, Nat.mod_lt _ hs_pos⟩ : Fin s) = r :=
          Fin.ext hrmod2
        rw [this]
        simp
  · simp only [pow_zero]
    have huniq : (Finset.univ : Finset (ZMod k → K)).filter (fun b => MOp d b = 0) = {0} := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hMb
        have hcop_m3 : Nat.Coprime m 3 := by
          have : Nat.gcd m 3 ∣ 3 := Nat.gcd_dvd_right m 3
          have hpos : 0 < Nat.gcd m 3 := Nat.gcd_pos_of_pos_right m (by omega)
          have hle : Nat.gcd m 3 ≤ 3 := Nat.le_of_dvd (by omega) this
          have hne3 : Nat.gcd m 3 ≠ 3 := fun h => h3m (h ▸ Nat.gcd_dvd_left m 3)
          have hne2 : Nat.gcd m 3 ≠ 2 := fun h => by rw [h] at this; omega
          exact Nat.coprime_iff_gcd_eq_one.mpr (by omega)
        have hstep1 : ∀ i : ZMod k, b (i + (d : ZMod k)) = b i := by
          intro i
          have h3_cop : Nat.Coprime 3 m := hcop_m3.symm
          by_cases hm1 : m = 1
          · have hk_eq : k = s := by rw [← hsm, hm1, mul_one]
            have hd0 : (d : ZMod k) = 0 := by
              rw [ZMod.natCast_eq_zero_iff, hk_eq]
              exact hs_dvd_d
            simp [hd0]
          · obtain ⟨v, hv⟩ := exists_mul_mod_eq_one h3_cop (by omega : 1 < m)
            have h3v_eq : ((3 * v * d : ℕ) : ZMod k) = (d : ZMod k) := by
              have hdiv : 3 * v = m * ((3 * v) / m) + 1 := by
                have := Nat.div_add_mod (3 * v) m
                omega
              have hmul : 3 * v * d = k * ((3 * v) / m * (d / s)) + d := by
                have hd_eq : d = s * (d / s) := (Nat.mul_div_cancel' hs_dvd_d).symm
                calc 3 * v * d = (m * ((3 * v) / m) + 1) * d := by conv_lhs => rw [hdiv]
                  _ = m * ((3 * v) / m) * d + d := by ring
                  _ = m * ((3 * v) / m) * (s * (d / s)) + d := by congr 1; rw [← hd_eq]
                  _ = (s * m) * ((3 * v) / m * (d / s)) + d := by ring
                  _ = k * ((3 * v) / m * (d / s)) + d := by rw [hsm]
              rw [hmul]
              simp
            have := hstep_3t b hMb v i
            rwa [h3v_eq] at this
        funext i
        have h0 := congrFun hMb i
        simp only [MOp, Pi.zero_apply] at h0
        have hprev : b (i - (d : ZMod k)) = b i := by
          have := hstep1 (i - (d : ZMod k))
          rw [sub_add_cancel] at this
          exact this.symm
        rw [hstep1 i, hprev] at h0
        rw [zmod2_add_self, zero_add] at h0
        exact h0
      · rintro rfl
        funext i
        simp [MOp]
    rw [huniq, Finset.card_singleton]

private lemma phase_polar {k : ℕ} [NeZero k] (spacing : ℕ) (start inject : ZMod k)
    (name c : ZMod k → K) (u v : ZMod k → K) :
    let phase := fun x : ZMod k → K =>
      let z := fun i : ZMod k => x (i - start) + name i
      let y := fun i : ZMod k => z i + z (i + (spacing : ZMod k)) + z (i - (spacing : ZMod k))
      ∑ i : ZMod k, (y i + (1 + y (i + 1)) * y (i + 2) + x (i - inject) + c i)
    phase (u + v) + phase u + phase v + phase 0 =
      ∑ i : ZMod k, u (i - start) * MOp (2 * spacing) (AOp (fun j => v (j - start))) i := by
  intro phase
  let u' : ZMod k → K := fun i => u (i - start)
  let v' : ZMod k → K := fun i => v (i - start)
  let M : (ZMod k → K) → (ZMod k → K) := MOp spacing
  have hterm : ∀ i : ZMod k,
      (let zuv := fun j => (u + v) (j - start) + name j
       let yuv := M zuv
       let zu := fun j => u (j - start) + name j
       let yu := M zu
       let zv := fun j => v (j - start) + name j
       let yv := M zv
       let z0 := fun j => (0 : ZMod k → K) (j - start) + name j
       let y0 := M z0
       (yuv i + (1 + yuv (i + 1)) * yuv (i + 2) + (u + v) (i - inject) + c i) +
       (yu i + (1 + yu (i + 1)) * yu (i + 2) + u (i - inject) + c i) +
       (yv i + (1 + yv (i + 1)) * yv (i + 2) + v (i - inject) + c i) +
       (y0 i + (1 + y0 (i + 1)) * y0 (i + 2) + (0 : ZMod k → K) (i - inject) + c i)) =
      M u' (i + 1) * M v' (i + 2) + M v' (i + 1) * M u' (i + 2) := by
    intro i
    dsimp only
    have hyuv : ∀ j, M (fun t => (u + v) (t - start) + name t) j = M u' j + M v' j + M name j := by
      intro j; simp only [M, MOp, u', v', Pi.add_apply]; ring
    have hyu : ∀ j, M (fun t => u (t - start) + name t) j = M u' j + M name j := by
      intro j; simp only [M, MOp, u', Pi.add_apply]; ring
    have hyv : ∀ j, M (fun t => v (t - start) + name t) j = M v' j + M name j := by
      intro j; simp only [M, MOp, v', Pi.add_apply]; ring
    have hy0 : ∀ j, M (fun t => (0 : ZMod k → K) (t - start) + name t) j = M name j := by
      intro j; simp only [M, MOp, Pi.zero_apply, zero_add]
    rw [hyuv i, hyuv (i + 1), hyuv (i + 2), hyu i, hyu (i + 1), hyu (i + 2),
      hyv i, hyv (i + 1), hyv (i + 2), hy0 i, hy0 (i + 1), hy0 (i + 2)]
    simp only [Pi.add_apply, Pi.zero_apply, add_zero]
    have h2 : ∀ x : K, x + x = 0 := zmod2_add_self
    generalize M u' i = a0
    generalize M v' i = b0
    generalize M name i = n0
    generalize M u' (i + 1) = a1
    generalize M v' (i + 1) = b1
    generalize M name (i + 1) = n1
    generalize M u' (i + 2) = a2
    generalize M v' (i + 2) = b2
    generalize M name (i + 2) = n2
    generalize u (i - inject) = ui
    generalize v (i - inject) = vi
    generalize c i = ci
    have hr :
        (a0 + b0 + n0 + (1 + (a1 + b1 + n1)) * (a2 + b2 + n2) + (ui + vi) + ci) +
        (a0 + n0 + (1 + (a1 + n1)) * (a2 + n2) + ui + ci) +
        (b0 + n0 + (1 + (b1 + n1)) * (b2 + n2) + vi + ci) +
        (n0 + (1 + n1) * n2 + ci) =
        (a1 * b2 + b1 * a2) +
        (a0 + a0) + (b0 + b0) + (n0 + n0) + (n0 + n0) +
        (a2 + a2) + (b2 + b2) + (n2 + n2) + (n2 + n2) +
        (a1 * a2 + a1 * a2) + (b1 * b2 + b1 * b2) +
        (a1 * n2 + a1 * n2) + (b1 * n2 + b1 * n2) +
        (n1 * a2 + n1 * a2) + (n1 * b2 + n1 * b2) +
        (n1 * n2 + n1 * n2) + (n1 * n2 + n1 * n2) +
        (ui + ui) + (vi + vi) + (ci + ci) + (ci + ci) := by ring
    rw [hr]
    simp only [h2, add_zero]
  have hsum : phase (u + v) + phase u + phase v + phase 0 =
      ∑ i : ZMod k, (M u' (i + 1) * M v' (i + 2) + M v' (i + 1) * M u' (i + 2)) := by
    simp only [phase, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hterm i
  rw [hsum, Finset.sum_add_distrib]
  have h1 : ∑ i : ZMod k, M u' (i + 1) * M v' (i + 2) =
      ∑ i : ZMod k, M u' i * M v' (i + 1) := by
    refine Fintype.sum_equiv (Equiv.addRight (1 : ZMod k)) _ _ fun i => ?_
    change M u' (i + 1) * M v' (i + 2) = M u' (i + 1) * M v' ((i + 1) + 1)
    congr 2; ring
  have h2 : ∑ i : ZMod k, M v' (i + 1) * M u' (i + 2) =
      ∑ i : ZMod k, M u' i * M v' (i - 1) := by
    refine Fintype.sum_equiv (Equiv.addRight (2 : ZMod k)) _ _ fun i => ?_
    change M v' (i + 1) * M u' (i + 2) = M u' (i + 2) * M v' ((i + 2) - 1)
    rw [mul_comm]
    congr 2; ring
  rw [h1, h2, ← Finset.sum_add_distrib]
  have h3 : ∑ i : ZMod k, (M u' i * M v' (i + 1) + M u' i * M v' (i - 1)) =
      ∑ i : ZMod k, MOp spacing u' i * AOp (MOp spacing v') i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [M, AOp, mul_add]
  rw [h3, MOp_self_adjoint, ← MOp_AOp_comm, MOp_comp_MOp]

private lemma rad_card_eq {k : ℕ} [NeZero k] (spacing : ℕ) (start inject : ZMod k)
    (name c : ZMod k → K) :
    let phase := fun x : ZMod k → K =>
      let z := fun i : ZMod k => x (i - start) + name i
      let y := fun i : ZMod k => z i + z (i + (spacing : ZMod k)) + z (i - (spacing : ZMod k))
      ∑ i : ZMod k, (y i + (1 + y (i + 1)) * y (i + 2) + x (i - inject) + c i)
    let rad := (Finset.univ : Finset (ZMod k → K)).filter (fun v =>
      ∀ u : ZMod k → K, phase (u + v) + phase u + phase v + phase 0 = 0)
    let s := Nat.gcd k (2 * spacing)
    rad.card = 2 ^ (Nat.gcd k 2 + (if 3 ∣ k / s then 2 * s else 0)) := by
  intro phase rad s
  have hmem : ∀ v : ZMod k → K, v ∈ rad ↔ MOp (2 * spacing) (AOp (fun j => v (j - start))) = 0 := by
    intro v
    simp only [rad, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      funext i0
      have hi := h (Pi.single (i0 - start) 1)
      rw [phase_polar] at hi
      have hsum : ∑ i : ZMod k, (Pi.single (i0 - start) (1 : K) : ZMod k → K) (i - start) *
          MOp (2 * spacing) (AOp (fun j => v (j - start))) i =
          MOp (2 * spacing) (AOp (fun j => v (j - start))) i0 := by
        rw [Finset.sum_eq_single i0]
        · simp
        · intro i _ hne
          have hne' : i - start ≠ i0 - start := fun h => hne (sub_left_inj.mp h)
          simp [Pi.single_apply, hne']
        · intro h0; exact absurd (Finset.mem_univ i0) h0
      rw [hsum] at hi
      exact hi
    · intro h u
      rw [phase_polar, h]
      simp
  have hbij : rad.card =
      ((Finset.univ : Finset (ZMod k → K)).filter (fun w => MOp (2 * spacing) (AOp w) = 0)).card := by
    refine Finset.card_bij (fun v _ => fun j => v (j - start)) ?_ ?_ ?_
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hmem v).mp hv
    · intro v1 _ v2 _ h
      funext j
      have := congrFun h (j + start)
      simpa using this
    · intro w hw
      refine ⟨fun j => w (j + start), ?_, ?_⟩
      · rw [hmem]
        have heq : (fun j => w (j - start + start)) = w := by funext j; simp
        rw [heq]
        exact (Finset.mem_filter.mp hw).2
      · funext j; simp
  rw [hbij, card_ker_prod_eq, card_ker_AOp, card_ker_MOp, ← pow_add]

private lemma p_eq_zero_iff {k : ℕ} [NeZero k] (spacing : ℕ) :
    let s := Nat.gcd k (2 * spacing)
    let loss := Nat.gcd k 2 + (if 3 ∣ k / s then 2 * s else 0)
    let p := (k - loss) / 2
    loss ≤ k →
    (p = 0 ↔ k ≤ 2 ∨ ((k = 3 ∨ k = 6) ∧ ¬ 3 ∣ spacing)) := by
  intro s loss p hle
  have hkpos : 0 < k := NeZero.pos k
  have hs_pos : 0 < s := Nat.gcd_pos_of_pos_left (2 * spacing) hkpos
  have hs_dvd_k : s ∣ k := Nat.gcd_dvd_left k (2 * spacing)
  have hparity : (k - loss) % 2 = 0 := by
    have hgcd2 : (Nat.gcd k 2) % 2 = k % 2 := by
      by_cases h2 : 2 ∣ k
      · rw [Nat.gcd_eq_right h2]; omega
      · have h1 : Nat.gcd k 2 = 1 := by
          have hdv := Nat.gcd_dvd_right k 2
          have hle2 : Nat.gcd k 2 ≤ 2 := Nat.le_of_dvd (by omega) hdv
          have hpos2 : 0 < Nat.gcd k 2 := Nat.gcd_pos_of_pos_right k (by omega)
          have hne2 : Nat.gcd k 2 ≠ 2 := fun h => h2 (h ▸ Nat.gcd_dvd_left k 2)
          omega
        rw [h1]; omega
    simp only [loss]
    split_ifs <;> omega
  have hp0 : p = 0 ↔ k = loss := by
    simp only [p]
    omega
  rw [hp0]
  constructor
  · intro hkl
    by_cases h3 : 3 ∣ k / s
    · simp only [loss, h3, ↓reduceIte] at hkl
      obtain ⟨q, hq⟩ := h3
      have hk_eq : k = s * (3 * q) := by
        have := Nat.mul_div_cancel' hs_dvd_k
        rw [hq] at this
        exact this.symm
      have hqpos : 1 ≤ q := by
        by_contra h0
        have : q = 0 := by omega
        rw [this] at hk_eq
        omega
      have hgcd_le : Nat.gcd k 2 ≤ 2 := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right k 2)
      have hq1 : q = 1 := by nlinarith
      subst hq1
      have hk3s : k = 3 * s := by omega
      have hs_eq : s = Nat.gcd k 2 := by omega
      have hs_le2 : s ≤ 2 := by omega
      have hs_cases : s = 1 ∨ s = 2 := by omega
      rcases hs_cases with hs1 | hs2
      · right
        refine ⟨Or.inl (by omega), ?_⟩
        intro h3sp
        have h3dvd : 3 ∣ s := Nat.dvd_gcd (by omega) (dvd_mul_of_dvd_right h3sp 2)
        omega
      · right
        refine ⟨Or.inr (by omega), ?_⟩
        intro h3sp
        have h6dvd : 6 ∣ s := Nat.dvd_gcd (by omega) (by obtain ⟨t, rfl⟩ := h3sp; exact ⟨t, by ring⟩)
        omega
    · simp only [loss, h3, ↓reduceIte, add_zero] at hkl
      have hgcd_le : Nat.gcd k 2 ≤ 2 := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right k 2)
      left; omega
  · rintro (hk2 | ⟨rfl | rfl, hnot3⟩)
    · have hk12 : k = 1 ∨ k = 2 := by omega
      rcases hk12 with rfl | rfl
      · have hs1 : s = 1 := Nat.gcd_one_left _
        have hnot3 : ¬ (3 ∣ 1 / s) := by simp [hs1]
        simp [loss, hnot3]
      · have hnot3 : ¬ (3 ∣ 2 / s) := by
          have : 2 / s ≤ 2 := Nat.div_le_self 2 s
          intro h
          have := Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd (by omega) hs_dvd_k) hs_pos) h
          omega
        simp [loss, hnot3]
    · have hs1 : s = 1 := by
        have hdv : s ∣ 3 := Nat.gcd_dvd_left 3 (2 * spacing)
        have hle3 : s ≤ 3 := Nat.le_of_dvd (by omega) hdv
        have hne3 : s ≠ 3 := fun h => by
          have h3 : 3 ∣ 2 * spacing := h ▸ Nat.gcd_dvd_right 3 (2 * spacing)
          exact hnot3 ((Nat.Prime.dvd_mul Nat.prime_three).mp h3 |>.resolve_left (by decide))
        have hne2 : s ≠ 2 := fun h => by rw [h] at hdv; omega
        omega
      simp [loss, hs1]
    · have hs2 : s = 2 := by
        have h2dvd : 2 ∣ s := Nat.dvd_gcd (by decide) (dvd_mul_right 2 spacing)
        have hdv : s ∣ 6 := Nat.gcd_dvd_left 6 (2 * spacing)
        have hle6 : s ≤ 6 := Nat.le_of_dvd (by omega) hdv
        have hne6 : s ≠ 6 := fun h => by
          have h6 : 6 ∣ 2 * spacing := h ▸ Nat.gcd_dvd_right 6 (2 * spacing)
          obtain ⟨t, ht⟩ := h6
          exact hnot3 ⟨t, by omega⟩
        obtain ⟨c, hc⟩ := h2dvd
        have hc_dvd : c ∣ 3 := by
          obtain ⟨t, ht⟩ := hdv
          rw [hc] at ht
          have h2 : 2 * 3 = 2 * (c * t) := by linarith
          exact ⟨t, Nat.eq_of_mul_eq_mul_left (by omega) h2⟩
        have : c = 1 := by
          have : c ≤ 3 := Nat.le_of_dvd (by omega) hc_dvd
          have : c ≠ 0 := by omega
          have : c ≠ 2 := fun h => by rw [h] at hc_dvd; omega
          have : c ≠ 3 := fun h => hne6 (by omega)
          omega
        omega
      simp [loss, hs2]

private lemma card_submodule_zmod2 {V : Type*} [AddCommGroup V] [Module K V] [Fintype V]
    (U : Submodule K V) [DecidablePred (· ∈ U)] :
    Fintype.card U = 2 ^ Module.finrank K U := by
  have h := Module.card_eq_pow_finrank (K := K) (V := U)
  simpa using h

private lemma sum_zmod2_char_eq_zero {U : Type*} [AddCommGroup U] [Module K U] [Fintype U]
    (f : U →ₗ[K] K) (hne : f ≠ 0) :
    (∑ u : U, if f u = 0 then (1 : ℤ) else -1) = 0 := by
  have hex : ∃ u0 : U, f u0 = 1 := by
    by_contra hall
    apply hne
    ext u
    have h0 : f u ≠ 1 := fun h => hall ⟨u, h⟩
    cases hfu : f u using Fin.cases with
    | zero => rfl
    | succ i =>
      fin_cases i
      exact absurd hfu h0
  obtain ⟨u0, hu0⟩ := hex
  have hshift : (∑ u : U, if f u = 0 then (1 : ℤ) else -1) =
      -(∑ u : U, if f u = 0 then (1 : ℤ) else -1) := by
    rw [← Finset.sum_neg_distrib]
    refine Fintype.sum_equiv (Equiv.addRight u0) _ _ fun u => ?_
    change (if f u = 0 then (1 : ℤ) else -1) = -(if f (u + u0) = 0 then (1 : ℤ) else -1)
    rw [map_add, hu0]
    rcases zmod2_eq_zero_or_one (f u) with h | h <;> simp [h, zmod2_add_self]
  linarith

private lemma single_affine_walsh_bound {V : Type*} [AddCommGroup V] [Module K V] [Fintype V]
    [DecidableEq V] (Q : V → K) (B : V →ₗ[K] V →ₗ[K] K)
    (hQ : ∀ u v : V, Q (u + v) = Q u + Q v + Q 0 + B u v)
    (U : Submodule K V) [DecidablePred (· ∈ U)] (x0 : V) (L : V →ₗ[K] K) (b : K) :
    let radU : Submodule K U :=
      { carrier := {w : U | ∀ u : U, B u.1 w.1 = 0}, add_mem' := fun ha hb u => by simp [ha u, hb u]
        zero_mem' := fun u => by simp
        smul_mem' := fun c _ ha u => by simp [ha u] }
    let hits := ((Finset.univ : Finset U).filter (fun u => Q (x0 + u.1) = L (x0 + u.1) + b)).card
    ((2 * hits : ℤ) - (Fintype.card U : ℤ)) ^ 2 ≤
      (Fintype.card U : ℤ) * (Fintype.card radU : ℤ) := by
  classical
  intro radU hits
  let χ : K → ℤ := fun a => if a = 0 then 1 else -1
  have hχ_mul : ∀ a c : K, χ (a + c) = χ a * χ c := by
    intro a c; fin_cases a <;> fin_cases c <;> rfl
  let S : ℤ := ∑ u : U, χ (Q (x0 + u.1) + L (x0 + u.1) + b)
  have hS_eq : S = (2 * hits : ℤ) - (Fintype.card U : ℤ) := by
    have hsplit : S =
        (∑ u ∈ (Finset.univ : Finset U).filter (fun u => Q (x0 + u.1) = L (x0 + u.1) + b),
          χ (Q (x0 + u.1) + L (x0 + u.1) + b)) +
        (∑ u ∈ (Finset.univ : Finset U).filter (fun u => ¬ Q (x0 + u.1) = L (x0 + u.1) + b),
          χ (Q (x0 + u.1) + L (x0 + u.1) + b)) :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ _ _).symm
    have h1 : ∀ u ∈ (Finset.univ : Finset U).filter (fun u => Q (x0 + u.1) = L (x0 + u.1) + b),
        χ (Q (x0 + u.1) + L (x0 + u.1) + b) = 1 := by
      intro u hu
      have heq := (Finset.mem_filter.mp hu).2
      rw [heq]
      have : L (x0 + u.1) + b + L (x0 + u.1) + b = 0 := by
        generalize L (x0 + u.1) = a; fin_cases a <;> fin_cases b <;> rfl
      rw [this]; rfl
    have h2 : ∀ u ∈ (Finset.univ : Finset U).filter (fun u => ¬ Q (x0 + u.1) = L (x0 + u.1) + b),
        χ (Q (x0 + u.1) + L (x0 + u.1) + b) = -1 := by
      intro u hu
      have hne := (Finset.mem_filter.mp hu).2
      have hne0 : Q (x0 + u.1) + L (x0 + u.1) + b ≠ 0 := by
        intro h0
        apply hne
        rw [add_assoc] at h0
        exact zmod2_add_eq_zero h0
      simp only [χ, hne0, ↓reduceIte]
    rw [hsplit, Finset.sum_congr rfl h1, Finset.sum_congr rfl h2,
      Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_neg_one]
    have htot := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset U)) (p := fun u => Q (x0 + u.1) = L (x0 + u.1) + b)
    rw [Finset.card_univ] at htot
    omega
  rw [← hS_eq]
  have hS2 : S ^ 2 = ∑ w : U, χ (Q (x0 + w.1) + Q x0 + L w.1) *
      ∑ u : U, χ (B u.1 w.1) := by
    rw [sq, Finset.sum_mul_sum]
    have hreidx : ∑ u : U, ∑ v : U,
        χ (Q (x0 + u.1) + L (x0 + u.1) + b) * χ (Q (x0 + v.1) + L (x0 + v.1) + b) =
        ∑ u : U, ∑ w : U,
          χ (Q (x0 + u.1) + L (x0 + u.1) + b) * χ (Q (x0 + (u + w).1) + L (x0 + (u + w).1) + b) := by
      refine Finset.sum_congr rfl fun u _ => ?_
      exact (Fintype.sum_equiv (Equiv.addLeft u) _ _ fun w => rfl).symm
    rw [hreidx, Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← hχ_mul, ← hχ_mul]
    congr 1
    have hQ1 : Q (x0 + (u.1 + w.1)) = Q (x0 + u.1) + Q w.1 + Q 0 + B (x0 + u.1) w.1 := by
      rw [← add_assoc, hQ]
    have hQ2 : Q (x0 + w.1) = Q x0 + Q w.1 + Q 0 + B x0 w.1 := hQ x0 w.1
    have hBadd : B (x0 + u.1) w.1 = B x0 w.1 + B u.1 w.1 := by simp
    have hLadd : L (x0 + (u.1 + w.1)) = L (x0 + u.1) + L w.1 := by
      rw [← add_assoc, map_add]
    simp only [Submodule.coe_add]
    rw [hQ1, hBadd, hLadd, hQ2]
    generalize Q (x0 + u.1) = a1
    generalize Q w.1 = a2
    generalize Q 0 = a3
    generalize Q x0 = a4
    generalize B x0 w.1 = a5
    generalize B u.1 w.1 = a6
    generalize L (x0 + u.1) = a7
    generalize L w.1 = a8
    have hr :
        a1 + a7 + b + (a1 + a2 + a3 + (a5 + a6) + (a7 + a8) + b) + (a4 + a4) =
        (a4 + a2 + a3 + a5 + a4 + a8 + a6) + (a1 + a1) + (a7 + a7) + (b + b) := by
      ring
    simpa only [zmod2_add_self, add_zero] using hr
  rw [hS2]
  have hinner : ∀ w : U,
      (∑ u : U, χ (B u.1 w.1)) = if w ∈ radU then (Fintype.card U : ℤ) else 0 := by
    intro w
    split_ifs with hw
    · have hall : ∀ u : U, χ (B u.1 w.1) = 1 := fun u => by
        have := hw u
        simp [χ, this]
      simp [hall]
    · let f : U →ₗ[K] K :=
        { toFun := fun u => B u.1 w.1
          map_add' := fun u1 u2 => by simp
          map_smul' := fun c u => by simp }
      have hne : f ≠ 0 := by
        intro h0
        apply hw
        intro u
        exact LinearMap.congr_fun h0 u
      exact sum_zmod2_char_eq_zero f hne
  simp_rw [hinner]
  have hle : ∑ w : U, χ (Q (x0 + w.1) + Q x0 + L w.1) *
      (if w ∈ radU then (Fintype.card U : ℤ) else 0) ≤
      ∑ w : U, if w ∈ radU then (Fintype.card U : ℤ) else 0 := by
    refine Finset.sum_le_sum fun w _ => ?_
    split_ifs
    · have hχ1 : χ (Q (x0 + w.1) + Q x0 + L w.1) ≤ 1 := by
        unfold χ; split_ifs <;> omega
      have hpos : (0 : ℤ) ≤ Fintype.card U := Nat.cast_nonneg _
      nlinarith
    · simp
  refine le_trans hle ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hcard_rad : ((Finset.univ : Finset U).filter (fun w => w ∈ radU)).card = Fintype.card radU := by
    rw [Fintype.card_subtype]
  rw [hcard_rad]

private lemma rad_codim_one_step {V : Type*} [AddCommGroup V] [Module K V] [Fintype V]
    (B : V →ₗ[K] V →ₗ[K] K) (U U' : Submodule K V) (hsub : U' ≤ U)
    (hcodim : Module.finrank K U ≤ Module.finrank K U' + 1) :
    let radU : Submodule K U :=
      { carrier := {w : U | ∀ u : U, B u.1 w.1 = 0}, add_mem' := fun ha hb u => by simp [ha u, hb u]
        zero_mem' := fun u => by simp
        smul_mem' := fun c _ ha u => by simp [ha u] }
    let radU' : Submodule K U' :=
      { carrier := {w : U' | ∀ u : U', B u.1 w.1 = 0}, add_mem' := fun ha hb u => by simp [ha u, hb u]
        zero_mem' := fun u => by simp
        smul_mem' := fun c _ ha u => by simp [ha u] }
    Module.finrank K radU' ≤ Module.finrank K radU + 1 := by
  classical
  intro radU radU'
  by_cases heq : U' = U
  · subst heq
    exact Nat.le_succ _
  · have hex : ∃ u0 : U, u0.1 ∉ U' := by
      by_contra hall
      apply heq
      apply le_antisymm hsub
      intro x hx
      by_contra hxn
      exact hall ⟨⟨x, hx⟩, hxn⟩
    obtain ⟨u0, hu0⟩ := hex
    let φ : radU' →ₗ[K] K :=
      { toFun := fun w => B u0.1 w.1.1
        map_add' := fun w1 w2 => by simp
        map_smul' := fun c w => by simp }
    have hker_le : Module.finrank K (LinearMap.ker φ) ≤ Module.finrank K radU := by
      let incl : LinearMap.ker φ →ₗ[K] radU :=
        { toFun := fun w => ⟨⟨w.1.1.1, hsub w.1.1.2⟩, fun u => by
            have hspan : ∀ x : U, x.1 ∈ U' ∨ (x.1 + u0.1) ∈ U' := by
              intro x
              by_cases hx : x.1 ∈ U'
              · exact Or.inl hx
              · right
                have hgt : Module.finrank K U' < Module.finrank K ↥(U' ⊔ Submodule.span K {u0.1}) := by
                  apply Submodule.finrank_lt_finrank_of_lt
                  refine lt_of_le_of_ne le_sup_left ?_
                  intro h
                  have : u0.1 ∈ U' ⊔ Submodule.span K {u0.1} :=
                    Submodule.mem_sup_right (Submodule.mem_span_singleton_self u0.1)
                  rw [← h] at this
                  exact hu0 this
                have hleU : U' ⊔ Submodule.span K {u0.1} ≤ U :=
                  sup_le hsub (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr u0.2))
                have hsup_eq : U' ⊔ Submodule.span K {u0.1} = U := by
                  apply Submodule.eq_of_le_of_finrank_eq hleU
                  have := Submodule.finrank_mono hleU
                  omega
                have hxmem : x.1 ∈ U' ⊔ Submodule.span K {u0.1} := by rw [hsup_eq]; exact x.2
                rw [Submodule.mem_sup] at hxmem
                obtain ⟨y, hyU', z, hz, hyz⟩ := hxmem
                rw [Submodule.mem_span_singleton] at hz
                obtain ⟨c, rfl⟩ := hz
                rcases zmod2_eq_zero_or_one c with rfl | rfl
                · simp only [zero_smul, add_zero] at hyz
                  exact absurd (hyz ▸ hyU') hx
                · simp only [one_smul] at hyz
                  have : x.1 + u0.1 = y := by
                    rw [← hyz, add_assoc, zmod2_vadd_self, add_zero]
                  rw [this]
                  exact hyU'
            rcases hspan u with hu' | hu'
            · exact w.1.2 ⟨u.1, hu'⟩
            · have h1 := w.1.2 ⟨u.1 + u0.1, hu'⟩
              have h2 : B u0.1 w.1.1.1 = 0 := w.2
              simp only [map_add, LinearMap.add_apply] at h1
              rw [h2, add_zero] at h1
              exact h1⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have hinj : Function.Injective incl := by
        intro w1 w2 h
        ext
        exact congrArg (fun z : radU => z.1.1) h
      exact LinearMap.finrank_le_finrank_of_injective hinj
    have hrn := LinearMap.finrank_range_add_finrank_ker φ
    have hran : Module.finrank K (LinearMap.range φ) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range φ)
      simpa using this
    omega

private lemma adaptive_upper_bound {V : Type*} [AddCommGroup V] [Module K V] [Fintype V]
    [DecidableEq V] (Q : V → K) (B : V →ₗ[K] V →ₗ[K] K)
    (hQ : ∀ u v : V, Q (u + v) = Q u + Q v + Q 0 + B u v) :
    ∀ (d : ℕ) (U : Submodule K V) [DecidablePred (· ∈ U)] (x0 : V) (r : ℕ),
      (∀ (radU : Submodule K U),
        (∀ w : U, w ∈ radU ↔ ∀ u : U, B u.1 w.1 = 0) →
        2 * r + Module.finrank K radU ≤ Module.finrank K U) →
      ∀ (ask : Fin d → ℕ → (V →ₗ[K] K)) (rule : ℕ → (V →ₗ[K] K)) (bias : ℕ → K) (h0 : ℕ),
        let runFrom := fun (x : V) =>
          (List.finRange d).foldl (fun h j => 2 * h + (if ask j h x = 0 then 0 else 1)) h0
        2 * ((Finset.univ : Finset U).filter (fun u =>
            Q (x0 + u.1) = rule (runFrom (x0 + u.1)) (x0 + u.1) + bias (runFrom (x0 + u.1)))).card ≤
          2 ^ Module.finrank K U + 2 ^ (Module.finrank K U - (r - d)) := by
  classical
  intro d
  induction d with
  | zero =>
    intro U _ x0 r hr ask rule bias h0
    let radU : Submodule K U :=
      { carrier := {w : U | ∀ u : U, B u.1 w.1 = 0}, add_mem' := fun ha hb u => by simp [ha u, hb u]
        zero_mem' := fun u => by simp
        smul_mem' := fun c _ ha u => by simp [ha u] }
    have hrad := hr radU (fun _ => Iff.rfl)
    have hwb := single_affine_walsh_bound Q B hQ U x0 (rule h0) (bias h0)
    have hcardU : Fintype.card U = 2 ^ Module.finrank K U := card_submodule_zmod2 U
    have hcardR : Fintype.card radU = 2 ^ Module.finrank K radU := card_submodule_zmod2 radU
    set hits := ((Finset.univ : Finset U).filter (fun u =>
      Q (x0 + u.1) = rule h0 (x0 + u.1) + bias h0)).card
    have hsq : ((2 * hits : ℤ) - (2 ^ Module.finrank K U : ℤ)) ^ 2 ≤
        (2 ^ (Module.finrank K U - r) : ℤ) ^ 2 := by
      calc ((2 * hits : ℤ) - (2 ^ Module.finrank K U : ℤ)) ^ 2
          ≤ (2 ^ Module.finrank K U : ℤ) * (2 ^ Module.finrank K radU : ℤ) := by
            change ((2 * hits : ℤ) - (Fintype.card U : ℤ)) ^ 2 ≤
              (Fintype.card U : ℤ) * (Fintype.card radU : ℤ) at hwb
            rw [hcardU, hcardR] at hwb
            exact_mod_cast hwb
        _ = (2 ^ (Module.finrank K U + Module.finrank K radU) : ℤ) := by
            rw [← pow_add]
        _ ≤ (2 ^ (2 * (Module.finrank K U - r)) : ℤ) := by
            exact_mod_cast Nat.pow_le_pow_right (by omega) (by omega)
        _ = (2 ^ (Module.finrank K U - r) : ℤ) ^ 2 := by
            rw [← pow_mul, mul_comm]
    have hlin : (2 * hits : ℤ) - (2 ^ Module.finrank K U : ℤ) ≤ (2 ^ (Module.finrank K U - r) : ℤ) := by
      have hpos : (0 : ℤ) ≤ (2 ^ (Module.finrank K U - r) : ℤ) := by positivity
      by_contra hlt
      push Not at hlt
      nlinarith
    simp only [Nat.sub_zero, List.finRange_zero, List.foldl_nil]
    have hlin' : (2 * hits : ℤ) ≤ (2 ^ Module.finrank K U : ℤ) + (2 ^ (Module.finrank K U - r) : ℤ) := by
      linarith
    exact_mod_cast hlin'
  | succ d ih =>
    intro U _ x0 r hr ask rule bias h0
    let ℓ : V →ₗ[K] K := ask 0 h0
    let ask' : Fin d → ℕ → (V →ₗ[K] K) := fun j h => ask j.succ h
    have hfold : ∀ x : V,
        (List.finRange (d + 1)).foldl (fun h j => 2 * h + (if ask j h x = 0 then 0 else 1)) h0 =
        (List.finRange d).foldl (fun h j => 2 * h + (if ask' j h x = 0 then 0 else 1))
          (2 * h0 + (if ℓ x = 0 then 0 else 1)) := by
      intro x
      rw [List.finRange_succ, List.foldl_cons, List.foldl_map]
    simp_rw [hfold]
    let ℓU : U →ₗ[K] K := ℓ.comp U.subtype
    by_cases hzero : ℓU = 0
    · have hconst : ∀ u : U, ℓ (x0 + u.1) = ℓ x0 := by
        intro u
        have hu : ℓ u.1 = 0 := LinearMap.congr_fun hzero u
        rw [map_add, hu, add_zero]
      simp_rw [hconst]
      have hih := ih U x0 r hr ask' rule bias (2 * h0 + (if ℓ x0 = 0 then 0 else 1))
      dsimp only at hih
      have hpow : 2 ^ (Module.finrank K U - (r - d)) ≤ 2 ^ (Module.finrank K U - (r - (d + 1))) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
    · have hex1 : ∃ u1 : U, ℓ u1.1 = 1 := by
        by_contra hall
        apply hzero
        ext u
        have h1 : ℓ u.1 ≠ 1 := fun h => hall ⟨u, h⟩
        rcases zmod2_eq_zero_or_one (ℓ u.1) with h | h
        · exact h
        · exact absurd h h1
      obtain ⟨u1, hu1⟩ := hex1
      let U' : Submodule K V := U ⊓ LinearMap.ker ℓ
      have hU'_le : U' ≤ U := inf_le_left
      have hdim_U' : Module.finrank K U' + 1 = Module.finrank K U := by
        have hrn := LinearMap.finrank_range_add_finrank_ker ℓU
        have hran : Module.finrank K (LinearMap.range ℓU) = 1 := by
          have hle1 : Module.finrank K (LinearMap.range ℓU) ≤ 1 := by
            have := Submodule.finrank_le (LinearMap.range ℓU)
            simpa using this
          have hpos : 0 < Module.finrank K (LinearMap.range ℓU) := by
            rw [Module.finrank_pos_iff_exists_ne_zero]
            exact ⟨⟨1, ⟨u1, hu1⟩⟩, fun h => by
              have h1 : (1 : K) = 0 := congrArg Subtype.val h
              exact absurd h1 (by decide)⟩
          omega
        have hker_eq : Module.finrank K (LinearMap.ker ℓU) = Module.finrank K U' := by
          let e : LinearMap.ker ℓU ≃ₗ[K] U' :=
            { toFun := fun u => ⟨u.1.1, u.1.2, u.2⟩
              invFun := fun u => ⟨⟨u.1, u.2.1⟩, u.2.2⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl
              map_add' := fun _ _ => rfl
              map_smul' := fun _ _ => rfl }
          exact LinearEquiv.finrank_eq e
        omega
      have hr' : ∀ (radU' : Submodule K U'),
          (∀ w : U', w ∈ radU' ↔ ∀ u : U', B u.1 w.1 = 0) →
          2 * (r - 1) + Module.finrank K radU' ≤ Module.finrank K U' := by
        intro radU' hradU'
        let radU : Submodule K U :=
          { carrier := {w : U | ∀ u : U, B u.1 w.1 = 0}, add_mem' := fun ha hb u => by simp [ha u, hb u]
            zero_mem' := fun u => by simp
            smul_mem' := fun c _ ha u => by simp [ha u] }
        let radU'_can : Submodule K U' :=
          { carrier := {w : U' | ∀ u : U', B u.1 w.1 = 0}, add_mem' := fun ha hb u => by simp [ha u, hb u]
            zero_mem' := fun u => by simp
            smul_mem' := fun c _ ha u => by simp [ha u] }
        have heq_rad : radU' = radU'_can := by ext w; exact hradU' w
        rw [heq_rad]
        have hstep : Module.finrank K radU'_can ≤ Module.finrank K radU + 1 :=
          rad_codim_one_step B U U' hU'_le (by omega)
        have hbase := hr radU (fun _ => Iff.rfl)
        have hleU' := Submodule.finrank_le radU'_can
        omega
      let xA : V := if ℓ x0 = 0 then x0 else x0 + u1.1
      let xB : V := if ℓ x0 = 0 then x0 + u1.1 else x0
      have hxA : ℓ xA = 0 := by
        dsimp only [xA]
        split_ifs with h
        · exact h
        · rw [map_add, hu1]
          cases h0' : ℓ x0 using Fin.cases with
          | zero => exact absurd h0' h
          | succ i => fin_cases i; rfl
      have hxB : ℓ xB = 1 := by
        dsimp only [xB]
        split_ifs with h
        · rw [map_add, h, hu1, zero_add]
        · cases h0' : ℓ x0 using Fin.cases with
          | zero => exact absurd h0' h
          | succ i => fin_cases i; rfl
      have hsplit_card :
          ((Finset.univ : Finset U).filter (fun u =>
            Q (x0 + u.1) = rule ((List.finRange d).foldl (fun h j => 2 * h + (if ask' j h (x0 + u.1) = 0 then 0 else 1))
              (2 * h0 + (if ℓ (x0 + u.1) = 0 then 0 else 1))) (x0 + u.1) +
            bias ((List.finRange d).foldl (fun h j => 2 * h + (if ask' j h (x0 + u.1) = 0 then 0 else 1))
              (2 * h0 + (if ℓ (x0 + u.1) = 0 then 0 else 1))))).card =
          ((Finset.univ : Finset U').filter (fun u =>
            Q (xA + u.1) = rule ((List.finRange d).foldl (fun h j => 2 * h + (if ask' j h (xA + u.1) = 0 then 0 else 1))
              (2 * h0)) (xA + u.1) +
            bias ((List.finRange d).foldl (fun h j => 2 * h + (if ask' j h (xA + u.1) = 0 then 0 else 1))
              (2 * h0)))).card +
          ((Finset.univ : Finset U').filter (fun u =>
            Q (xB + u.1) = rule ((List.finRange d).foldl (fun h j => 2 * h + (if ask' j h (xB + u.1) = 0 then 0 else 1))
              (2 * h0 + 1)) (xB + u.1) +
            bias ((List.finRange d).foldl (fun h j => 2 * h + (if ask' j h (xB + u.1) = 0 then 0 else 1))
              (2 * h0 + 1)))).card := by
        rw [← Finset.card_filter_add_card_filter_not (p := fun u : U => ℓ (x0 + u.1) = 0)]
        congr 1
        · refine Finset.card_bij (fun u _ =>
            (⟨if ℓ x0 = 0 then u.1 else u.1 + u1.1, by
              have hu_cond : ℓ (x0 + u.1) = 0 := by
                have := (Finset.mem_filter.mp ‹_›).2
                exact this
              split_ifs with h
              · exact ⟨u.2, by rw [map_add, h, zero_add] at hu_cond; exact hu_cond⟩
              · refine ⟨U.add_mem u.2 u1.2, ?_⟩
                change ℓ (u.1 + u1.1) = 0
                rw [map_add, hu1]
                rw [map_add] at hu_cond
                rcases zmod2_eq_zero_or_one (ℓ x0) with h0' | h0'
                · exact absurd h0' h
                · rw [h0'] at hu_cond
                  rcases zmod2_eq_zero_or_one (ℓ u.1) with hu' | hu'
                  · rw [hu'] at hu_cond; exact absurd hu_cond (by decide)
                  · rw [hu']; rfl⟩ : U')) ?_ ?_ ?_
          · intro u hu
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
            have heq : xA + (if ℓ x0 = 0 then u.1 else u.1 + u1.1) = x0 + u.1 := by
              dsimp only [xA]
              split_ifs
              · rfl
              · have h1 : (x0 + u1.1) + (u.1 + u1.1) = x0 + u.1 + (u1.1 + u1.1) := by abel
                rw [h1, zmod2_vadd_self, add_zero]
            rw [heq]
            simpa only [hu.2, ↓reduceIte, add_zero] using hu.1
          · intro u _ v _ h
            ext
            have h1 := congrArg Subtype.val h
            dsimp only at h1
            split_ifs at h1
            · exact h1
            · have := congrArg (· + u1.1) h1
              simpa [add_assoc, zmod2_vadd_self] using this
          · intro w hw
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
            let u : U := ⟨if ℓ x0 = 0 then w.1 else w.1 + u1.1, by
              split_ifs
              · exact w.2.1
              · exact U.add_mem w.2.1 u1.2⟩
            have heq : x0 + u.1 = xA + w.1 := by
              dsimp only [u, xA]
              split_ifs
              · rfl
              · rw [add_assoc, add_comm w.1 u1.1, ← add_assoc]
            have hlu : ℓ (x0 + u.1) = 0 := by
              rw [heq, map_add, hxA, w.2.2, add_zero]
            refine ⟨u, ?_, ?_⟩
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hlu, ↓reduceIte, add_zero]
              simpa [heq] using hw
            · ext
              dsimp only [u]
              split_ifs
              · rfl
              · rw [add_assoc, zmod2_vadd_self, add_zero]
        · refine Finset.card_bij (fun u _ =>
            (⟨if ℓ x0 = 0 then u.1 + u1.1 else u.1, by
              have hu_cond : ¬ ℓ (x0 + u.1) = 0 := by
                have := (Finset.mem_filter.mp ‹_›).2
                exact this
              split_ifs with h
              · refine ⟨U.add_mem u.2 u1.2, ?_⟩
                change ℓ (u.1 + u1.1) = 0
                rw [map_add, hu1]
                rw [map_add, h, zero_add] at hu_cond
                rcases zmod2_eq_zero_or_one (ℓ u.1) with hu' | hu'
                · exact absurd hu' hu_cond
                · rw [hu']; rfl
              · refine ⟨u.2, ?_⟩
                change ℓ u.1 = 0
                rw [map_add] at hu_cond
                rcases zmod2_eq_zero_or_one (ℓ x0) with h0' | h0'
                · exact absurd h0' h
                · rw [h0'] at hu_cond
                  rcases zmod2_eq_zero_or_one (ℓ u.1) with hu' | hu'
                  · exact hu'
                  · rw [hu'] at hu_cond; exact absurd (by decide : (1 : K) + 1 = 0) hu_cond⟩ : U')) ?_ ?_ ?_
          · intro u hu
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
            have heq : xB + (if ℓ x0 = 0 then u.1 + u1.1 else u.1) = x0 + u.1 := by
              dsimp only [xB]
              split_ifs
              · have h1 : (x0 + u1.1) + (u.1 + u1.1) = x0 + u.1 + (u1.1 + u1.1) := by abel
                rw [h1, zmod2_vadd_self, add_zero]
              · rfl
            rw [heq]
            simpa only [hu.2, ↓reduceIte] using hu.1
          · intro u _ v _ h
            ext
            have h1 := congrArg Subtype.val h
            dsimp only at h1
            split_ifs at h1
            · have := congrArg (· + u1.1) h1
              simpa [add_assoc, zmod2_vadd_self] using this
            · exact h1
          · intro w hw
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
            let u : U := ⟨if ℓ x0 = 0 then w.1 + u1.1 else w.1, by
              split_ifs
              · exact U.add_mem w.2.1 u1.2
              · exact w.2.1⟩
            have heq : x0 + u.1 = xB + w.1 := by
              dsimp only [u, xB]
              split_ifs
              · rw [add_assoc, add_comm w.1 u1.1, ← add_assoc]
              · rfl
            have hlu : ¬ ℓ (x0 + u.1) = 0 := by
              rw [heq, map_add, hxB, w.2.2, add_zero]
              decide
            refine ⟨u, ?_, ?_⟩
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hlu, ↓reduceIte]
              simpa [heq] using hw
            · ext
              dsimp only [u]
              split_ifs
              · rw [add_assoc, zmod2_vadd_self, add_zero]
              · rfl
      rw [hsplit_card]
      have hihA := ih U' xA (r - 1) hr' ask' rule bias (2 * h0)
      have hihB := ih U' xB (r - 1) hr' ask' rule bias (2 * h0 + 1)
      dsimp only at hihA hihB
      have hpow1 : 2 ^ Module.finrank K U = 2 * 2 ^ Module.finrank K U' := by
        rw [← hdim_U', Nat.pow_succ]; omega
      have hpow2 : 2 ^ (Module.finrank K U - (r - (d + 1))) =
          2 * 2 ^ (Module.finrank K U' - ((r - 1) - d)) := by
        have hexp : Module.finrank K U - (r - (d + 1)) = (Module.finrank K U' - ((r - 1) - d)) + 1 := by
          have : r ≤ Module.finrank K U := by
            let radU : Submodule K U :=
              { carrier := {w : U | ∀ u : U, B u.1 w.1 = 0}, add_mem' := fun ha hb u => by simp [ha u, hb u]
                zero_mem' := fun u => by simp
                smul_mem' := fun c _ ha u => by simp [ha u] }
            have := hr radU (fun _ => Iff.rfl)
            omega
          omega
        rw [hexp, Nat.pow_succ]; omega
      omega

private lemma exists_symplectic_decomposition {V : Type*} [AddCommGroup V] [Module K V] [Fintype V]
    (B : V →ₗ[K] V →ₗ[K] K)
    (hB_alt : ∀ u : V, B u u = 0)
    (hB_sym : ∀ u v : V, B u v = B v u) :
    ∀ (U : Submodule K V),
      let radU : Submodule K U :=
        { carrier := {w : U | ∀ u : U, B u.1 w.1 = 0}, add_mem' := fun ha hb u => by simp [ha u, hb u]
          zero_mem' := fun u => by simp
          smul_mem' := fun c _ ha u => by simp [ha u] }
      ∃ (p : ℕ) (e f : Fin p → U),
        2 * p + Module.finrank K radU = Module.finrank K U ∧
        (∀ i j : Fin p, B (e i).1 (f j).1 = if i = j then 1 else 0) ∧
        (∀ i j : Fin p, B (e i).1 (e j).1 = 0) ∧
        (∀ i j : Fin p, B (f i).1 (f j).1 = 0) ∧
        ∀ x : U, x - (∑ i : Fin p, (B x.1 (f i).1 • e i + B x.1 (e i).1 • f i)) ∈ radU := by
  classical
  have hgen : ∀ (m : ℕ) (U : Submodule K V), Module.finrank K U ≤ m →
      let radU : Submodule K U :=
        { carrier := {w : U | ∀ u : U, B u.1 w.1 = 0}, add_mem' := fun ha hb u => by simp [ha u, hb u]
          zero_mem' := fun u => by simp
          smul_mem' := fun c _ ha u => by simp [ha u] }
      ∃ (p : ℕ) (e f : Fin p → U),
        2 * p + Module.finrank K radU = Module.finrank K U ∧
        (∀ i j : Fin p, B (e i).1 (f j).1 = if i = j then 1 else 0) ∧
        (∀ i j : Fin p, B (e i).1 (e j).1 = 0) ∧
        (∀ i j : Fin p, B (f i).1 (f j).1 = 0) ∧
        ∀ x : U, x - (∑ i : Fin p, (B x.1 (f i).1 • e i + B x.1 (e i).1 • f i)) ∈ radU := by
    intro m
    induction m with
    | zero =>
      intro U hm radU
      refine ⟨0, Fin.elim0, Fin.elim0, ?_, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
      · have hU0 : Module.finrank K U = 0 := by omega
        have hR0 : Module.finrank K radU ≤ 0 := by
          have := Submodule.finrank_le radU
          omega
        omega
      · intro x u
        have hU0 : Module.finrank K U = 0 := by omega
        have hx0 : x = 0 := by
          have hcard : Fintype.card U = 1 := by rw [card_submodule_zmod2, hU0, pow_zero]
          haveI : Subsingleton U := Fintype.card_le_one_iff_subsingleton.mp (le_of_eq hcard)
          exact Subsingleton.elim x 0
        simp [hx0]
    | succ m ih =>
      intro U hm radU
      by_cases hall : ∀ u v : U, B u.1 v.1 = 0
      · refine ⟨0, Fin.elim0, Fin.elim0, ?_, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
        · have htop : radU = ⊤ := by ext w; simp [radU, hall]
          rw [htop, finrank_top]; omega
        · intro x u; simp [hall]
      · push_neg at hall
        obtain ⟨e0, f0, hne⟩ := hall
        have hB0 : B e0.1 f0.1 = 1 := by
          cases h : B e0.1 f0.1 using Fin.cases with
          | zero => exact absurd h hne
          | succ i => fin_cases i; rfl
        let U' : Submodule K V :=
          { carrier := {x : V | x ∈ U ∧ B x e0.1 = 0 ∧ B x f0.1 = 0}, add_mem' := fun ha hb => ⟨U.add_mem ha.1 hb.1, by simp [ha.2.1, hb.2.1], by simp [ha.2.2, hb.2.2]⟩
            zero_mem' := ⟨U.zero_mem, by simp, by simp⟩
            smul_mem' := fun c _ ha => ⟨U.smul_mem c ha.1, by simp [ha.2.1], by simp [ha.2.2]⟩ }
        have hU'_le : U' ≤ U := fun x hx => hx.1
        let proj : U →ₗ[K] U' :=
          { toFun := fun x => ⟨x.1 + B x.1 f0.1 • e0.1 + B x.1 e0.1 • f0.1,
              ⟨U.add_mem (U.add_mem x.2 (U.smul_mem _ e0.2)) (U.smul_mem _ f0.2),
               by simp [hB_alt, hB_sym f0.1 e0.1, hB0, zmod2_add_self],
               by simp [hB_alt, hB0, zmod2_add_self]⟩⟩
            map_add' := fun x y => by ext; simp [add_smul]; abel
            map_smul' := fun c x => by ext; simp [mul_smul, smul_add] }
        have hdimU' : Module.finrank K U' + 2 = Module.finrank K U := by
          let φ : U →ₗ[K] (K × K) :=
            { toFun := fun x => (B x.1 f0.1, B x.1 e0.1)
              map_add' := fun x y => by ext <;> simp
              map_smul' := fun c x => by ext <;> simp }
          have hsurj : Function.Surjective φ := by
            rintro ⟨a, b⟩
            refine ⟨a • e0 + b • f0, ?_⟩
            ext <;> simp [φ, hB_alt, hB0, hB_sym f0.1 e0.1]
          have hker_eq : Module.finrank K (LinearMap.ker φ) = Module.finrank K U' := by
            let e : LinearMap.ker φ ≃ₗ[K] U' :=
              { toFun := fun x => ⟨x.1.1, x.1.2, (Prod.ext_iff.mp x.2).2, (Prod.ext_iff.mp x.2).1⟩
                invFun := fun x => ⟨⟨x.1, x.2.1⟩, Prod.ext x.2.2.2 x.2.2.1⟩
                left_inv := fun _ => rfl
                right_inv := fun _ => rfl
                map_add' := fun _ _ => rfl
                map_smul' := fun _ _ => rfl }
            exact LinearEquiv.finrank_eq e
          have hrn := LinearMap.finrank_range_add_finrank_ker φ
          have hran : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hsurj
          rw [hran, finrank_top, hker_eq] at hrn
          have hkk : Module.finrank K (K × K) = 2 := by simp
          omega
        obtain ⟨p', e', f', hpdim, hef', hee', hff', hrad'⟩ := ih U' (by omega)
        let radU' : Submodule K U' :=
          { carrier := {w : U' | ∀ u : U', B u.1 w.1 = 0}, add_mem' := fun ha hb u => by simp [ha u, hb u]
            zero_mem' := fun u => by simp
            smul_mem' := fun c _ ha u => by simp [ha u] }
        have hrad_eq : Module.finrank K radU' = Module.finrank K radU := by
          let e : radU' ≃ₗ[K] radU :=
            { toFun := fun w => ⟨⟨w.1.1, w.1.2.1⟩, fun u => by
                have h1 := w.2 (proj u)
                change B (u.1 + B u.1 f0.1 • e0.1 + B u.1 e0.1 • f0.1) w.1.1 = 0 at h1
                simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
                  smul_eq_mul] at h1
                have he0w : B e0.1 w.1.1 = 0 := by rw [hB_sym]; exact w.1.2.2.1
                have hf0w : B f0.1 w.1.1 = 0 := by rw [hB_sym]; exact w.1.2.2.2
                rw [he0w, hf0w] at h1
                simpa using h1⟩
              invFun := fun w => ⟨⟨w.1.1, w.1.2, by rw [hB_sym]; exact w.2 e0,
                by rw [hB_sym]; exact w.2 f0⟩, fun u => w.2 ⟨u.1, u.2.1⟩⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl
              map_add' := fun _ _ => rfl
              map_smul' := fun _ _ => rfl }
          exact LinearEquiv.finrank_eq e
        have hpdim' : 2 * p' + Module.finrank K radU' = Module.finrank K U' := hpdim
        let e : Fin (p' + 1) → U := Fin.cons e0 (fun i => ⟨(e' i).1, (e' i).2.1⟩)
        let f : Fin (p' + 1) → U := Fin.cons f0 (fun i => ⟨(f' i).1, (f' i).2.1⟩)
        refine ⟨p' + 1, e, f, by omega, ?_, ?_, ?_, ?_⟩
        · intro i j
          refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
          · simp [e, f, hB0]
          · simp only [e, f, Fin.cons_zero, Fin.cons_succ, (Fin.succ_ne_zero j').symm, ↓reduceIte]
            rw [hB_sym]
            exact (f' j').2.2.1
          · simp only [e, f, Fin.cons_zero, Fin.cons_succ, Fin.succ_ne_zero, ↓reduceIte]
            exact (e' i').2.2.2
          · simp only [e, f, Fin.cons_succ, Fin.succ_inj]
            exact hef' i' j'
        · intro i j
          refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
          · simp [e, hB_alt]
          · simp only [e, Fin.cons_zero, Fin.cons_succ]
            rw [hB_sym]
            exact (e' j').2.2.1
          · simp only [e, Fin.cons_zero, Fin.cons_succ]
            exact (e' i').2.2.1
          · simp only [e, Fin.cons_succ]
            exact hee' i' j'
        · intro i j
          refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
          · simp [f, hB_alt]
          · simp only [f, Fin.cons_zero, Fin.cons_succ]
            rw [hB_sym]
            exact (f' j').2.2.2
          · simp only [f, Fin.cons_zero, Fin.cons_succ]
            exact (f' i').2.2.2
          · simp only [f, Fin.cons_succ]
            exact hff' i' j'
        · intro x u
          have hmem' := hrad' (proj x)
          have hbu' : B (proj u).1 (proj x - ∑ i : Fin p',
              (B (proj x).1 (f' i).1 • e' i + B (proj x).1 (e' i).1 • f' i)).1 = 0 :=
            hmem' (proj u)
          have hBxf : ∀ i : Fin p', B (proj x).1 (f' i).1 = B x.1 (f' i).1 := by
            intro i
            change B (x.1 + B x.1 f0.1 • e0.1 + B x.1 e0.1 • f0.1) (f' i).1 = B x.1 (f' i).1
            simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
            rw [hB_sym e0.1 (f' i).1, (f' i).2.2.1, hB_sym f0.1 (f' i).1, (f' i).2.2.2]
            simp
          have hBxe : ∀ i : Fin p', B (proj x).1 (e' i).1 = B x.1 (e' i).1 := by
            intro i
            change B (x.1 + B x.1 f0.1 • e0.1 + B x.1 e0.1 • f0.1) (e' i).1 = B x.1 (e' i).1
            simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
            rw [hB_sym e0.1 (e' i).1, (e' i).2.2.1, hB_sym f0.1 (e' i).1, (e' i).2.2.2]
            simp
          have hdiff : (x - ∑ i : Fin (p' + 1), (B x.1 (f i).1 • e i + B x.1 (e i).1 • f i)).1 =
              (proj x - ∑ i : Fin p', (B (proj x).1 (f' i).1 • e' i + B (proj x).1 (e' i).1 • f' i)).1 := by
            simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_add, Submodule.coe_smul,
              Fin.sum_univ_succ, e, f, Fin.cons_zero, Fin.cons_succ, hBxf, hBxe]
            simp only [proj, LinearMap.coe_mk, AddHom.coe_mk, sub_eq_add_neg, zmod2_vneg]
            abel
          rw [hdiff]
          have hu_eq : u.1 = (proj u).1 + (B u.1 f0.1 • e0.1 + B u.1 e0.1 • f0.1) := by
            change u.1 = (u.1 + B u.1 f0.1 • e0.1 + B u.1 e0.1 • f0.1) + (B u.1 f0.1 • e0.1 + B u.1 e0.1 • f0.1)
            have h1 : B u.1 f0.1 • e0.1 + B u.1 f0.1 • e0.1 = 0 := zmod2_vadd_self _
            have h2 : B u.1 e0.1 • f0.1 + B u.1 e0.1 • f0.1 = 0 := zmod2_vadd_self _
            calc u.1 = u.1 + 0 + 0 := by simp
              _ = u.1 + (B u.1 f0.1 • e0.1 + B u.1 f0.1 • e0.1) +
                  (B u.1 e0.1 • f0.1 + B u.1 e0.1 • f0.1) := by rw [h1, h2]
              _ = u.1 + B u.1 f0.1 • e0.1 + B u.1 e0.1 • f0.1 +
                  (B u.1 f0.1 • e0.1 + B u.1 e0.1 • f0.1) := by abel
          rw [hu_eq, map_add, LinearMap.add_apply, hbu', zero_add]
          have hmemU' : (proj x - ∑ i : Fin p',
              (B (proj x).1 (f' i).1 • e' i + B (proj x).1 (e' i).1 • f' i)).1 ∈ U' :=
            (proj x - ∑ i : Fin p',
              (B (proj x).1 (f' i).1 • e' i + B (proj x).1 (e' i).1 • f' i)).2
          simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
          rw [hB_sym e0.1, hmemU'.2.1, hB_sym f0.1, hmemU'.2.2]
          simp
  intro U
  exact hgen (Module.finrank K U) U le_rfl

private lemma card_inner_prod_zero (t : ℕ) :
    ((Finset.univ : Finset (Fin t → K × K)).filter
      (fun ab => ∑ i : Fin t, (ab i).1 * (ab i).2 = 0)).card = (4 ^ t + 2 ^ t) / 2 := by
  induction t with
  | zero => decide
  | succ t ih =>
    let g : (Fin (t + 1) → K × K) → (K × K) × (Fin t → K × K) :=
      fun ab => (ab 0, fun i => ab i.succ)
    have hbij : ((Finset.univ : Finset (Fin (t + 1) → K × K)).filter
        (fun ab => ∑ i : Fin (t + 1), (ab i).1 * (ab i).2 = 0)).card =
        ((Finset.univ : Finset ((K × K) × (Fin t → K × K))).filter
          (fun p => p.1.1 * p.1.2 + ∑ i : Fin t, (p.2 i).1 * (p.2 i).2 = 0)).card := by
      refine Finset.card_bij (fun ab _ => g ab) ?_ ?_ ?_
      · intro ab hab
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, g] at hab ⊢
        rwa [Fin.sum_univ_succ] at hab
      · intro a _ b _ h
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact congrArg Prod.fst h
        · exact congrFun (congrArg Prod.snd h) j
      · rintro ⟨p0, rest⟩ hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        refine ⟨Fin.cons p0 rest, ?_, by ext <;> simp [g]⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.sum_univ_succ,
          Fin.cons_zero, Fin.cons_succ]
        exact hp
    rw [hbij]
    set S0 := ((Finset.univ : Finset (Fin t → K × K)).filter
      (fun ab => ∑ i : Fin t, (ab i).1 * (ab i).2 = 0)).card
    set S1 := ((Finset.univ : Finset (Fin t → K × K)).filter
      (fun ab => ∑ i : Fin t, (ab i).1 * (ab i).2 = 1)).card
    have htot : S0 + S1 = 4 ^ t := by
      have h1 : S0 + S1 = Fintype.card (Fin t → K × K) := by
        have hne : ∀ x : K, (¬ x = 0) ↔ (x = 1) := by decide
        have := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin t → K × K)))
          (p := fun ab => ∑ i : Fin t, (ab i).1 * (ab i).2 = 0)
        rw [Finset.card_univ] at this
        simpa [S0, S1, hne] using this
      rw [h1]
      simp [Fintype.card_fin]
    have hcnt : ((Finset.univ : Finset ((K × K) × (Fin t → K × K))).filter
        (fun p => p.1.1 * p.1.2 + ∑ i : Fin t, (p.2 i).1 * (p.2 i).2 = 0)).card =
        3 * S0 + 1 * S1 := by
      have hsum : ((Finset.univ : Finset ((K × K) × (Fin t → K × K))).filter
          (fun p => p.1.1 * p.1.2 + ∑ i : Fin t, (p.2 i).1 * (p.2 i).2 = 0)).card =
          ∑ p0 : K × K, ((Finset.univ : Finset (Fin t → K × K)).filter
            (fun rest => p0.1 * p0.2 + ∑ i : Fin t, (rest i).1 * (rest i).2 = 0)).card := by
        rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun p0 _ => ?_
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [hsum]
      have hval : ∀ p0 : K × K,
          ((Finset.univ : Finset (Fin t → K × K)).filter
            (fun rest => p0.1 * p0.2 + ∑ i : Fin t, (rest i).1 * (rest i).2 = 0)).card =
          if p0.1 * p0.2 = 0 then S0 else S1 := by
        intro p0
        split_ifs with h0
        · simp [h0, S0]
        · have h1 : p0.1 * p0.2 = 1 := (zmod2_eq_zero_or_one _).resolve_left h0
          simp only [h1, S1]
          congr 1; ext rest
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have h1v : ∀ v : K, (1 + v = 0) ↔ (v = 1) := by decide
          exact h1v _
      simp_rw [hval]
      rw [Fintype.sum_prod_type]
      change ∑ a : Fin 2, ∑ b : Fin 2, (if (a : K) * (b : K) = 0 then S0 else S1) = 3 * S0 + 1 * S1
      simp [Fin.sum_univ_two]
      omega
    rw [hcnt]
    have h4 : 4 ^ (t + 1) = 4 * 4 ^ t := by rw [Nat.pow_succ]; omega
    have h2 : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [Nat.pow_succ]; omega
    have heven : (4 ^ t + 2 ^ t) % 2 = 0 := by
      cases t with
      | zero => decide
      | succ t' =>
        rw [Nat.pow_succ, Nat.pow_succ]
        omega
    omega

private lemma adaptive_attain {V : Type*} [AddCommGroup V] [Module K V] [Fintype V]
    [DecidableEq V] (Q : V → K) (B : V →ₗ[K] V →ₗ[K] K)
    (hQ : ∀ u v : V, Q (u + v) = Q u + Q v + Q 0 + B u v)
    (hB_alt : ∀ u : V, B u u = 0)
    (hB_sym : ∀ u v : V, B u v = B v u)
    (k p d : ℕ) (hk : Module.finrank K V = k)
    (hrad_dim : Module.finrank K
      ({ carrier := {w : V | ∀ u : V, B u w = 0}, add_mem' := fun ha hb u => by simp [ha u, hb u]
         zero_mem' := fun u => by simp
         smul_mem' := fun c _ ha u => by simp [ha u] } : Submodule K V) = k - 2 * p)
    (hp2 : 2 * p ≤ k) :
    ∃ (ask : Fin d → ℕ → (V →ₗ[K] K)) (rule : ℕ → (V →ₗ[K] K)) (bias : ℕ → K),
      let run := fun (x : V) =>
        (List.finRange d).foldl (fun h j => 2 * h + (if ask j h x = 0 then 0 else 1)) 0
      ((Finset.univ : Finset V).filter (fun x =>
        Q x = rule (run x) x + bias (run x))).card = (2 ^ k + 2 ^ (k - (p - d))) / 2 := by
  classical
  obtain ⟨p', e, f, hpdim, hef, hee, hff, hrad⟩ := exists_symplectic_decomposition B hB_alt hB_sym ⊤
  let radV : Submodule K V :=
    { carrier := {w : V | ∀ u : V, B u w = 0}, add_mem' := fun ha hb u => by simp [ha u, hb u]
      zero_mem' := fun u => by simp
      smul_mem' := fun c _ ha u => by simp [ha u] }
  let radTop : Submodule K (⊤ : Submodule K V) :=
    { carrier := {w : (⊤ : Submodule K V) | ∀ u : (⊤ : Submodule K V), B u.1 w.1 = 0}, add_mem' := fun ha hb u => by simp [ha u, hb u]
      zero_mem' := fun u => by simp
      smul_mem' := fun c _ ha u => by simp [ha u] }
  have hrad_top_eq : Module.finrank K radTop = Module.finrank K radV := by
    let eqv : radTop ≃ₗ[K] radV :=
      { toFun := fun w => ⟨w.1.1, fun u => w.2 ⟨u, trivial⟩⟩
        invFun := fun w => ⟨⟨w.1, trivial⟩, fun u => w.2 u.1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact LinearEquiv.finrank_eq eqv
  have htop_dim : Module.finrank K (⊤ : Submodule K V) = k := by rw [finrank_top, hk]
  have hp_eq : p' = p := by
    rw [hrad_top_eq, hrad_dim, htop_dim] at hpdim
    omega
  subst p'
  let aL : Fin p → (V →ₗ[K] K) := fun i =>
    { toFun := fun x => B x (f i).1
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp }
  let bL : Fin p → (V →ₗ[K] K) := fun i =>
    { toFun := fun x => B x (e i).1
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp }
  let rProj : V →ₗ[K] radV :=
    { toFun := fun x =>
        ⟨x + ∑ i : Fin p, (aL i x • (e i).1 + bL i x • (f i).1), fun u => by
          have h := hrad ⟨x, trivial⟩ ⟨u, trivial⟩
          simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_add, Submodule.coe_smul] at h
          simpa [sub_eq_add_neg, zmod2_vneg, aL, bL] using h⟩
      map_add' := fun x y => by
        ext; simp [add_smul, Finset.sum_add_distrib]; abel
      map_smul' := fun c x => by
        ext; simp [mul_smul, smul_add, Finset.smul_sum] }
  have hQ_rad_lin : ∀ r1 r2 : radV, Q (r1.1 + r2.1) + Q 0 = (Q r1.1 + Q 0) + (Q r2.1 + Q 0) := by
    intro r1 r2
    rw [hQ r1.1 r2.1, r2.2 r1.1, add_zero]
    generalize Q r1.1 = a; generalize Q r2.1 = b; generalize Q 0 = c
    fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl
  let Lrad : radV →ₗ[K] K :=
    { toFun := fun r => Q r.1 + Q 0
      map_add' := fun r1 r2 => hQ_rad_lin r1 r2
      map_smul' := fun c r => by
        rcases zmod2_eq_zero_or_one c with rfl | rfl <;> simp [zmod2_add_self] }
  let L0 : V →ₗ[K] K :=
    Lrad.comp rProj +
    ∑ i : Fin p, ((Q (e i).1 + Q 0) • aL i + (Q (f i).1 + Q 0) • bL i)
  have hQ_decomp : ∀ x : V, Q x = Q 0 + L0 x + ∑ i : Fin p, aL i x * bL i x := by
    intro x
    have hx : x = (rProj x).1 + ∑ i : Fin p, (aL i x • (e i).1 + bL i x • (f i).1) := by
      change x = (x + ∑ i : Fin p, (aL i x • (e i).1 + bL i x • (f i).1)) +
        ∑ i : Fin p, (aL i x • (e i).1 + bL i x • (f i).1)
      rw [add_assoc, zmod2_vadd_self, add_zero]
    have hsum_Q : ∀ (S : Finset (Fin p)),
        Q (∑ i ∈ S, (aL i x • (e i).1 + bL i x • (f i).1)) =
        Q 0 + ∑ i ∈ S, (aL i x * (Q (e i).1 + Q 0) + bL i x * (Q (f i).1 + Q 0) + aL i x * bL i x) := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp
      | insert j S hj ih =>
        rw [Finset.sum_insert hj, Finset.sum_insert hj, hQ, ih]
        have hB_orth : B (aL j x • (e j).1 + bL j x • (f j).1)
            (∑ i ∈ S, (aL i x • (e i).1 + bL i x • (f i).1)) = 0 := by
          simp only [map_sum, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
            smul_eq_mul]
          refine Finset.sum_eq_zero fun i hi => ?_
          have hji : j ≠ i := fun h => hj (h ▸ hi)
          have hij : i ≠ j := Ne.symm hji
          rw [hee j i, hef j i, hB_sym (f j).1 (e i).1, hef i j, hff j i]
          simp [hji, hij]
        have hQ_pair : Q (aL j x • (e j).1 + bL j x • (f j).1) =
            Q 0 + aL j x * (Q (e j).1 + Q 0) + bL j x * (Q (f j).1 + Q 0) + aL j x * bL j x := by
          rw [hQ]
          have hBe : B (aL j x • (e j).1) (bL j x • (f j).1) = aL j x * bL j x := by
            simp [hef j j]; ring
          have hQe : Q (aL j x • (e j).1) = Q 0 + aL j x * (Q (e j).1 + Q 0) := by
            rcases zmod2_eq_zero_or_one (aL j x) with h | h <;> rw [h]
            · simp
            · simp only [one_smul, one_mul, add_comm (Q (e j).1) (Q 0), zmod2_add_add_cancel]
          have hQf : Q (bL j x • (f j).1) = Q 0 + bL j x * (Q (f j).1 + Q 0) := by
            rcases zmod2_eq_zero_or_one (bL j x) with h | h <;> rw [h]
            · simp
            · simp only [one_smul, one_mul, add_comm (Q (f j).1) (Q 0), zmod2_add_add_cancel]
          rw [hBe, hQe, hQf]
          generalize Q 0 = q0
          generalize aL j x * (Q (e j).1 + q0) = t1
          generalize bL j x * (Q (f j).1 + q0) = t2
          generalize aL j x * bL j x = t3
          have hr : q0 + t1 + (q0 + t2) + q0 + t3 = q0 + t1 + t2 + t3 + (q0 + q0) := by ring
          simpa only [zmod2_add_self, add_zero] using hr
        rw [hB_orth, hQ_pair]
        generalize Q 0 = q0
        generalize aL j x * (Q (e j).1 + q0) = t1
        generalize bL j x * (Q (f j).1 + q0) = t2
        generalize aL j x * bL j x = t3
        generalize ∑ i ∈ S, (aL i x * (Q (e i).1 + q0) + bL i x * (Q (f i).1 + q0) + aL i x * bL i x) = rest
        have hr : q0 + t1 + t2 + t3 + (q0 + rest) + q0 + 0 = q0 + (t1 + t2 + t3 + rest) + (q0 + q0) := by ring
        simpa only [zmod2_add_self, add_zero] using hr
    conv_lhs => rw [hx]
    rw [hQ, hsum_Q]
    have hBrad : B (rProj x).1 (∑ i : Fin p, (aL i x • (e i).1 + bL i x • (f i).1)) = 0 := by
      rw [hB_sym]
      exact (rProj x).2 _
    rw [hBrad, add_zero]
    simp only [L0, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, Lrad, LinearMap.coe_mk, AddHom.coe_mk,
      Finset.sum_add_distrib]
    have hcomm1 : ∀ i : Fin p, aL i x * (Q (e i).1 + Q 0) = (Q (e i).1 + Q 0) * aL i x :=
      fun i => mul_comm _ _
    have hcomm2 : ∀ i : Fin p, bL i x * (Q (f i).1 + Q 0) = (Q (f i).1 + Q 0) * bL i x :=
      fun i => mul_comm _ _
    simp_rw [hcomm1, hcomm2]
    generalize Q (rProj x).1 = qr
    generalize Q 0 = q0
    generalize ∑ i : Fin p, (Q (e i).1 + q0) * aL i x = s1
    generalize ∑ i : Fin p, (Q (f i).1 + q0) * bL i x = s2
    generalize ∑ i : Fin p, aL i x * bL i x = s3
    have hr : qr + (q0 + (s1 + s2 + s3)) + q0 = q0 + (qr + q0 + (s1 + s2)) + s3 := by ring
    exact hr
  let q := min d p
  let ask : Fin d → ℕ → (V →ₗ[K] K) := fun j _ =>
    if hj : j.val < p then aL ⟨j.val, hj⟩ else 0
  let bitOf : ℕ → Fin q → K := fun h i =>
    if h.testBit (d - 1 - i.val) then 1 else 0
  let rule : ℕ → (V →ₗ[K] K) := fun h =>
    L0 + ∑ i : Fin q, bitOf h i • bL ⟨i.val, lt_of_lt_of_le i.isLt (Nat.min_le_right d p)⟩
  let bias : ℕ → K := fun _ => Q 0
  have hrun_bit : ∀ (x : V) (i : Fin q),
      bitOf ((List.finRange d).foldl (fun h j => 2 * h + (if ask j h x = 0 then 0 else 1)) 0) i =
      aL ⟨i.val, lt_of_lt_of_le i.isLt (Nat.min_le_right d p)⟩ x := by
    intro x i
    have hfold_bit : ∀ (m : ℕ) (f_bit : ℕ → Bool) (t : ℕ), t < m →
        ((List.range m).foldl (fun h j => 2 * h + (if f_bit j then 1 else 0)) 0).testBit (m - 1 - t) = f_bit t := by
      intro m f_bit
      induction m with
      | zero => intro t ht; omega
      | succ m ih =>
        intro t ht
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        set prev := (List.range m).foldl (fun h j => 2 * h + (if f_bit j then 1 else 0)) 0
        by_cases htm : t = m
        · subst htm
          simp only [Nat.add_sub_cancel, Nat.sub_self]
          cases f_bit t <;> simp [Nat.testBit_zero]
        · have hlt : t < m := by omega
          have heq : m + 1 - 1 - t = (m - 1 - t) + 1 := by omega
          rw [heq, Nat.testBit_succ]
          have hdiv : (2 * prev + (if f_bit m then 1 else 0)) / 2 = prev := by
            cases f_bit m <;> simp <;> omega
          rw [hdiv]
          exact ih t hlt
    have hfr : (List.finRange d).foldl (fun h j => 2 * h + (if ask j h x = 0 then 0 else 1)) 0 =
        (List.range d).foldl (fun h j => 2 * h + (if (if hj : j < d then ask ⟨j, hj⟩ 0 x != 0 else false) then 1 else 0)) 0 := by
      have hzip : ∀ (l : List (Fin d)) (acc : ℕ),
          l.foldl (fun h j => 2 * h + (if ask j h x = 0 then 0 else 1)) acc =
          (l.map Fin.val).foldl (fun h j => 2 * h + (if (if hj : j < d then ask ⟨j, hj⟩ 0 x != 0 else false) then 1 else 0)) acc := by
        intro l
        induction l with
        | nil => intro acc; rfl
        | cons j l ih =>
          intro acc
          simp only [List.map_cons, List.foldl_cons, j.isLt, ↓reduceDIte]
          have heq : (if ask j acc x = 0 then 0 else 1) = (if (ask j 0 x != 0) = true then 1 else 0) := by
            have ha_eq : ask j acc x = ask j 0 x := rfl
            rw [ha_eq]
            by_cases h0 : ask j 0 x = 0 <;> simp [h0]
          rw [heq]
          exact ih _
      have hmap : (List.finRange d).map Fin.val = List.range d := by
        apply List.ext_getElem
        · simp
        · intro i h1 h2
          simp
      rw [hzip, hmap]
    rw [hfr]
    simp only [bitOf]
    rw [hfold_bit d _ i.val (lt_of_lt_of_le i.isLt (Nat.min_le_left d p))]
    have hid : i.val < d := lt_of_lt_of_le i.isLt (Nat.min_le_left d p)
    have hip : i.val < p := lt_of_lt_of_le i.isLt (Nat.min_le_right d p)
    simp only [hid, ↓reduceDIte, ask, hip]
    rcases zmod2_eq_zero_or_one (aL ⟨i.val, hip⟩ x) with ha | ha <;> rw [ha] <;> decide
  refine ⟨ask, rule, bias, ?_⟩
  dsimp only
  let run := fun x : V =>
    (List.finRange d).foldl (fun h j => 2 * h + (if ask j h x = 0 then 0 else 1)) 0
  have hcond : ∀ x : V, (Q x = rule (run x) x + bias (run x)) ↔
      (∑ i : Fin (p - q), aL ⟨q + i.val, by omega⟩ x * bL ⟨q + i.val, by omega⟩ x = 0) := by
    intro x
    rw [hQ_decomp x]
    simp only [rule, bias, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    have hbit : ∑ i : Fin q, bitOf (run x) i * bL ⟨i.val, lt_of_lt_of_le i.isLt (Nat.min_le_right d p)⟩ x =
        ∑ i : Fin q, aL ⟨i.val, lt_of_lt_of_le i.isLt (Nat.min_le_right d p)⟩ x *
          bL ⟨i.val, lt_of_lt_of_le i.isLt (Nat.min_le_right d p)⟩ x :=
      Finset.sum_congr rfl fun i _ => by rw [hrun_bit x i]
    rw [hbit]
    have hsplit_p : ∑ i : Fin p, aL i x * bL i x =
        (∑ i : Fin q, aL ⟨i.val, lt_of_lt_of_le i.isLt (Nat.min_le_right d p)⟩ x *
          bL ⟨i.val, lt_of_lt_of_le i.isLt (Nat.min_le_right d p)⟩ x) +
        (∑ i : Fin (p - q), aL ⟨q + i.val, by omega⟩ x * bL ⟨q + i.val, by omega⟩ x) := by
      have hqp : q + (p - q) = p := Nat.add_sub_of_le (Nat.min_le_right d p)
      let eFin : Fin (q + (p - q)) ≃ Fin p := finCongr hqp
      rw [← Equiv.sum_comp eFin, Fin.sum_univ_add]
      rfl
    rw [hsplit_p]
    generalize Q 0 = q0
    generalize L0 x = l0
    generalize ∑ i : Fin q, aL ⟨i.val, lt_of_lt_of_le i.isLt (Nat.min_le_right d p)⟩ x *
      bL ⟨i.val, lt_of_lt_of_le i.isLt (Nat.min_le_right d p)⟩ x = s1
    generalize ∑ i : Fin (p - q), aL ⟨q + i.val, by omega⟩ x * bL ⟨q + i.val, by omega⟩ x = s2
    constructor
    · intro h
      have h1 : (q0 + l0 + (s1 + s2)) + (l0 + s1 + q0) =
          s2 + (q0 + q0) + (l0 + l0) + (s1 + s1) := by ring
      rw [h, zmod2_add_self] at h1
      simpa only [zmod2_add_self, add_zero] using h1.symm
    · intro h
      rw [h]
      ring
  dsimp only [run] at hcond
  simp_rw [hcond]
  let φ : V ≃ (radV × (Fin q → K × K) × (Fin (p - q) → K × K)) :=
    { toFun := fun x =>
        (rProj x,
         fun i => (aL ⟨i.val, lt_of_lt_of_le i.isLt (Nat.min_le_right d p)⟩ x,
                   bL ⟨i.val, lt_of_lt_of_le i.isLt (Nat.min_le_right d p)⟩ x),
         fun i => (aL ⟨q + i.val, by omega⟩ x, bL ⟨q + i.val, by omega⟩ x))
      invFun := fun t =>
        t.1.1 +
        (∑ i : Fin q, ((t.2.1 i).1 • (e ⟨i.val, lt_of_lt_of_le i.isLt (Nat.min_le_right d p)⟩).1 +
                       (t.2.1 i).2 • (f ⟨i.val, lt_of_lt_of_le i.isLt (Nat.min_le_right d p)⟩).1)) +
        (∑ i : Fin (p - q), ((t.2.2 i).1 • (e ⟨q + i.val, by omega⟩).1 +
                             (t.2.2 i).2 • (f ⟨q + i.val, by omega⟩).1))
      left_inv := fun x => by
        have hqp : q + (p - q) = p := Nat.add_sub_of_le (Nat.min_le_right d p)
        have hsum :
            (∑ i : Fin q, (aL ⟨i.val, lt_of_lt_of_le i.isLt (Nat.min_le_right d p)⟩ x •
              (e ⟨i.val, lt_of_lt_of_le i.isLt (Nat.min_le_right d p)⟩).1 +
              bL ⟨i.val, lt_of_lt_of_le i.isLt (Nat.min_le_right d p)⟩ x •
              (f ⟨i.val, lt_of_lt_of_le i.isLt (Nat.min_le_right d p)⟩).1)) +
            (∑ i : Fin (p - q), (aL ⟨q + i.val, by omega⟩ x • (e ⟨q + i.val, by omega⟩).1 +
              bL ⟨q + i.val, by omega⟩ x • (f ⟨q + i.val, by omega⟩).1)) =
            ∑ i : Fin p, (aL i x • (e i).1 + bL i x • (f i).1) := by
          let eFin : Fin (q + (p - q)) ≃ Fin p := finCongr hqp
          rw [← Equiv.sum_comp eFin, Fin.sum_univ_add]
          rfl
        simp only [rProj, LinearMap.coe_mk, AddHom.coe_mk]
        rw [add_assoc, hsum, add_assoc, zmod2_vadd_self, add_zero]
      right_inv := fun ⟨r, u1, u2⟩ => by
        have hB_e : ∀ j : Fin p,
            aL j (r.1 +
              (∑ i : Fin q, ((u1 i).1 • (e ⟨i.val, lt_of_lt_of_le i.isLt (Nat.min_le_right d p)⟩).1 +
                             (u1 i).2 • (f ⟨i.val, lt_of_lt_of_le i.isLt (Nat.min_le_right d p)⟩).1)) +
              (∑ i : Fin (p - q), ((u2 i).1 • (e ⟨q + i.val, by omega⟩).1 +
                                   (u2 i).2 • (f ⟨q + i.val, by omega⟩).1))) =
            if hj : j.val < q then (u1 ⟨j.val, hj⟩).1 else (u2 ⟨j.val - q, by omega⟩).1 := by
          intro j
          simp only [aL, LinearMap.coe_mk, AddHom.coe_mk, map_add, map_sum, map_smul,
            LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
          rw [hB_sym r.1, r.2 (f j).1, zero_add]
          have h1 : ∀ i : Fin q, (u1 i).1 * B (e ⟨i.val, lt_of_lt_of_le i.isLt (Nat.min_le_right d p)⟩).1 (f j).1 +
              (u1 i).2 * B (f ⟨i.val, lt_of_lt_of_le i.isLt (Nat.min_le_right d p)⟩).1 (f j).1 =
              if (⟨i.val, lt_of_lt_of_le i.isLt (Nat.min_le_right d p)⟩ : Fin p) = j then (u1 i).1 else 0 := by
            intro i
            rw [hef, hff]
            split_ifs <;> simp
          have h2 : ∀ i : Fin (p - q), (u2 i).1 * B (e ⟨q + i.val, by omega⟩).1 (f j).1 +
              (u2 i).2 * B (f ⟨q + i.val, by omega⟩).1 (f j).1 =
              if (⟨q + i.val, by omega⟩ : Fin p) = j then (u2 i).1 else 0 := by
            intro i
            rw [hef, hff]
            split_ifs <;> simp
          simp_rw [h1, h2]
          split_ifs with hj
          · rw [Finset.sum_eq_single ⟨j.val, hj⟩, Finset.sum_eq_zero]
            · simp
            · intro i _
              split_ifs with h
              · exfalso; have hv := congrArg Fin.val h; dsimp at hv; omega
              · rfl
            · intro i _ hne
              split_ifs with h
              · exfalso; apply hne; apply Fin.ext; have hv := congrArg Fin.val h; dsimp at hv ⊢; omega
              · rfl
            · intro h0; exact absurd (Finset.mem_univ _) h0
          · rw [Finset.sum_eq_zero, Finset.sum_eq_single ⟨j.val - q, by omega⟩]
            · simp [show q + (j.val - q) = j.val by omega]
            · intro i _ hne
              split_ifs with h
              · exfalso; apply hne; apply Fin.ext; have hv := congrArg Fin.val h; dsimp at hv ⊢; omega
              · rfl
            · intro h0; exact absurd (Finset.mem_univ _) h0
            · intro i _
              split_ifs with h
              · exfalso; have hv := congrArg Fin.val h; dsimp at hv; omega
              · rfl
        have hB_f : ∀ j : Fin p,
            bL j (r.1 +
              (∑ i : Fin q, ((u1 i).1 • (e ⟨i.val, lt_of_lt_of_le i.isLt (Nat.min_le_right d p)⟩).1 +
                             (u1 i).2 • (f ⟨i.val, lt_of_lt_of_le i.isLt (Nat.min_le_right d p)⟩).1)) +
              (∑ i : Fin (p - q), ((u2 i).1 • (e ⟨q + i.val, by omega⟩).1 +
                                   (u2 i).2 • (f ⟨q + i.val, by omega⟩).1))) =
            if hj : j.val < q then (u1 ⟨j.val, hj⟩).2 else (u2 ⟨j.val - q, by omega⟩).2 := by
          intro j
          simp only [bL, LinearMap.coe_mk, AddHom.coe_mk, map_add, map_sum, map_smul,
            LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
          rw [hB_sym r.1, r.2 (e j).1, zero_add]
          have h1 : ∀ i : Fin q, (u1 i).1 * B (e ⟨i.val, lt_of_lt_of_le i.isLt (Nat.min_le_right d p)⟩).1 (e j).1 +
              (u1 i).2 * B (f ⟨i.val, lt_of_lt_of_le i.isLt (Nat.min_le_right d p)⟩).1 (e j).1 =
              if j = (⟨i.val, lt_of_lt_of_le i.isLt (Nat.min_le_right d p)⟩ : Fin p) then (u1 i).2 else 0 := by
            intro i
            rw [hee, hB_sym (f _).1 (e j).1, hef]
            split_ifs <;> simp
          have h2 : ∀ i : Fin (p - q), (u2 i).1 * B (e ⟨q + i.val, by omega⟩).1 (e j).1 +
              (u2 i).2 * B (f ⟨q + i.val, by omega⟩).1 (e j).1 =
              if j = (⟨q + i.val, by omega⟩ : Fin p) then (u2 i).2 else 0 := by
            intro i
            rw [hee, hB_sym (f _).1 (e j).1, hef]
            split_ifs <;> simp
          simp_rw [h1, h2]
          split_ifs with hj
          · rw [Finset.sum_eq_single ⟨j.val, hj⟩, Finset.sum_eq_zero]
            · simp
            · intro i _
              split_ifs with h
              · exfalso; have hv := congrArg Fin.val h; dsimp at hv; omega
              · rfl
            · intro i _ hne
              split_ifs with h
              · exfalso; apply hne; apply Fin.ext; have hv := congrArg Fin.val h; dsimp at hv ⊢; omega
              · rfl
            · intro h0; exact absurd (Finset.mem_univ _) h0
          · rw [Finset.sum_eq_zero, Finset.sum_eq_single ⟨j.val - q, by omega⟩]
            · simp [show q + (j.val - q) = j.val by omega]
            · intro i _ hne
              split_ifs with h
              · exfalso; apply hne; apply Fin.ext; have hv := congrArg Fin.val h; dsimp at hv ⊢; omega
              · rfl
            · intro h0; exact absurd (Finset.mem_univ _) h0
            · intro i _
              split_ifs with h
              · exfalso; have hv := congrArg Fin.val h; dsimp at hv; omega
              · rfl
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · ext
          simp only [rProj, LinearMap.coe_mk, AddHom.coe_mk]
          have hqp : q + (p - q) = p := Nat.add_sub_of_le (Nat.min_le_right d p)
          let eFin : Fin (q + (p - q)) ≃ Fin p := finCongr hqp
          let s1 := ∑ i : Fin q, ((u1 i).1 • (e ⟨i.val, lt_of_lt_of_le i.isLt (Nat.min_le_right d p)⟩).1 +
                                  (u1 i).2 • (f ⟨i.val, lt_of_lt_of_le i.isLt (Nat.min_le_right d p)⟩).1)
          let s2 := ∑ i : Fin (p - q), ((u2 i).1 • (e ⟨q + i.val, by omega⟩).1 +
                                        (u2 i).2 • (f ⟨q + i.val, by omega⟩).1)
          have hsum : (∑ j : Fin p, (aL j (r.1 + s1 + s2) • (e j).1 + bL j (r.1 + s1 + s2) • (f j).1)) =
              s1 + s2 := by
            rw [← Equiv.sum_comp eFin, Fin.sum_univ_add]
            congr 1
            · refine Finset.sum_congr rfl fun i _ => ?_
              simp only [eFin, finCongr_apply, s1, s2, hB_e, hB_f, Fin.coe_cast, Fin.coe_castAdd,
                i.isLt, ↓reduceDIte]
              rfl
            · refine Finset.sum_congr rfl fun i _ => ?_
              simp only [eFin, finCongr_apply, s1, s2, hB_e, hB_f, Fin.coe_cast, Fin.coe_natAdd,
                show ¬(q + i.val < q) by omega, ↓reduceDIte, Nat.add_sub_cancel_left]
              rfl
          change r.1 + s1 + s2 + (∑ j : Fin p, (aL j (r.1 + s1 + s2) • (e j).1 + bL j (r.1 + s1 + s2) • (f j).1)) = r.1
          rw [hsum]
          have hadd : r.1 + s1 + s2 + (s1 + s2) = r.1 + ((s1 + s2) + (s1 + s2)) := by abel
          rw [hadd, zmod2_vadd_self, add_zero]
        · funext i
          ext <;> simp [hB_e, hB_f, i.isLt]
        · funext i
          ext <;> simp [hB_e, hB_f, show ¬(q + i.val < q) by omega] }
  have hcard_eq :
      ((Finset.univ : Finset V).filter (fun x =>
        ∑ i : Fin (p - q), aL ⟨q + i.val, by omega⟩ x * bL ⟨q + i.val, by omega⟩ x = 0)).card =
      Fintype.card radV * Fintype.card (Fin q → K × K) *
        ((Finset.univ : Finset (Fin (p - q) → K × K)).filter
          (fun ab => ∑ i : Fin (p - q), (ab i).1 * (ab i).2 = 0)).card := by
    rw [← Finset.card_univ, ← Finset.card_univ, ← Finset.card_product, ← Finset.card_product]
    refine Finset.card_bij (fun x _ => (((φ x).1, (φ x).2.1), (φ x).2.2)) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, φ] at hx ⊢
      exact hx
    · intro x _ y _ h
      apply φ.injective
      exact Prod.ext (congrArg (fun z => z.1.1) h) (Prod.ext (congrArg (fun z => z.1.2) h) (congrArg (fun z => z.2) h))
    · rintro ⟨⟨r, u1⟩, u2⟩ h
      simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_filter] at h
      refine ⟨φ.symm (r, u1, u2), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hright := φ.apply_symm_apply (r, u1, u2)
        have hu2 : (fun i : Fin (p - q) =>
            (aL ⟨q + i.val, by omega⟩ (φ.symm (r, u1, u2)),
             bL ⟨q + i.val, by omega⟩ (φ.symm (r, u1, u2)))) = u2 := congrArg (fun t => t.2.2) hright
        have hsum_eq : ∑ i : Fin (p - q), aL ⟨q + i.val, by omega⟩ (φ.symm (r, u1, u2)) *
            bL ⟨q + i.val, by omega⟩ (φ.symm (r, u1, u2)) =
            ∑ i : Fin (p - q), (u2 i).1 * (u2 i).2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have hi := congrFun hu2 i
          rw [← hi]
        rw [hsum_eq]
        exact h
      · have hright := φ.apply_symm_apply (r, u1, u2)
        simp [hright]
  have hrad_dim' : Module.finrank K radV = k - 2 * p := hrad_dim
  rw [hcard_eq, card_submodule_zmod2 radV, hrad_dim', card_inner_prod_zero]
  have hfq : Fintype.card (Fin q → K × K) = 2 ^ (2 * q) := by
    simp [Fintype.card_fin]
    rw [show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_mul]
  rw [hfq]
  have hpq : p - q = p - d := by omega
  rw [hpq]
  have h4 : 4 ^ (p - d) = 2 ^ (2 * (p - d)) := by
    rw [show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_mul]
  rw [h4]
  have heven : 2 ∣ 2 ^ (2 * (p - d)) + 2 ^ (p - d) := by
    by_cases h0 : p - d = 0
    · simp [h0]
    · have h1 : 2 ∣ 2 ^ (2 * (p - d)) := dvd_pow_self 2 (by omega)
      have h2 : 2 ∣ 2 ^ (p - d) := dvd_pow_self 2 h0
      exact dvd_add h1 h2
  have hmul_div : 2 ^ (k - 2 * p) * 2 ^ (2 * q) * ((2 ^ (2 * (p - d)) + 2 ^ (p - d)) / 2) =
      (2 ^ (k - 2 * p) * 2 ^ (2 * q) * (2 ^ (2 * (p - d)) + 2 ^ (p - d))) / 2 :=
    (Nat.mul_div_assoc _ heven).symm
  rw [hmul_div, mul_add]
  congr 1
  have he1 : 2 ^ (k - 2 * p) * 2 ^ (2 * q) * 2 ^ (2 * (p - d)) = 2 ^ k := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have he2 : 2 ^ (k - 2 * p) * 2 ^ (2 * q) * 2 ^ (p - d) = 2 ^ (k - (p - d)) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [he1, he2]

private theorem main_aux : ∀ (k : Nat) [NeZero k] (spacing : Nat),
    let K := ZMod 2
    let I := ZMod k
    let W := I → K
    let D := W →ₗ[K] K
    let s := Nat.gcd k (2 * spacing)
    let loss := Nat.gcd k 2 + (if 3 ∣ k / s then 2 * s else 0)
    let p := (k - loss) / 2
    ∀ (start inject : I) (name c : W),
      let phase := fun x : W =>
        let z := fun i : I => x (i - start) + name i
        let y := fun i : I => z i + z (i + (spacing : I)) + z (i - (spacing : I))
        ∑ i : I, (y i + (1 + y (i + 1)) * y (i + 2) + x (i - inject) + c i)
      let rad := (Finset.univ : Finset W).filter (fun v =>
        ∀ u : W, phase (u + v) + phase u + phase v + phase 0 = 0)
      rad.card = 2 ^ loss ∧ (p = 0 ↔ k ≤ 2 ∨ ((k = 3 ∨ k = 6) ∧ ¬ 3 ∣ spacing)) ∧
      ∀ d : Nat,
        let run := fun (ask : Fin d → Nat → D) (x : W) =>
          (List.finRange d).foldl (fun h j => 2 * h + (if ask j h x = 0 then 0 else 1)) 0
        let hits := fun (ask : Fin d → Nat → D) (rule : Nat → D) (bias : Nat → K) =>
          ((Finset.univ : Finset W).filter (fun x =>
            phase x = rule (run ask x) x + bias (run ask x))).card
        let cap := (2 ^ k + 2 ^ (k - (p - d))) / 2
        (∀ ask rule bias, hits ask rule bias ≤ cap) ∧ ∃ ask rule bias, hits ask rule bias = cap := by
  classical
  intro k _ spacing
  dsimp only
  intro start inject name c
  let I := ZMod k
  let W := I → K
  let s := Nat.gcd k (2 * spacing)
  let loss := Nat.gcd k 2 + (if 3 ∣ k / s then 2 * s else 0)
  let p := (k - loss) / 2
  let phase : W → K := fun x =>
    let z := fun i : I => x (i - start) + name i
    let y := fun i : I => z i + z (i + (spacing : I)) + z (i - (spacing : I))
    ∑ i : I, (y i + (1 + y (i + 1)) * y (i + 2) + x (i - inject) + c i)
  let rad : Finset W := (Finset.univ : Finset W).filter (fun v =>
    ∀ u : W, phase (u + v) + phase u + phase v + phase 0 = 0)
  have hrad_card : rad.card = 2 ^ loss := rad_card_eq spacing start inject name c
  have hloss_le : loss ≤ k := by
    have h1 : 2 ^ loss ≤ 2 ^ k := by
      rw [← hrad_card]
      have h2 := Finset.card_le_univ rad
      simpa [W, I, Fintype.card_fun, ZMod.card] using h2
    exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp h1
  have hp0 : p = 0 ↔ k ≤ 2 ∨ ((k = 3 ∨ k = 6) ∧ ¬ 3 ∣ spacing) :=
    p_eq_zero_iff spacing hloss_le
  refine ⟨hrad_card, hp0, ?_⟩
  let B : W →ₗ[K] W →ₗ[K] K :=
    { toFun := fun u =>
        { toFun := fun v => ∑ i : I, u (i - start) * MOp (2 * spacing) (AOp (fun j => v (j - start))) i
          map_add' := fun v1 v2 => by
            have h1 : (fun j => (v1 + v2) (j - start)) = (fun j => v1 (j - start)) + (fun j => v2 (j - start)) := rfl
            rw [h1]
            have h2 : AOp ((fun j => v1 (j - start)) + (fun j => v2 (j - start))) =
                AOp (fun j => v1 (j - start)) + AOp (fun j => v2 (j - start)) := by
              funext j; exact AOp_add _ _ j
            rw [h2, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [MOp_add, mul_add]
          map_smul' := fun a v => by
            rcases zmod2_eq_zero_or_one a with rfl | rfl
            · simp only [zero_smul, RingHom.id_apply]
              refine Finset.sum_eq_zero fun x _ => ?_
              change u (x - start) * (0 + 0 + (0 + 0) + (0 + 0)) = 0
              simp
            · simp only [one_smul, RingHom.id_apply] }
      map_add' := fun u1 u2 => by
        refine LinearMap.ext fun v => ?_
        change ∑ i : I, (u1 (i - start) + u2 (i - start)) * MOp (2 * spacing) (AOp (fun j => v (j - start))) i =
          (∑ i : I, u1 (i - start) * MOp (2 * spacing) (AOp (fun j => v (j - start))) i) +
          (∑ i : I, u2 (i - start) * MOp (2 * spacing) (AOp (fun j => v (j - start))) i)
        simp only [add_mul, Finset.sum_add_distrib]
      map_smul' := fun a u => by
        refine LinearMap.ext fun v => ?_
        rcases zmod2_eq_zero_or_one a with rfl | rfl
        · simp only [zero_smul, RingHom.id_apply, LinearMap.zero_apply]
          refine Finset.sum_eq_zero fun x _ => ?_
          change (0 : K) * _ = 0
          exact zero_mul _
        · simp only [one_smul, RingHom.id_apply] }
  have hQ : ∀ u v : W, phase (u + v) = phase u + phase v + phase 0 + B u v := by
    intro u v
    have hpol := phase_polar spacing start inject name c u v
    change phase (u + v) + phase u + phase v + phase 0 = B u v at hpol
    rw [← hpol]
    generalize phase (u + v) = a
    generalize phase u = b
    generalize phase v = d0
    generalize phase 0 = e0
    have hr : b + d0 + e0 + (a + b + d0 + e0) = a + (b + b) + (d0 + d0) + (e0 + e0) := by ring
    simpa only [zmod2_add_self, add_zero] using hr.symm
  have hB_alt : ∀ u : W, B u u = 0 := by
    intro u
    have h := hQ u u
    have huu : u + u = 0 := zmod2_vadd_self u
    rw [huu, zmod2_add_self, zero_add] at h
    have h1 := congrArg (· + phase 0) h
    rw [zmod2_add_self, add_comm (phase 0) (B u u), add_assoc, zmod2_add_self, add_zero] at h1
    exact h1.symm
  have hB_sym : ∀ u v : W, B u v = B v u := by
    intro u v
    have h1 := hQ u v
    have h2 := hQ v u
    rw [add_comm u v] at h1
    rw [h1] at h2
    have h3 : (phase u + phase v + phase 0 + B u v) + (phase v + phase u + phase 0 + B v u) =
        B u v + B v u + (phase u + phase u) + (phase v + phase v) + (phase 0 + phase 0) := by ring
    rw [h2, zmod2_add_self] at h3
    simp only [zmod2_add_self, add_zero] at h3
    exact zmod2_add_eq_zero h3.symm
  let radSub : Submodule K W :=
    { carrier := {w : W | ∀ u : W, B u w = 0}, add_mem' := fun ha hb u => by simp [ha u, hb u]
      zero_mem' := fun u => by simp
      smul_mem' := fun c _ ha u => by simp [ha u] }
  have hrad_sub_card : Fintype.card radSub = 2 ^ loss := by
    rw [← hrad_card, Fintype.card_subtype]
    congr 1
    ext v
    simp only [rad, Finset.mem_filter, Finset.mem_univ, true_and, radSub, Submodule.mem_mk,
      AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]
    constructor
    · intro h u
      rw [phase_polar spacing start inject name c u v]
      exact h u
    · intro h u
      have := h u
      rwa [phase_polar spacing start inject name c u v] at this
  have hrad_dim : Module.finrank K radSub = loss := by
    have h1 : 2 ^ Module.finrank K radSub = 2 ^ loss := by
      rw [← card_submodule_zmod2 radSub, hrad_sub_card]
    exact Nat.pow_right_injective (by omega : 1 < 2) h1
  have hdimW : Module.finrank K W = k := by
    simp [W, I, Module.finrank_pi, ZMod.card]
  have hparity : (k - loss) % 2 = 0 := by
    have hgcd2 : (Nat.gcd k 2) % 2 = k % 2 := by
      by_cases h2 : 2 ∣ k
      · rw [Nat.gcd_eq_right h2]; omega
      · have h1 : Nat.gcd k 2 = 1 := by
          have hdv := Nat.gcd_dvd_right k 2
          have hle2 : Nat.gcd k 2 ≤ 2 := Nat.le_of_dvd (by omega) hdv
          have hpos2 : 0 < Nat.gcd k 2 := Nat.gcd_pos_of_pos_right k (by omega)
          have hne2 : Nat.gcd k 2 ≠ 2 := fun h => h2 (h ▸ Nat.gcd_dvd_left k 2)
          omega
        rw [h1]; omega
    simp only [loss]
    split_ifs <;> omega
  have h2p : 2 * p = k - loss := by
    simp only [p]; omega
  intro d
  constructor
  · intro ask rule bias
    have htop := adaptive_upper_bound phase B hQ d (⊤ : Submodule K W) 0 p
      (fun radTop hradTop => by
        have htop_dim : Module.finrank K (⊤ : Submodule K W) = k := by rw [finrank_top, hdimW]
        have heq : Module.finrank K radTop = Module.finrank K radSub := by
          let eqv : radTop ≃ₗ[K] radSub :=
            { toFun := fun w => ⟨w.1.1, fun u => (hradTop w.1).mp w.2 ⟨u, trivial⟩⟩
              invFun := fun w => ⟨⟨w.1, trivial⟩, (hradTop ⟨w.1, trivial⟩).mpr (fun u => w.2 u.1)⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl
              map_add' := fun _ _ => rfl
              map_smul' := fun _ _ => rfl }
          exact LinearEquiv.finrank_eq eqv
        rw [htop_dim, heq, hrad_dim]
        omega)
      ask rule bias 0
    have htop_dim : Module.finrank K (⊤ : Submodule K W) = k := by rw [finrank_top, hdimW]
    rw [htop_dim] at htop
    have hcard_eq :
        ((Finset.univ : Finset W).filter (fun x =>
          phase x = rule ((List.finRange d).foldl (fun h j => 2 * h + (if ask j h x = 0 then 0 else 1)) 0) x +
            bias ((List.finRange d).foldl (fun h j => 2 * h + (if ask j h x = 0 then 0 else 1)) 0))).card =
        ((Finset.univ : Finset (⊤ : Submodule K W)).filter (fun u =>
          phase (0 + u.1) = rule ((List.finRange d).foldl (fun h j => 2 * h + (if ask j h (0 + u.1) = 0 then 0 else 1)) 0) (0 + u.1) +
            bias ((List.finRange d).foldl (fun h j => 2 * h + (if ask j h (0 + u.1) = 0 then 0 else 1)) 0))).card := by
      refine Finset.card_bij (fun x _ => (⟨x, trivial⟩ : (⊤ : Submodule K W))) ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, zero_add] at hx ⊢
        exact hx
      · intro _ _ _ _ h; exact congrArg Subtype.val h
      · intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, zero_add] at hu
        exact ⟨u.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩, rfl⟩
    rw [hcard_eq]
    dsimp only at htop
    change _ ≤ (2 ^ k + 2 ^ (k - (p - d))) / 2
    omega
  · exact adaptive_attain phase B hQ hB_alt hB_sym k p d hdimW
      (by rw [hrad_dim]; omega) (by omega)

end PEqualNP.Outside.L_lib_653_aux

theorem PEqualNP.Outside.L_lib_653 : (∀ (k : Nat) [NeZero k] (spacing : Nat),
  let K := ZMod 2
  let I := ZMod k
  let W := I → K
  let D := W →ₗ[K] K
  let s := Nat.gcd k (2*spacing)
  let loss := Nat.gcd k 2 + (if 3 ∣ k/s then 2*s else 0)
  let p := (k-loss)/2
  ∀ (start inject : I) (name c : W),
    let phase := fun x : W =>
      let z := fun i : I => x (i-start) + name i
      let y := fun i : I => z i + z (i+(spacing:I)) + z (i-(spacing:I))
      ∑ i : I, (y i + (1+y (i+1))*y (i+2) + x (i-inject) + c i)
    let rad := (Finset.univ : Finset W).filter (fun v =>
      ∀ u : W, phase (u+v) + phase u + phase v + phase 0 = 0)
    rad.card = 2^loss ∧ (p = 0 ↔ k ≤ 2 ∨ ((k = 3 ∨ k = 6) ∧ ¬3 ∣ spacing)) ∧
    ∀ d : Nat,
      let run := fun (ask : Fin d → Nat → D) (x : W) =>
        (List.finRange d).foldl (fun h j => 2*h + (if ask j h x = 0 then 0 else 1)) 0
      let hits := fun (ask : Fin d → Nat → D) (rule : Nat → D) (bias : Nat → K) =>
        ((Finset.univ : Finset W).filter (fun x =>
          phase x = rule (run ask x) x + bias (run ask x))).card
      let cap := (2^k + 2^(k-(p-d)))/2
      (∀ ask rule bias, hits ask rule bias ≤ cap) ∧ ∃ ask rule bias, hits ask rule bias = cap) :=
  PEqualNP.Outside.L_lib_653_aux.main_aux
