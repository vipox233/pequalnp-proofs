import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_828

lemma allocate (q E : ℕ) (cap : Fin q → ℕ) (h : E ≤ ∑ j, cap j) :
    ∃ a : Fin q → ℕ, (∀ j, a j ≤ cap j) ∧ (∑ j, a j) = E := by
  induction q generalizing E with
  | zero =>
    have he : E = 0 := by simpa using h
    subst E
    exact ⟨Fin.elim0, by simp⟩
  | succ q ih =>
    let z := min E (cap 0)
    have hzE : z ≤ E := Nat.min_le_left _ _
    have hzC : z ≤ cap 0 := Nat.min_le_right _ _
    have hr : E-z ≤ ∑ j : Fin q, cap j.succ := by
      rw [Fin.sum_univ_succ] at h
      dsimp [z]
      omega
    obtain ⟨a, ha, hs⟩ := ih (E-z) (fun j => cap j.succ) hr
    refine ⟨Fin.cases z a, ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · exact hzC
      · exact ha j
    · simp only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ]
      omega

lemma pow_split (n k : ℕ) (h : k ≤ n) :
    2^n = 2^k * 2^(n-k) := by
  rw [← pow_add, Nat.add_sub_of_le h]

lemma pow_tail (n k : ℕ) (h : k ≤ n) :
    2^(n+1-k)-1 = (2^(n-k)-1)+2^(n-k) := by
  have he : n+1-k = (n-k)+1 := by omega
  rw [he, pow_succ]
  have hp : 0 < 2^(n-k) := by positivity
  omega

lemma quotient (n k c d a : ℕ) (hk : k ≤ n) (hc : c = d+2^n*a) :
    c / 2^k = d / 2^k + 2^(n-k)*a := by
  rw [hc, pow_split n k hk]
  rw [show 2^k * 2^(n-k)*a = (2^(n-k)*a)*2^k by ring]
  exact Nat.add_mul_div_right _ _ (by positivity)

lemma pack (n q E : ℕ) (cap : Fin q → ℕ)
    (hmass : (∑ j, cap j) = E*(2^n-1))
    (hcut : ∀ k < n, E*(2^(n-k)-1) ≤ ∑ j, cap j / 2^k) :
    ∃ v : Fin n → Fin q → ℕ,
      (∀ i, (∑ j, v i j) = E) ∧
      ∀ j, (∑ i : Fin n, 2^i.val * v i j) = cap j := by
  induction n generalizing cap with
  | zero =>
    have hz : ∀ j, cap j = 0 := by
      have hh : (∑ j, cap j) = 0 := by simpa using hmass
      exact fun j => (Finset.sum_eq_zero_iff.mp hh) j (Finset.mem_univ _)
    refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
    · simp
    · intro j; simp [hz j]
  | succ n ih =>
    have htop : E ≤ ∑ j, cap j / 2^n := by
      simpa using hcut n (by omega)
    obtain ⟨a, ha, hasum⟩ := allocate q E (fun j => cap j / 2^n) htop
    have hab : ∀ j, 2^n*a j ≤ cap j := by
      intro j
      have hh := (Nat.le_div_iff_mul_le (by positivity : 0 < 2^n)).mp (ha j)
      simpa [mul_comm] using hh
    let rest := fun j => cap j - 2^n*a j
    have hc : ∀ j, cap j = rest j + 2^n*a j := by
      intro j
      exact (Nat.sub_add_cancel (hab j)).symm
    have hsum : (∑ j, cap j) = (∑ j, rest j) + 2^n*E := by
      simp_rw [hc]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hasum]
    have hpow : 2^(n+1)-1 = (2^n-1)+2^n := by
      simpa using pow_tail n 0 (Nat.zero_le _)
    have hmassR : (∑ j, rest j) = E*(2^n-1) := by
      rw [hpow, mul_add] at hmass
      nlinarith
    have hcutR : ∀ k < n, E*(2^(n-k)-1) ≤ ∑ j, rest j / 2^k := by
      intro k hk
      have hh := hcut k (by omega)
      have hd : (∑ j, cap j / 2^k) = (∑ j, rest j / 2^k) + 2^(n-k)*E := by
        simp_rw [quotient n k _ _ _ (by omega) (hc _)]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hasum]
      rw [pow_tail n k (by omega), mul_add, hd] at hh
      nlinarith
    obtain ⟨v, hv, hvsum⟩ := ih rest hmassR hcutR
    refine ⟨Fin.lastCases a v, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa using hasum
      · simpa using hv i
    · intro j
      rw [Fin.sum_univ_castSucc]
      simpa only [Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_last, Fin.val_castSucc,
        hvsum] using (hc j).symm

lemma cuts {n q E : ℕ} (v : Fin n → Fin q → ℕ)
    (hv : ∀ i, (∑ j, v i j) = E) :
    ∀ k < n, E*(2^(n-k)-1) ≤
      ∑ j, (∑ i : Fin n, 2^i.val * v i j) / 2^k := by
  induction n with
  | zero => simp
  | succ n ih =>
    let a := v (Fin.last n)
    let w := fun i : Fin n => v i.castSucc
    let rest := fun j => ∑ i : Fin n, 2^i.val * w i j
    have ha : (∑ j, a j) = E := hv _
    have hw : ∀ i, (∑ j, w i j) = E := fun i => hv _
    have hc : ∀ j, (∑ i : Fin (n+1), 2^i.val*v i j) = rest j+2^n*a j := by
      intro j
      rw [Fin.sum_univ_castSucc]
      rfl
    intro k hk
    have hkn : k ≤ n := by omega
    have hl : E*(2^(n-k)-1) ≤ ∑ j, rest j / 2^k := by
      by_cases hlt : k < n
      · exact ih w hw k hlt
      · have he : k = n := by omega
        simp [he]
    have hd : (∑ j, (∑ i : Fin (n+1), 2^i.val*v i j) / 2^k) =
        (∑ j, rest j / 2^k)+2^(n-k)*E := by
      simp_rw [quotient n k _ _ _ hkn (hc _)]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ha]
    rw [pow_tail n k hkn, mul_add, hd]
    nlinarith

lemma pred_mul (a E : ℕ) (ha : 0 < a) : E*(a-1)+E = a*E := by
  calc
    E*(a-1)+E = E*((a-1)+1) := by ring
    _ = a*E := by rw [Nat.sub_add_cancel (by omega), mul_comm]

lemma residue_cut (q E p M k : ℕ) (hq : 0 < q) (hE : 0 < E) (hEq : E < q)
    (hmod : 2^p % q = 1) (hmass : q*M+E = 2^p*E) (hk : k ≤ p) :
    E*(2^(p-k)-1) ≤ q*(M / 2^k) ↔ (2^(p-k)*E) % q ≤ E := by
  let a := 2^(p-k)
  let d := 2^k
  let A := a*E / q
  let r := a*E % q
  have ha : 0 < a := by dsimp [a]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hdiv : q*A+r = a*E := Nat.div_add_mod _ _
  have hr : r < q := Nat.mod_lt _ hq
  have hpow : 2^p = d*a := pow_split p k hk
  have hmodr : (d*r) % q = E := by
    calc
      (d*r) % q = (d*(q*A+r)) % q := by simp [Nat.mul_add, Nat.add_mod, Nat.mul_mod]
      _ = (2^p*E) % q := by rw [hdiv, hpow]; congr 1 <;> ring
      _ = E := by rw [Nat.mul_mod, hmod]; simp [Nat.mod_eq_of_lt hEq]
  have her : E ≤ d*r := by rw [← hmodr]; exact Nat.mod_le _ _
  have heq : q*M+E = q*(d*A)+d*r := by
    calc
      q*M+E = 2^p*E := hmass
      _ = d*(q*A+r) := by rw [hdiv, hpow]; ring
      _ = q*(d*A)+d*r := by ring
  have hlo : d*A ≤ M := by
    have hh : q*(d*A) ≤ q*M := by omega
    exact le_of_mul_le_mul_left hh hq
  have hhi : M < (A+1)*d := by
    have hh : d*r < d*q := Nat.mul_lt_mul_of_pos_left hr hd
    have hqhi : q*M < q*((A+1)*d) := by nlinarith
    exact (mul_lt_mul_iff_right₀ hq).mp (by simpa [mul_comm] using hqhi)
  have hfloor : M / d = A := Nat.div_eq_of_lt_le (by simpa [mul_comm] using hlo) hhi
  change E*(a-1) ≤ q*(M/d) ↔ r ≤ E
  rw [hfloor]
  have hp := pred_mul a E ha
  omega

end PEqualNP.Outside.L_lib_828

theorem PEqualNP.Outside.L_lib_828 : (∀ (q E p : ℕ), 1 < q → 0 < E → E < q → 0 < p → 2^p % q = 1 →
  ((∃ v : Fin p → Fin q → ℕ,
    (∀ i, (∑ j, v i j) = E) ∧
    ∀ j, q*(∑ i : Fin p, 2^i.val * v i j) = (2^p-1)*E) ↔
   ∀ b < p, (2^b*E) % q ≤ E)) := by
  classical
  intro q E p hq hE hEq hp hmod
  let M := (2^p / q)*E
  have hq0 : 0 < q := by omega
  have hpow : 2^p = q*(2^p / q)+1 := by
    have hh := Nat.mod_add_div (2^p) q
    omega
  have hmass : q*M+E = 2^p*E := by
    calc
      q*M+E = (q*(2^p / q)+1)*E := by dsimp [M]; ring
      _ = 2^p*E := by rw [← hpow]
  have hprod := PEqualNP.Outside.L_lib_828.pred_mul (2^p) E (by positivity)
  have htotal : q*M = E*(2^p-1) := by omega
  have hcut := PEqualNP.Outside.L_lib_828.residue_cut q E p M
  constructor
  · rintro ⟨v, hv, hvsum⟩ b hb
    by_cases hb0 : b = 0
    · subst b; simp [Nat.mod_eq_of_lt hEq]
    have hbin : ∀ j, (∑ i : Fin p, 2^i.val*v i j) = M := by
      intro j
      have heq : q*(∑ i : Fin p, 2^i.val*v i j) = q*M := by
        calc
          q*(∑ i : Fin p, 2^i.val*v i j) = (2^p-1)*E := hvsum j
          _ = q*M := by simpa [mul_comm] using htotal.symm
      exact Nat.eq_of_mul_eq_mul_left hq0 heq
    have hc := PEqualNP.Outside.L_lib_828.cuts v hv (p-b) (by omega)
    simp_rw [hbin] at hc
    have hr := (hcut (p-b) hq0 hE hEq hmod hmass (by omega)).mp (by simpa using hc)
    have he : p-(p-b) = b := by omega
    simpa only [he] using hr
  · intro hr
    have hc : ∀ k < p, E*(2^(p-k)-1) ≤ ∑ _j : Fin q, M / 2^k := by
      intro k hk
      have hres : (2^(p-k)*E) % q ≤ E := by
        by_cases hk0 : k = 0
        · subst k; simp [Nat.mul_mod, hmod, Nat.mod_eq_of_lt hEq]
        · exact hr (p-k) (by omega)
      have hh := (hcut k hq0 hE hEq hmod hmass (by omega)).mpr hres
      simpa using hh
    obtain ⟨v, hv, hvs⟩ := PEqualNP.Outside.L_lib_828.pack p q E (fun _ => M)
      (by simpa using htotal) hc
    refine ⟨v, hv, ?_⟩
    intro j
    rw [hvs j]
    simpa [mul_comm] using htotal
